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

/-! ## The two GROUND cells — settled without the floor

The whole off-cycle row reduces to these two, and neither needs a new census:

* at the COOPERATOR the guard's consequent is "the frozen `.const .C` plays D".
  `TailTo` walks the `.impl` to it, and `no_provable_botConst_tail`
  (`TauCIMCIC/Helpers`, budget-free — a frozen constant is bridge-unreadable and
  its atom has no certificate) kills it. Note this is NOT a floor argument: the
  bit is 0 because the fact is FALSE, not because citing it is too expensive.
* at the DEFECTOR the consequent is "the frozen `.const .D` plays D" — a cheap
  positive atom, so `weakenImpl` fires and DIMCID defects. -/

/-- τ(DIMCID)'s guard at the cooperator is unprovable at EVERY budget: its
    consequent asks the unconditional cooperator to defect. -/
theorem ps_dimGuard_coop_false {k K : Nat} :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .coop .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .coop .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop)))
      = false := by
  rw [dimG_subst]
  cases h : proofSearch K (dimG (.bot (inst (tauZoo k) .dimcid .coop))
      (inst (tauZoo k) .coop .dimcid)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [show inst (tauZoo k) .coop .dimcid = .const .C from inst_coop_peel k .dimcid]
        at hp
      refine no_provable_botConst_tail (a := Action.C) (b := Action.D) (by decide) _
        hp ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp)

/-- τ(DIMCID) COOPERATES with the unconditional cooperator — it has nothing to
    convict. -/
theorem dimcid_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .coop))
      (.bot (inst (tauZoo k) .dimcid .coop)) (inst (tauZoo k) .dimcid .coop)
      = some Action.C := by
  rw [inst_dimcid_peel_coop k]
  exact searchGuardD_plays_C _ _ ps_dimGuard_coop_false

/-- The defect-cell consequent: the frozen constant defector provably defects. -/
theorem pf_dimG_defect {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    Pf k (dimG (.bot (inst (tauZoo k) .dimcid .defect)) (.const .D)) := by
  refine pf_dimG_of_consequent (m := 3)
    (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩) ?_
  rw [inst_dimcid_peel_defect k, inst_defect_peel k .dimcid]
  have hlog := Nat.log2_le_self k
  simp only [dimG, Formula.size, Prog.size, numCost]
  omega

theorem ps_dimGuard_defect {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .defect .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .defect .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid .defect)) (.bot (inst (tauZoo k) .dimcid .defect)))
      = true := by
  rw [dimG_subst]
  exact (proofSearch_spec _ _).2
    (by rw [inst_defect_peel k .dimcid]; exact pf_dimG_defect hL)

/-- τ(DIMCID) DEFECTS against the constant defector — its suspicion is confirmed. -/
theorem dimcid_defect_plays_D {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .defect))
      (.bot (inst (tauZoo k) .dimcid .defect)) (inst (tauZoo k) .dimcid .defect)
      = some Action.D := by
  rw [inst_dimcid_peel_defect k]
  exact searchGuardD_plays_D _ _ (ps_dimGuard_defect hL)

/-! ### THE OFF-CYCLE ROW IS BLOCKED — a polarity obstruction, recorded

**Status 2026-08-21: the diagonal and the two ground cells are PROVEN; the eight
remaining off-cycle cells are not, and the blocker is structural rather than
proof-craft.** Recorded here so the next attempt starts from the analysis instead
of rediscovering it.

**The obstruction.** For CIMCIC, a provable guard FIRES the search into `C`,
making the guard's own antecedent ("I cooperate with them") TRUE, so soundness
detaches the consequent and refutes it — that is how `outcome_CIMCIC_vs_OBot`
closed with no census at all. DIMCID fires into `D`, so a provable guard makes
its antecedent FALSE and the implication VACUOUSLY true. **The soundness route is
unavailable by polarity.** Every false bit therefore needs a syntactic census, as
CIMCIC's floor cells did.

**Where the censuses land.**

* then-`C` partners (`tftPf`, and the run-stage shapes via their own cascades):
  the consequent "they play D" is their ELSE-play, so
  `no_provable_botSearcherElse_tail` prices it out. `ps_dimGuard_searcherC_false`
  below does exactly this and WORKS.
* then-`D` partners (`guardian`, `cupodTroll`): the consequent is their THEN-play,
  which `search_t`/`botSearchStep` CAN conclude — but only from their own guard,
  which is FALSE here (both probe `inst .dimcid .coop`, and
  `dimcid_coop_plays_C` pins it to `C`). So the atom is still unprovable, by
  soundness at one level down. **But the existing census kernel cannot express
  this**: `no_provable_tailToS_floor`'s `hbotsearch` obligation demands the target
  player not BE a bot-searcher with the target as then-action, and here it is.
  The kernel is asking us to exclude `botSearchStep`'s conclusion
  `□(their guard) → they play D`, which is a THEOREM of `S` and harmless (with
  their guard false, `□` never becomes provable, so it never detaches).

**Why no hypothesis refinement can fix this — MACHINE-CHECKED (2026-08-21).**
The obvious repair (parameterize `hbotsearch` by a guard-falsity premise, the
way `no_provable_botTwoWatchD` threads one through its `ite_t` arm) is
UNSOUND, because the census STATEMENT is already false for this shape. The
witness, verified in Lean:

    TailTo (.plays (.bot (.search k g (.const a) (.const b))) O a)
      (.impl (.box k (g.subst … O)) (.plays (.bot (.search k g …)) O a))

holds — the antecedent is a `.box`, never equal to the plays-atom target, so
`TailTo`'s guard clause is satisfied and the tail matches. `botSearchStep`
therefore PROVES a formula that `TailTo`-tails at our target (its size side
condition is `O(log k) ≤ k`, comfortably met), so "no `Pf` tails at this atom"
is FALSE. No amount of extra hypotheses on the kernel's slots can rescue a
false conclusion; the fix must change what is being claimed.

**What the next attempt actually needs** — the tail predicate must forbid BOX
antecedents, so that the search-reading arms die structurally:

    TailToA A S (.impl a ψ) = TailToA A S ψ ∧ ¬ TailToS S a ∧ A a
    TailToA A S φ           = S φ

with the DIMCID caller taking `A a := ¬ ∃ n φ, a = .box n φ` and every existing
caller taking `A := fun _ => True` (recovering `TailToS` exactly, via a bridge
lemma). Every implication-concluding arm of the kernel then gains one `A ant`
obligation — `trivial` for the existing 25 call sites, fatal for
`botSearchStep`/`searchBranch`/`iteBranchSearch_t`/`searchThenSearch_t` under
the box-forbidding instance.

That is a refactor of `no_provable_tailToS_floor` itself (31 arms, ~235 lines)
plus its 25 call sites — the trusted core of every floor result in the library.
It is worth doing when a SECOND bot needs it (WaryBot's `.neg` guard is the
likely candidate), not for one row.

**The detachment note, for the record.** The implication `botSearchStep` proves
is harmless: with the partner's guard false and `S` sound, `□(their guard)` is
never provable, so it never detaches. DIMCID's own guard — whose antecedent is
a plays-atom, not a box — remains plausibly unprovable. The bit values below
are almost certainly right; they are simply not certifiable with the present
census.

**Not a bistability.** The cell is NOT open in the `JustBot`-vs-`MirrorBot` sense:
the second fixed point ("DIMCID defects, so its antecedent is refutable, so the
guard is provable") does NOT close, because `Pf.atomNeg` needs an
`AtomProvable` certificate of the actual play, i.e. a certificate of the very
defection being assumed. With the self-reference running through `.bot`-FROZEN
instances there is no `diag`/PBLT rule to break that circle — unlike the
diagonal, where the `.self` pronoun supplies exactly that knot. So the intended
values below are almost certainly right; they are simply not yet certified. -/

/-- A prove-stage hypothesis whose THEN-action is `.C` (e.g. `tftPf` at DIMCID)
    cannot be shown to DEFECT at any budget ≤ its own: its `D` is the else-play,
    `search_f`-floored. This is the half of the row that DOES go through. -/
theorem ps_dimGuard_searcherC_false {k K : Nat} (hK : K ≤ k) (T : Tmpl)
    (g : Formula) (pE : Prog)
    (hpeelT : inst (tauZoo k) T .dimcid = .search k g (.const .C) pE)
    (hpeelD : inst (tauZoo k) .dimcid T
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) Action.C)
                         (.plays (.bot (inst (tauZoo k) T .dimcid)) .self Action.D))
          (.const .D) (.const .C)) :
    proofSearch K
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) T .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid T)) (.bot (inst (tauZoo k) .dimcid T)))
      = false := by
  rw [dimG_subst]
  cases h : proofSearch K (dimG (.bot (inst (tauZoo k) .dimcid T))
      (inst (tauZoo k) T .dimcid)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [hpeelT] at hp
      refine no_provable_botSearcherElse_tail k k g .C .D pE (by decide)
        (Nat.le_refl k) _ K _ hp hK ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by rw [hpeelD, hpeelT]; simp)

/-- …so DIMCID cooperates with such a partner. -/
theorem dimcid_plays_C_of_searcherC {k : Nat} (T : Tmpl) (g : Formula) (pE : Prog)
    (hpeelT : inst (tauZoo k) T .dimcid = .search k g (.const .C) pE)
    (hpeelD : inst (tauZoo k) .dimcid T
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) Action.C)
                         (.plays (.bot (inst (tauZoo k) T .dimcid)) .self Action.D))
          (.const .D) (.const .C)) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid T))
      (.bot (inst (tauZoo k) .dimcid T)) (inst (tauZoo k) .dimcid T)
      = some Action.C := by
  -- the guard-falsity fact is stated at the UNPEELED frame, so generalize the
  -- frame first and only then peel the program slot
  have hg := ps_dimGuard_searcherC_false (Nat.le_refl k) T g pE hpeelT hpeelD
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimcid T)) = Me at hg ⊢
  rw [hpeelD]
  exact searchGuardD_plays_C _ _ hg

/-! ### The entangled systems, named -/

/-- The closed-substituted form of DIMCID's entangled guard (the asymmetric twin
    of `sysClose_subst_cimSelfIdx`). -/
theorem sysClose_subst_cimSelfIdxD (defs : ProgList) (j : Nat) (me o : Prog) :
    ((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.C)
                   (.plays (.bot (.selfIdx j)) .self Action.D)).sysClose defs).subst me o
      = .impl (.plays me (.bot (.sys defs j)) Action.C)
              (.plays (.bot (.sys defs j)) me Action.D) := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]


/-- `inst .dimcid .dupoc`: DIMCID at the head. -/
def mdSysD (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
    (.const .C) (.const .D)) .nil)

theorem inst_dimcid_dupoc_eq (k : Nat) :
    inst (tauZoo k) .dimcid .dupoc = .sys (mdSysD k) 0 := rfl

theorem mdSysD_get0 (k : Nat) :
    (mdSysD k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.D))
          (.const .D) (.const .C)) := rfl

theorem mdSysD_get1 (k : Nat) :
    (mdSysD k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.const .C) (.const .D)) := rfl

/-! ## The ENTANGLED cells — the alignment rule, one pair at a time

DIMCID's member wants its partner to play `D` and fires `D`; the partner's own
target/fire decide the pair. Applying the rule (`TauCIMCIC/Helpers`, and its
Python mirror `_resolve_entangled`):

| pair | partner target / fire | verdict |
|---|---|---|
| dimcid × dupoc | C / C | ANTI-aligned → floor, both defaults: `(C, D)` |
| dimcid × cimcic | C / C | ANTI-aligned → floor, both defaults: `(C, D)` |
| dimcid × cupod | D / D | ALIGNED → mutual Löb, both fire: `(D, D)` |

The two anti-aligned pairs close here with the existing census
(`ps_botSys_mismatch_false`); the aligned one is left for the same treatment
`cimcic_dupoc_mutual` gives — see the note at the end of this section. -/

/-- The DIMCID member of a system, seen at index `i`, has then-action `.D`; a
    partner probing it for `.C` is therefore floor-false. -/
theorem ps_dimcidSys_C_false {k K : Nat} (hK : K ≤ k) (defs : ProgList) (i : Nat)
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx (1 - i))) Action.C)
             (.plays (.bot (.selfIdx (1 - i))) .self Action.D))
      (.const .D) (.const .C))) (O : Prog) :
    proofSearch K (.plays (.bot (.sys defs i)) O Action.C) = false :=
  ps_botSys_mismatch_false hK defs i k _ .D .C _ (by decide) (Nat.le_refl k) hget O

/-! ### dimcid × dupoc — anti-aligned, closed by the floor -/

theorem ps_probe_inst_dimcid_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimcid .dupoc)) = false := by
  rw [show probe (inst (tauZoo k) .dimcid .dupoc)
        = .plays (.bot (.sys (mdSysD k) 0)) (.bot (.sys (mdSysD k) 0)) Action.C
      from by rw [probe, inst_dimcid_dupoc_eq]]
  exact ps_botSys_mismatch_false hK (mdSysD k) 0 k _ .D .C _ (by decide)
    (Nat.le_refl k) (mdSysD_get0 k) _

/-- **τ(DIMCID) at Dupoc COOPERATES**: its guard aims `D` at the rewarding Dupoc
    component (then-action `C`) — floor-false — so the else-constant `C` runs. -/
theorem dimcid_dupoc_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .dupoc))
      (.bot (inst (tauZoo k) .dimcid .dupoc)) (inst (tauZoo k) .dimcid .dupoc)
      = some Action.C := by
  rw [inst_dimcid_dupoc_eq]
  refine sysSearcher_plays_else _ _ (mdSysD_get0 k) ?_
  rw [sysClose_subst_cimSelfIdxD]
  -- the guard is an IMPLICATION: refute it by walking `TailTo` through the
  -- `.impl` to the consequent, which is the Dupoc component's floor-priced
  -- ELSE-play (then-action C ≠ D). An atom-shaped lemma does NOT apply here.
  cases h : proofSearch k
      (.impl (.plays (.bot (.sys (mdSysD k) 0)) (.bot (.sys (mdSysD k) 1)) Action.C)
             (.plays (.bot (.sys (mdSysD k) 1)) (.bot (.sys (mdSysD k) 0)) Action.D)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      refine no_provable_botSysSearcherElse_tail k (mdSysD k) 1 k _ .C .D _ (by decide)
        (Nat.le_refl k) (mdSysD_get1 k) _ k _ hp (Nat.le_refl k) ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp)

/-- `inst .dupoc .dimcid`: Dupoc at the head (the mirrored orientation). -/
def dmSysD (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
    (.const .C) (.const .D))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem dmSysD_get0 (k : Nat) :
    (dmSysD k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.const .C) (.const .D)) := rfl

theorem dmSysD_get1 (k : Nat) :
    (dmSysD k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.D))
          (.const .D) (.const .C)) := rfl

/-- `inst .cimcic .dimcid`: CIMCIC at the head (the mirrored orientation). -/
def mmSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.C))
    (.const .C) (.const .D))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem mmSys_get0 (k : Nat) :
    (mmSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.C))
          (.const .C) (.const .D)) := rfl

theorem mmSys_get1 (k : Nat) :
    (mmSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.D))
          (.const .D) (.const .C)) := rfl

/-! ### dimcid × cimcic — anti-aligned, closed by the floor

The two `.impl`-guard bots facing each other at opposite consequent polarities.
DIMCID wants CIMCIC to play `D`, but CIMCIC's component fires `C`; CIMCIC wants
DIMCID to play `C`, but DIMCID's component fires `D`. Both guards are floor-false
and both members take their DEFAULTS: DIMCID cooperates, CIMCIC defects. -/

/-- `inst .dimcid .cimcic`: DIMCID at the head. -/
def mdSysM (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.C))
    (.const .C) (.const .D)) .nil)

theorem inst_dimcid_cimcic_eq (k : Nat) :
    inst (tauZoo k) .dimcid .cimcic = .sys (mdSysM k) 0 := rfl

theorem mdSysM_get0 (k : Nat) :
    (mdSysM k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.D))
          (.const .D) (.const .C)) := rfl

theorem mdSysM_get1 (k : Nat) :
    (mdSysM k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.C))
          (.const .C) (.const .D)) := rfl

/-- **τ(DIMCID) at CIMCIC COOPERATES**: its guard aims `D` at CIMCIC's component,
    whose then-action is `C` — floor-false through the `.impl`. -/
theorem dimcid_cimcic_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .cimcic))
      (.bot (inst (tauZoo k) .dimcid .cimcic)) (inst (tauZoo k) .dimcid .cimcic)
      = some Action.C := by
  rw [inst_dimcid_cimcic_eq]
  refine sysSearcher_plays_else _ _ (mdSysM_get0 k) ?_
  rw [sysClose_subst_cimSelfIdxD]
  cases h : proofSearch k
      (.impl (.plays (.bot (.sys (mdSysM k) 0)) (.bot (.sys (mdSysM k) 1)) Action.C)
             (.plays (.bot (.sys (mdSysM k) 1)) (.bot (.sys (mdSysM k) 0)) Action.D)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      refine no_provable_botSysSearcherElse_tail k (mdSysM k) 1 k _ .C .D _ (by decide)
        (Nat.le_refl k) (mdSysM_get1 k) _ k _ hp (Nat.le_refl k) ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp)

/-- The δ_L-style bit for the pair: `probe (inst .dimcid .cimcic)` is FALSE — the
    head component's then-action is `D`. -/
theorem ps_probe_inst_dimcid_cimcic_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimcid .cimcic)) = false := by
  rw [show probe (inst (tauZoo k) .dimcid .cimcic)
        = .plays (.bot (.sys (mdSysM k) 0)) (.bot (.sys (mdSysM k) 0)) Action.C
      from by rw [probe, inst_dimcid_cimcic_eq]]
  exact ps_botSys_mismatch_false hK (mdSysM k) 0 k _ .D .C _ (by decide)
    (Nat.le_refl k) (mdSysM_get0 k) _

/-- **τ(Dupoc) at DIMCID DEFECTS** — the mirrored side of the anti-aligned pair:
    its trust-probe aims `C` at the DIMCID component, whose then-action is `D`,
    so the probe is floor-false and the else-constant `D` runs. -/
theorem dupoc_dimcid_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .dimcid))
      (.bot (inst (tauZoo k) .dupoc .dimcid)) (inst (tauZoo k) .dupoc .dimcid)
      = some Action.D := by
  rw [show inst (tauZoo k) .dupoc .dimcid = .sys (dmSysD k) 0 from rfl]
  refine sysSearcher_plays_else _ _ (dmSysD_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_botSys_mismatch_false (Nat.le_refl k) (dmSysD k) 1 k _ .D .C _ (by decide)
    (Nat.le_refl k) (dmSysD_get1 k) _

/-- **τ(CIMCIC) at DIMCID DEFECTS** — the mirrored anti-aligned side: CIMCIC's
    guard aims `C` at the DIMCID component, whose then-action is `D`, so the
    guard is floor-false through the `.impl` and the else-constant `D` runs. -/
theorem cimcic_dimcid_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .dimcid))
      (.bot (inst (tauZoo k) .cimcic .dimcid)) (inst (tauZoo k) .cimcic .dimcid)
      = some Action.D := by
  rw [show inst (tauZoo k) .cimcic .dimcid = .sys (mmSys k) 0 from rfl]
  refine sysSearcher_plays_else _ _ (mmSys_get0 k) ?_
  rw [sysClose_subst_cimSelfIdx]
  cases h : proofSearch k
      (.impl (.plays (.bot (.sys (mmSys k) 0)) (.bot (.sys (mmSys k) 1)) Action.C)
             (.plays (.bot (.sys (mmSys k) 1)) (.bot (.sys (mmSys k) 0)) Action.C)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      refine no_provable_botSysSearcherElse_tail k (mmSys k) 1 k _ .D .C _ (by decide)
        (Nat.le_refl k) (mmSys_get1 k) _ k _ hp (Nat.le_refl k) ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp)

/-! ## Column-facing corollaries

The five columns that depend only on the ground cells, plus the δ_L one that the
dimcid×dupoc floor closure settles. The δ_Cu column's `.dimcid` arm needs the
dimcid×cupod pair, which is ALIGNED (mutual Löb) and left open — see the section
header above. -/

/-- δ_C bit: `inst .dimcid .coop` plays C, and provably so (its search FAILS, so
    the certificate is `search_f` over the refutation — floor-priced). Reported
    false: the trusting C sits behind a failed search, Guardian's shape again. -/
theorem ps_probe_inst_dimcid_coop_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimcid .coop)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .dimcid .coop)) with
  | false => rfl
  | true =>
      exfalso
      have hp := (proofSearch_spec _ _).1 h
      rw [probe, inst_dimcid_peel_coop k] at hp
      exact no_provable_botSearcherElse_tail k k _ .D .C (.const .C) (by decide)
        (Nat.le_refl k) _ K _ hp hK rfl

/-- δ_D bit: `inst .dimcid .defect` plays D — provable, `search_t` citing the
    fired guard. -/
theorem ps_probe_inst_dimcid_defect_false {k K : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimcid .defect)) = false := by
  exact ps_probe_false_of_plays_D K (dimcid_defect_plays_D hL)

/-- guard bit: `inst .dimcid .coop` does not provably DEFECT (it cooperates). -/
theorem ps_probeD_inst_dimcid_coop_false {k K : Nat} :
    proofSearch K (probeD (inst (tauZoo k) .dimcid .coop)) = false :=
  ps_probeD_false_of_plays_C K dimcid_coop_plays_C

/-- δ_L bit: `inst .dimcid .dupoc` cooperates but only through the floor. -/
theorem ps_probe_inst_dimcid_dupoc_false' {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dimcid .dupoc)) = false :=
  ps_probe_inst_dimcid_dupoc_false hK

end PD.Tau