import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.TowerCensus
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

/-- The diagonal SLOT: τ(DIMCID)'s self-play is `D` past the Löb threshold —
    the certified probe bit, read back through soundness. -/
theorem dimcid_dimcid_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .dimcid))
        (.bot (inst (tauZoo k) .dimcid .dimcid)) (inst (tauZoo k) .dimcid .dimcid)
        = some Action.D := by
  obtain ⟨k₂, h⟩ := ps_probeD_dimcid_quine
  refine ⟨k₂, fun k hk => ?_⟩
  exact entry_of_interp (Pf_sound _ _ ((proofSearch_spec _ _).1 (h k hk)))

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

-- `sysClose_subst_cimSelfIdxD` hoisted to `Tau/Theorems/Helpers.lean` (2026-08-24).

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

/-! ### The two prover partners — floor-priced DEFECTIONS

`inst .tftPf .dimcid` and `inst .just .dimcid` really DO defect against DIMCID
(their probes of DIMCID's floor-priced cooperation fail), so DIMCID's consequent
is TRUE here — and still uncitable: their `D` is the ELSE-play of a then-`C`
searcher, so every certificate pays `search_f`. DIMCID cannot convict them and
cooperates. Two more true-but-unprovable cells, the shape this zoo keeps
producing. -/

theorem dimcid_tftPf_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .tftPf))
      (.bot (inst (tauZoo k) .dimcid .tftPf)) (inst (tauZoo k) .dimcid .tftPf)
      = some Action.C :=
  dimcid_plays_C_of_searcherC .tftPf _ _ (inst_tftPf_peel k .dimcid)
    (inst_dimcid_peel_tftPf k)

theorem dimcid_just_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .just))
      (.bot (inst (tauZoo k) .dimcid .just)) (inst (tauZoo k) .dimcid .just)
      = some Action.C :=
  dimcid_plays_C_of_searcherC .just _ _ (inst_just_peel k .dimcid)
    (inst_dimcid_peel_just k)

/-! ### The row is COMPLETE (2026-08-25)

All fifteen slots are theorems; the row and phase live in `TauDIMCID/Phase.lean`.
The last two cells — `guardian` and `cupodTroll`, the then-`D` searcher partners —
closed with the TOWER CENSUS (`Base/TowerCensus.lean`, the section at the end of
this file), after both existing census techniques were shown to fail on them for
the same reason: the tail census's class contains `□(partner's guard) → T`, a
genuine theorem; the valuation census needs the forced pair `(bot I, bot P)`, a
`.bot` OPPONENT, and with it `iteBranchSearch_t` derives a real theorem whose
truth depends on the forced atom — and in the DIMCID-defects world `S` derives
`¬A` outright, so no sound valuation designates `A` there. The argument had to be
proof-theoretic: `¬A ⊬ A → T` (no object-level ex falso), formalised as a class
that tracks the PROVABILITY of box antecedents along the tail, nested through the
partner's guard. -/

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

/-! ## dimcid × cupod — ALIGNED ON DEFECTION, closed by mutual bounded Löb (2026-08-24)

The first aligned-on-`D` pair. DIMCID's member fires `D` from □(its guard); its
guard's consequent is "cupod's member defects against me", which cupod's searcher
concludes from □(DIMCID's member self-defects); and that self-defection is what
DIMCID's own reading concludes. Both legs are BOXED, so this is `mutual_pblt_engine_id`
verbatim — the same closure as `cimcic_dupoc_mutual`, at the other polarity, with
`implK` weakening cupod's reading into DIMCID's implication guard. -/

-- `sys_cross_impl_dim` hoisted to `Tau/Theorems/Helpers.lean` (2026-08-24).

/-- `inst .dimcid .cupod`: DIMCID at the head, Cupod punishing it. (`dcSys` in
    `TauCupod/Helpers` is the DUPOC×Cupod system — different bot, different name.) -/
def dimCupSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
    (.const .D) (.const .C)) .nil)

theorem inst_dimcid_cupod_eq (k : Nat) :
    inst (tauZoo k) .dimcid .cupod = .sys (dimCupSys k) 0 := rfl
theorem dimCupSys_get0 (k : Nat) :
    (dimCupSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.D))
          (.const .D) (.const .C)) := rfl
theorem dimCupSys_get1 (k : Nat) :
    (dimCupSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
          (.const .D) (.const .C)) := rfl

/-- `inst .cupod .dimcid`: Cupod at the head. -/
def cupDimSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
    (.const .D) (.const .C))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem inst_cupod_dimcid_eq (k : Nat) :
    inst (tauZoo k) .cupod .dimcid = .sys (cupDimSys k) 0 := rfl
theorem cupDimSys_get0 (k : Nat) :
    (cupDimSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
          (.const .D) (.const .C)) := rfl
theorem cupDimSys_get1 (k : Nat) :
    (cupDimSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.D))
          (.const .D) (.const .C)) := rfl

private theorem log_facts' (k : Nat) :
    Nat.log2 k ≤ k ∧ Nat.log2 0 = 0 ∧ Nat.log2 1 = 0 :=
  ⟨Nat.log2_le_self k, by decide, by decide⟩

/-- **The mutual engine, DIMCID-at-the-head**: `Af` = DIMCID's member (0)
    self-defects, `Bf` = its closed guard. Leg 1 is cupod's reading weakened by
    `implK` into the implication guard; leg 2 is DIMCID's own reading. -/
theorem dimCup_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, Pf m (.plays (.bot (.sys (dimCupSys k) 0)) (.bot (.sys (dimCupSys k) 0)) Action.D) := by
  refine mutual_pblt_engine_id
    (fun k => .plays (.bot (.sys (dimCupSys k) 0)) (.bot (.sys (dimCupSys k) 0)) Action.D)
    (fun k => .impl (.plays (.bot (.sys (dimCupSys k) 0)) (.bot (.sys (dimCupSys k) 1)) Action.C)
                    (.plays (.bot (.sys (dimCupSys k) 1)) (.bot (.sys (dimCupSys k) 0)) Action.D))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, dimCupSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, dimCupSys, numCost]; omega
  · intro k _
    have h1 := sys_cross_at (dimCupSys k) 1 0 k
      ((Formula.impl (.box k (.plays (.bot (.sys (dimCupSys k) 0)) (.bot (.sys (dimCupSys k) 0)) Action.D))
        (.plays (.bot (.sys (dimCupSys k) 1)) (.bot (.sys (dimCupSys k) 0)) Action.D)).size)
      (.bot (.sys (dimCupSys k) 0)) .D .C (dimCupSys_get1 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (dimCupSys k) 1)) (.bot (.sys (dimCupSys k) 0)) Action.D)
      (.plays (.bot (.sys (dimCupSys k) 0)) (.bot (.sys (dimCupSys k) 1)) Action.C)
      (k := (Formula.impl (.plays (.bot (.sys (dimCupSys k) 1)) (.bot (.sys (dimCupSys k) 0)) Action.D)
        (.impl (.plays (.bot (.sys (dimCupSys k) 0)) (.bot (.sys (dimCupSys k) 1)) Action.C)
               (.plays (.bot (.sys (dimCupSys k) 1)) (.bot (.sys (dimCupSys k) 0)) Action.D))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    obtain ⟨h, h0, h1'⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, dimCupSys, numCost]; omega
  · intro k _
    refine Pf_mono (sys_cross_impl_dim (dimCupSys k) 0 1 k _ (dimCupSys_get0 k) le_rfl) ?_
    obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, dimCupSys, numCost]; omega

/-- **The mutual engine, Cupod-at-the-head**: DIMCID's member is index 1. -/
theorem cupDim_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, Pf m (.plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 1)) Action.D) := by
  refine mutual_pblt_engine_id
    (fun k => .plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 1)) Action.D)
    (fun k => .impl (.plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 0)) Action.C)
                    (.plays (.bot (.sys (cupDimSys k) 0)) (.bot (.sys (cupDimSys k) 1)) Action.D))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, cupDimSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, cupDimSys, numCost]; omega
  · intro k _
    have h1 := sys_cross_at (cupDimSys k) 0 1 k
      ((Formula.impl (.box k (.plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 1)) Action.D))
        (.plays (.bot (.sys (cupDimSys k) 0)) (.bot (.sys (cupDimSys k) 1)) Action.D)).size)
      (.bot (.sys (cupDimSys k) 1)) .D .C (cupDimSys_get0 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (cupDimSys k) 0)) (.bot (.sys (cupDimSys k) 1)) Action.D)
      (.plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 0)) Action.C)
      (k := (Formula.impl (.plays (.bot (.sys (cupDimSys k) 0)) (.bot (.sys (cupDimSys k) 1)) Action.D)
        (.impl (.plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 0)) Action.C)
               (.plays (.bot (.sys (cupDimSys k) 0)) (.bot (.sys (cupDimSys k) 1)) Action.D))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    obtain ⟨h, h0, h1'⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, cupDimSys, numCost]; omega
  · intro k _
    refine Pf_mono (sys_cross_impl_dim (cupDimSys k) 1 0 k _ (cupDimSys_get1 k) le_rfl) ?_
    obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, cupDimSys, numCost]; omega

/-- The cheap budget-`k` re-certification of the DIMCID member's defection from
    its FIRED guard (`search_t` cites via `c_guard`). -/
theorem pf_dimcidSys_D_of_guard {defs : ProgList} {i j k : Nat}
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
             (.plays (.bot (.selfIdx j)) .self Action.D)) (.const .D) (.const .C)))
    (hkk : c_guard k + 5 ≤ k)
    (hBf : Pf k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D))) :
    Pf k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D) := by
  have hpre : Pf k (((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.C)
      (.plays (.bot (.selfIdx j)) .self Action.D)).sysClose defs).subst
      (.bot (.sys defs i)) (.bot (.sys defs i))) := by
    rw [sysClose_subst_cimSelfIdxD]; exact hBf
  have h1 := PlaysProof.search_t (q := .const .C) hpre
    (PlaysProof.const (me := .bot (.sys defs i)) (opponent := .bot (.sys defs i))
      (a := Action.D))
  have hbody : PlaysProof (.bot (.sys defs i)) (.bot (.sys defs i)) (.sys defs i) Action.D
      (c_leaf + c_guard k + c_node + c_node) :=
    PlaysProof.sysStep hget (by simp only [Prog.sysClose]; exact h1)
  exact Pf.atom ⟨PlaysProof.bot hbody, by have := hcl; have := hcn; omega⟩

/-- **τ(DIMCID) at Cupod DEFECTS** (Löb-gated) — the `.cupod` slot of its row. -/
theorem dimcid_cupod_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .cupod))
        (.bot (inst (tauZoo k) .dimcid .cupod)) (inst (tauZoo k) .dimcid .cupod)
        = some Action.D := by
  obtain ⟨kL, hLb⟩ := dimCup_mutual
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hLb k hk
  rw [inst_dimcid_cupod_eq k]
  exact entry_of_interp (Pf_sound m _ hm)

/-- **The `hdc` gate**: `probeD (inst .dimcid .cupod)` is PROVABLE at `k` — eval
    inversion recovers the fired guard, then the cheap re-certification. -/
theorem ps_probeD_inst_dimcid_cupod :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probeD (inst (tauZoo k) .dimcid .cupod)) = true := by
  obtain ⟨kL, hLp⟩ := dimcid_cupod_plays_D
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  refine ⟨max kL kA, fun k hk => ?_⟩
  have hplay := hLp k (by omega)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k := hkA k (by omega)
  have hkk : c_guard k + 5 ≤ k := by simp only [c_guard, numCost]; omega
  rw [inst_dimcid_cupod_eq k] at hplay
  have hfired := sysSearcher_fired_of_plays (by decide) _ _ (dimCupSys_get0 k) hplay
  rw [sysClose_subst_cimSelfIdxD] at hfired
  rw [probeD, inst_dimcid_cupod_eq k]
  exact (proofSearch_spec _ _).2
    (pf_dimcidSys_D_of_guard (dimCupSys_get0 k) hkk ((proofSearch_spec _ _).1 hfired))

/-- **The `hdcP` gate**: τ(Cupod) DEFECTS against τ(DIMCID) — its punish-search
    fires on the DIMCID member's Löb-certified self-defection. -/
theorem cupod_dimcid_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dimcid))
        (.bot (inst (tauZoo k) .cupod .dimcid)) (inst (tauZoo k) .cupod .dimcid)
        = some Action.D := by
  obtain ⟨kL, hLb⟩ := cupDim_mutual
  obtain ⟨kC, hkC⟩ := cg_headroom
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  refine ⟨max kL (max kC kA), fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hLb k (by omega)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k := hkA k (by omega)
  have hkk : c_guard k + 5 ≤ k := by simp only [c_guard, numCost]; omega
  have hplay : ∃ N, eval N (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 1))
      (.sys (cupDimSys k) 1) = some Action.D := entry_of_interp (Pf_sound m _ hm)
  have hfired := sysSearcher_fired_of_plays (by decide) _ _ (cupDimSys_get1 k) hplay
  rw [sysClose_subst_cimSelfIdxD] at hfired
  have hAf : Pf k (.plays (.bot (.sys (cupDimSys k) 1)) (.bot (.sys (cupDimSys k) 1)) Action.D) :=
    pf_dimcidSys_D_of_guard (cupDimSys_get1 k) hkk ((proofSearch_spec _ _).1 hfired)
  rw [inst_cupod_dimcid_eq k]
  exact sysSearcher_head_plays (cupDimSys_get0 k) (hkC k (by omega)) hAf

/-! ## The four REACHABLE off-cycle cells (2026-08-25)

The partner's instance against DIMCID is a `.bot`-frozen `.ite` cascade — an
UNREADABLE player (no `ReadableMe` disjunct is `.bot (.ite …)`), so DIMCID's
guard `(I play C vs them) → (they play D vs me)` is unprovable as soon as the
consequent has no certificate in the relevant budget range:

* tftSim, ebot, dbot play `C` against DIMCID, so their `D`-play has NO
  certificate at any budget (soundness + `eval_det`) — the budget-FREE census
  `no_provable_tailTo_unreadable`;
* obot really DOES defect against DIMCID, but every transcript of that
  defection runs its first watch, `inst .dimcid .coop`, whose `C` is
  floor-priced — so the certificate costs more than `k`, and the budget-`k`
  floor census `no_provable_tailTo_floor` closes it.

In all four DIMCID cooperates: the else-play. -/

/-- DIMCID cooperates with any partner whose instance is an `.ite` cascade that
    plays `C` against it in EVERY frame (the cascade is `.opp`-free, so its play
    does not depend on the frame). -/
theorem dimcid_plays_C_of_iteC {k : Nat} (T : Tmpl) (b : Prog) (aT : Action) (p q : Prog)
    (hpeelT : inst (tauZoo k) T .dimcid = .ite b aT p q)
    (hpeelD : inst (tauZoo k) .dimcid T
      = .search k (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) Action.C)
                         (.plays (.bot (inst (tauZoo k) T .dimcid)) .self Action.D))
          (.const .D) (.const .C))
    (hplaysC : ∀ me opp, ∃ N, eval N me opp (inst (tauZoo k) T .dimcid) = some Action.C) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid T))
      (.bot (inst (tauZoo k) .dimcid T)) (inst (tauZoo k) .dimcid T)
      = some Action.C := by
  -- the guard is unprovable at every budget: budget-free unreadable census
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) T .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid T)) (.bot (inst (tauZoo k) .dimcid T))) = false := by
    rw [dimG_subst]
    cases h : proofSearch k (dimG (.bot (inst (tauZoo k) .dimcid T))
        (inst (tauZoo k) T .dimcid)) with
    | false => rfl
    | true =>
        exfalso
        have hp := (proofSearch_spec _ _).1 h
        refine no_provable_tailTo_unreadable (.bot (inst (tauZoo k) T .dimcid))
          (.bot (inst (tauZoo k) .dimcid T)) .D ?_ ?_ ?_ ?_ ?_ hp ⟨rfl, by simp⟩
        · -- no D-certificate at any budget: the cascade plays C in this frame
          intro n hA
          obtain ⟨m, hm⟩ := Pf_sound n _ (Pf.atom hA)
          obtain ⟨N, hN⟩ := hplaysC (.bot (inst (tauZoo k) T .dimcid))
            (.bot (inst (tauZoo k) .dimcid T))
          have hN' : eval (N + 1) (.bot (inst (tauZoo k) T .dimcid))
              (.bot (inst (tauZoo k) .dimcid T)) (.bot (inst (tauZoo k) T .dimcid))
              = some Action.C := by rw [eval]; exact hN
          rw [play] at hm
          exact absurd (eval_det hm hN') (by decide)
        · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
            ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, h⟩) <;>
            simp [hpeelT] at h
        · intro L
          cases L with
          | nil => simp [searchPlug]
          | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
        · intro hd L; cases hd <;> simp [ctxPlug]
        · intro hd L; cases hd <;> simp [plug2]
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimcid T)) = Me at hg ⊢
  rw [hpeelD]
  exact searchGuardD_plays_C _ _ hg

/-- τ(DIMCID) at TFTSim COOPERATES. -/
theorem dimcid_tftSim_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .tftSim))
      (.bot (inst (tauZoo k) .dimcid .tftSim)) (inst (tauZoo k) .dimcid .tftSim)
      = some Action.C :=
  dimcid_plays_C_of_iteC .tftSim _ _ _ _ (inst_tftSim_peel k .dimcid)
    (inst_dimcid_peel_tftSim k)
    (fun me opp => by rw [inst_tftSim_peel k .dimcid]; exact simCopy_plays _ _ dimcid_coop_plays_C)

/-- τ(DIMCID) at EBot COOPERATES. -/
theorem dimcid_ebot_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .ebot))
      (.bot (inst (tauZoo k) .dimcid .ebot)) (inst (tauZoo k) .dimcid .ebot)
      = some Action.C :=
  dimcid_plays_C_of_iteC .ebot _ _ _ _ (inst_ebot_peel k .dimcid)
    (inst_dimcid_peel_ebot k)
    (fun me opp => by
      rw [inst_ebot_peel k .dimcid]
      exact simWatchC_falls _ _ (dimcid_defect_plays_D hL)
        (simWatchC_fires _ _ dimcid_coop_plays_C))

/-- τ(DIMCID) at DBot COOPERATES. -/
theorem dimcid_dbot_plays_C {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .dbot))
      (.bot (inst (tauZoo k) .dimcid .dbot)) (inst (tauZoo k) .dimcid .dbot)
      = some Action.C :=
  dimcid_plays_C_of_iteC .dbot _ _ _ _ (inst_dbot_peel k .dimcid)
    (inst_dimcid_peel_dbot k)
    (fun me opp => by
      rw [inst_dbot_peel k .dimcid]
      exact simWatchC_falls _ _ (dimcid_defect_plays_D hL) ⟨1, rfl⟩)

/-! ### obot — the defector whose defection is too expensive to cite -/

/-- Any transcript of a watch on `inst .dimcid .coop` costs MORE than `k`: a
    `C` transcript is a certificate of the floor-priced probe, a `D` transcript
    is unsound. -/
theorem dimcid_coop_watch_over_budget {k : Nat} {me opp : Prog} {r : Action} {m : Nat}
    (h : PlaysProof me opp
      (.sim (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop))) r m)
    (hm : m ≤ k) : False := by
  cases h with
  | sim hin =>
    simp only [Prog.subst] at hin
    cases hin with
    | bot hin3 =>
      rename_i m₃
      have hcert : AtomProvable (m₃ + c_node)
          (.plays (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop)) r) :=
        ⟨PlaysProof.bot hin3, le_refl _⟩
      cases r with
      | C =>
          have h1 := (proofSearch_spec _ _).2 (Pf.atom hcert)
          have h2 := ps_probe_inst_dimcid_coop_false (k := k) (K := m₃ + c_node)
            (by have := hcn; omega)
          rw [probe] at h2
          exact absurd (h1.symm.trans h2) (by decide)
      | D =>
          obtain ⟨n, hn⟩ := Pf_sound _ _ (Pf.atom hcert)
          obtain ⟨N, hN⟩ := dimcid_coop_plays_C (k := k)
          have hN' : eval (N + 1) (.bot (inst (tauZoo k) .dimcid .coop))
              (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop))
              = some Action.C := by rw [eval]; exact hN
          rw [play] at hn
          exact absurd (eval_det hn hN') (by decide)

/-- τ(DIMCID) at OBot COOPERATES: obot defects against it, but no certificate of
    that defection fits in `k`, so DIMCID's guard is floor-unprovable. -/
theorem dimcid_obot_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .obot))
      (.bot (inst (tauZoo k) .dimcid .obot)) (inst (tauZoo k) .dimcid .obot)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .obot .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .obot .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid .obot)) (.bot (inst (tauZoo k) .dimcid .obot))) = false := by
    rw [dimG_subst]
    cases h : proofSearch k (dimG (.bot (inst (tauZoo k) .dimcid .obot))
        (inst (tauZoo k) .obot .dimcid)) with
    | false => rfl
    | true =>
        exfalso
        have hp := (proofSearch_spec _ _).1 h
        rw [inst_obot_peel k .dimcid] at hp
        refine no_provable_tailTo_floor k _ (.bot (inst (tauZoo k) .dimcid .obot)) .D
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ k _ hp le_rfl ⟨rfl, by simp⟩
        · -- the cost floor: every D-transcript runs the coop watch
          rintro K hK ⟨hpp, hn⟩
          cases hpp with
          | bot hin =>
            cases hin with
            | ite_t hg' _ _ => exact dimcid_coop_watch_over_budget hg' (by omega)
            | ite_f hg' _ _ => exact dimcid_coop_watch_over_budget hg' (by omega)
        · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
            ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
        · intro defs i h; simp at h
        · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
        · intro L
          cases L with
          | nil => simp [searchPlug]
          | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug]
        · intro hd L; cases hd <;> simp [ctxPlug]
        · intro hd L h; cases hd <;> simp [plug2] at h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimcid .obot)) = Me at hg ⊢
  rw [inst_dimcid_peel_obot k]
  exact searchGuardD_plays_C _ _ hg

/-! ## The two then-`D` partner cells — closed by the TOWER CENSUS (2026-08-25)

`Base/TowerCensus.lean` is the provability-tracking kernel built for exactly these
two cells. Guardian's chain has three targets: DIMCID's consequent `T` ("guardian
plays D against me"), guardian's guard `Y` ("`inst .dimcid .coop` self-defects"),
and the consequent `T₃` of THAT instance's guard ("the constant cooperator
defects") — whose player nothing reads, so the chain ends. CupodTroll's has two:
its guard is the index-decided `.eq (const C) (const D)`, an atom no rule reads. -/

/-- Level 3: the constant cooperator's defection against `inst .dimcid .coop`. -/
private abbrev Z₃ (k : Nat) : Formula :=
  .plays (.bot (.const .C)) (.bot (inst (tauZoo k) .dimcid .coop)) Action.D

private theorem level3 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Z₃ k) (DeadAll []) n φ → False := by
  refine tower_census (Z₃ k) [] ⟨Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp at h, trivial⟩
    DeadAll_nil_kill ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro K ⟨hpp, -⟩
    cases hpp with
    | bot hin => cases hin
  · intro g ψ b c opp h; simp at h
  · intro p q opp a h; simp at h
  · intro p q opp a h; simp at h
  · intro g ψ b c opp h; simp at h
  · intro defs i opp a h; simp at h
  · intro z a' g ψ c0 c1 q opp h; simp at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp at h
  · intro g₁ ψ₁ e₁ L a opp h; simp at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug] at h
  · intro hd L a opp h; cases hd <;> simp [plug2] at h

/-- Level 2 (guardian): guardian's guard — `inst .dimcid .coop` self-defects. -/
private abbrev Y₂ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop)) Action.D

private theorem level2 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Y₂ k) (DeadAll [Z₃ k]) n φ → False := by
  refine tower_census (Y₂ k) [Z₃ k]
    ⟨Or.inl ⟨_, _, _, rfl⟩, ?_, Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill (level3 k) DeadAll_nil_kill) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Z' h; simp only [List.mem_singleton] at h; subst h
    intro h; simp [inst_dimcid_peel_coop] at h
  · -- no certificate: the instance cooperates
    intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := dimcid_coop_plays_C (k := k)
    have hN' : eval (N + 1) (.bot (inst (tauZoo k) .dimcid .coop))
        (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop))
        = some Action.C := by rw [eval]; exact hN
    rw [play] at hm
    exact absurd (eval_det hm hN') (by decide)
  · intro g ψ b c opp h; simp [inst_dimcid_peel_coop] at h
  · intro p q opp a h; simp [inst_dimcid_peel_coop] at h
  · intro p q opp a h; simp [inst_dimcid_peel_coop] at h
  · -- THE reading rule: its box is the guard of `inst .dimcid .coop`, a level-3 formula
    intro g ψ b c opp h
    simp only [Y₂] at h
    rw [inst_dimcid_peel_coop] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst, inst_coop_peel k .dimcid]
    refine (TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, fun h => h⟩
    intro m hm hT
    have hm0 : m = 0 := by omega
    subst hm0
    have := (TowerAt_zero_plays _ _ _ _ _).1 hT
    simp at this
  · intro defs i opp a h; simp [inst_dimcid_peel_coop] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_dimcid_peel_coop] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_dimcid_peel_coop] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_dimcid_peel_coop] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_dimcid_peel_coop] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_dimcid_peel_coop] at h

/-- Level 1 (guardian): DIMCID's consequent — guardian defects against it. -/
private abbrev T₁ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .guardian .dimcid)) (.bot (inst (tauZoo k) .dimcid .guardian))
    Action.D

/-- Guardian COOPERATES with DIMCID in DIMCID's own frame: its punish-search on
    `inst .dimcid .coop` fails. -/
private theorem guardian_plays_C_vs_dimcid (k : Nat) :
    ∃ N, eval N (.bot (inst (tauZoo k) .guardian .dimcid)) (.bot (inst (tauZoo k) .dimcid .guardian))
      (.bot (inst (tauZoo k) .guardian .dimcid)) = some Action.C := by
  have hY : proofSearch k
      ((Formula.plays (.bot (inst (tauZoo k) .dimcid .coop)) (.bot (inst (tauZoo k) .dimcid .coop))
        Action.D).subst (.bot (inst (tauZoo k) .guardian .dimcid))
        (.bot (inst (tauZoo k) .dimcid .guardian))) = false := by
    simp only [Formula.subst, Prog.subst]
    exact ps_probeD_false_of_plays_C k dimcid_coop_plays_C
  obtain ⟨N, hN⟩ := searchGuardD_plays_C (k := k)
    (.bot (inst (tauZoo k) .guardian .dimcid)) (.bot (inst (tauZoo k) .dimcid .guardian)) hY
  refine ⟨N + 1, ?_⟩
  rw [eval, inst_guardian_peel k .dimcid]
  exact hN

private theorem level1 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (T₁ k) (DeadAll [Y₂ k, Z₃ k]) n φ → False := by
  refine tower_census (T₁ k) [Y₂ k, Z₃ k]
    ⟨Or.inl ⟨_, _, _, rfl⟩, ?_,
     Or.inl ⟨_, _, _, rfl⟩, ?_, Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill (level2 k) (DeadAll_cons_kill (level3 k) DeadAll_nil_kill))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Z' h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · intro h; simp [inst_guardian_peel, inst_dimcid_peel_coop] at h
    · intro h; simp [inst_guardian_peel] at h
  · intro Z' h; simp only [List.mem_singleton] at h; subst h
    intro h; simp [inst_dimcid_peel_coop] at h
  · -- no certificate: guardian cooperates
    intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := guardian_plays_C_vs_dimcid k
    rw [play] at hm
    exact absurd (eval_det hm hN) (by decide)
  · intro g ψ b c opp h; simp [inst_guardian_peel] at h
  · intro p q opp a h; simp [inst_guardian_peel] at h
  · intro p q opp a h; simp [inst_guardian_peel] at h
  · -- THE reading rule: guardian's box is its guard, a level-2 formula
    intro g ψ b c opp h
    simp only [T₁] at h
    rw [inst_guardian_peel k .dimcid] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst]
    exact (TowerAt_zero_plays _ _ _ _ _).2 rfl
  · intro defs i opp a h; simp [inst_guardian_peel] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_guardian_peel] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_guardian_peel] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_guardian_peel] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_guardian_peel] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_guardian_peel] at h

/-- **τ(DIMCID) at Guardian COOPERATES**: its guard is unprovable at every budget. -/
theorem dimcid_guardian_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .guardian))
      (.bot (inst (tauZoo k) .dimcid .guardian)) (inst (tauZoo k) .dimcid .guardian)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .guardian .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .guardian .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid .guardian)) (.bot (inst (tauZoo k) .dimcid .guardian)))
      = false := by
    rw [dimG_subst]
    cases h : proofSearch k (dimG (.bot (inst (tauZoo k) .dimcid .guardian))
        (inst (tauZoo k) .guardian .dimcid)) with
    | false => rfl
    | true =>
        exfalso
        refine level1 k k 0 _ ((proofSearch_spec _ _).1 h)
          ((TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, ?_⟩)
        · intro m hm hT
          have hm0 : m = 0 := by omega
          subst hm0
          have := (TowerAt_zero_plays _ _ _ _ _).1 hT
          simp at this
        · rintro (⟨m, -, hT⟩ | ⟨m, -, hT⟩ | h)
          · cases m with
            | zero => have := (TowerAt_zero_plays _ _ _ _ _).1 hT; simp [inst_guardian_peel, inst_dimcid_peel_coop] at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · cases m with
            | zero => have := (TowerAt_zero_plays _ _ _ _ _).1 hT; simp at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · exact h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimcid .guardian)) = Me at hg ⊢
  rw [inst_dimcid_peel_guardian k]
  exact searchGuardD_plays_C _ _ hg

/-! ### cupodTroll — two levels, the second an identity atom -/

private abbrev Zc₂ : Formula := .eq (.const Action.C) (.const Action.D)

private theorem levelc2 :
    ∀ K n φ, Pf K φ → TowerAt Zc₂ (DeadAll []) n φ → False := by
  refine tower_census Zc₂ [] ⟨Or.inr ⟨_, _, by simp, rfl⟩, fun Z' h => by simp at h, trivial⟩
    DeadAll_nil_kill ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K h; cases h
  all_goals (intros; simp_all)

private abbrev Tc₁ (k : Nat) : Formula :=
  .plays (.bot (inst (tauZoo k) .cupodTroll .dimcid)) (.bot (inst (tauZoo k) .dimcid .cupodTroll))
    Action.D

private theorem cupodTroll_plays_C_vs_dimcid (k : Nat) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll .dimcid))
      (.bot (inst (tauZoo k) .dimcid .cupodTroll)) (.bot (inst (tauZoo k) .cupodTroll .dimcid))
      = some Action.C := by
  have hY : proofSearch k
      ((Formula.eq (.const Action.C) (.const Action.D)).subst
        (.bot (inst (tauZoo k) .cupodTroll .dimcid)) (.bot (inst (tauZoo k) .dimcid .cupodTroll)))
      = false := by
    simp only [Formula.subst, Prog.subst]
    cases hps : proofSearch k (Formula.eq (.const Action.C) (.const Action.D)) with
    | false => rfl
    | true =>
        have := Pf_sound _ _ ((proofSearch_spec _ _).1 hps)
        simp [Formula.interp] at this
  obtain ⟨N, hN⟩ := searchGuardD_plays_C (k := k)
    (.bot (inst (tauZoo k) .cupodTroll .dimcid)) (.bot (inst (tauZoo k) .dimcid .cupodTroll)) hY
  refine ⟨N + 1, ?_⟩
  rw [eval, inst_cupodTroll_peel k .dimcid (by decide)]
  exact hN

private theorem levelc1 (k : Nat) :
    ∀ K n φ, Pf K φ → TowerAt (Tc₁ k) (DeadAll [Zc₂]) n φ → False := by
  refine tower_census (Tc₁ k) [Zc₂]
    ⟨Or.inl ⟨_, _, _, rfl⟩, fun Z' h => by simp only [List.mem_singleton] at h; subst h; simp,
     Or.inr ⟨_, _, by simp, rfl⟩, fun Z' h => by simp at h, trivial⟩
    (DeadAll_cons_kill levelc2 DeadAll_nil_kill) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K h
    obtain ⟨m, hm⟩ := Pf_sound K _ (Pf.atom h)
    obtain ⟨N, hN⟩ := cupodTroll_plays_C_vs_dimcid k
    rw [play] at hm
    exact absurd (eval_det hm hN) (by decide)
  · intro g ψ b c opp h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro p q opp a h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro p q opp a h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro g ψ b c opp h
    simp only [Tc₁] at h
    rw [inst_cupodTroll_peel k .dimcid (by decide)] at h
    simp only [Formula.plays.injEq, Prog.bot.injEq, Prog.search.injEq, Prog.const.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -⟩ := h
    refine Or.inl ⟨1, le_rfl, (TowerAt_succ_box _ _ _ _ _).2 ?_⟩
    simp only [Formula.subst, Prog.subst]
    exact (TowerAt_zero_eq _ _ _ _).2 rfl
  · intro defs i opp a h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro z a' g ψ c0 c1 q opp h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro k₁ ψ₁ k₂ ψ₂ c0 c1 q opp h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro g₁ ψ₁ e₁ L a opp h; simp [inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro hd L a opp h; cases hd <;> simp [ctxPlug, inst_cupodTroll_peel k .dimcid (by decide)] at h
  · intro hd L a opp h; cases hd <;> simp [plug2, inst_cupodTroll_peel k .dimcid (by decide)] at h

/-- **τ(DIMCID) at CupodTroll COOPERATES**: its guard is unprovable at every budget. -/
theorem dimcid_cupodTroll_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .cupodTroll))
      (.bot (inst (tauZoo k) .dimcid .cupodTroll)) (inst (tauZoo k) .dimcid .cupodTroll)
      = some Action.C := by
  have hg : proofSearch k
      ((Formula.impl (.plays .self (.bot (inst (tauZoo k) .cupodTroll .dimcid)) Action.C)
                     (.plays (.bot (inst (tauZoo k) .cupodTroll .dimcid)) .self Action.D)).subst
        (.bot (inst (tauZoo k) .dimcid .cupodTroll)) (.bot (inst (tauZoo k) .dimcid .cupodTroll)))
      = false := by
    rw [dimG_subst]
    cases h : proofSearch k (dimG (.bot (inst (tauZoo k) .dimcid .cupodTroll))
        (inst (tauZoo k) .cupodTroll .dimcid)) with
    | false => rfl
    | true =>
        exfalso
        refine levelc1 k k 0 _ ((proofSearch_spec _ _).1 h)
          ((TowerAt_impl _ _ _ _ _).2 ⟨(TowerAt_zero_plays _ _ _ _ _).2 rfl, ?_, ?_⟩)
        · intro m hm hT
          have hm0 : m = 0 := by omega
          subst hm0
          have := (TowerAt_zero_plays _ _ _ _ _).1 hT
          simp at this
        · rintro (⟨m, -, hT⟩ | h)
          · cases m with
            | zero => have := (TowerAt_zero_plays _ _ _ _ _).1 hT; simp at this
            | succ _ => exact TowerAt_succ_plays _ _ _ _ _ _ hT
          · exact h
  generalize hMe : (Prog.bot (inst (tauZoo k) .dimcid .cupodTroll)) = Me at hg ⊢
  rw [inst_dimcid_peel_cupodTroll k]
  exact searchGuardD_plays_C _ _ hg

end PD.Tau