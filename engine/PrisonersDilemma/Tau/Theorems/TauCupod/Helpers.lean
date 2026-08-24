import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.Transpose

/-!
# Tau/Theorems/TauCupod — the suspicious cooperator's mathematics

τ(Cupod) is τ(Dupoc)'s mirror: same self-probe geometry, inverted polarity. It
proves DEFECTION and punishes; it trusts by default. Three shapes to handle:

* **off-cycle hypotheses** — an ordinary `probeD` prove-stage, so the existing
  `searchProbeD_plays_*` shape lemmas apply verbatim;
* **the diagonal** — the quine, with `.D` in the guard: "if I can prove I defect
  against myself, defect". Unlike Dupoc's, this fixpoint is NOT closed by bounded
  Löb — Löb gives you `□φ → φ ⊢ φ` for the sentence the searcher FIRES on, and
  here firing means defecting, so the Löbian route would prove self-defection.
  What actually holds is the opposite and it is cheap: the guard is REFUTABLE
  (a cost floor), so the search fails and Cupod trusts itself;
* **the entangled cell** — `.sys`, handled in `Columns.lean` where both sides of
  the 2-cycle are in scope.
-/

set_option maxHeartbeats 2000000

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The diagonal: τ(Cupod)'s quine is LÖBIAN, and it proves SELF-DEFECTION

The mirror of Dupoc's Löb quine with the polarity inverted — and the inversion
changes what the fixpoint MEANS. Dupoc's guard fires on cooperation, so bounded Löb
delivers self-cooperation. Cupod's guard fires on DEFECTION with a trusting default,
so the very same machinery (`botSearchStep` is polarity-generic: it takes the
then/else actions as parameters) delivers **self-DEFECTION**: past the threshold
τ(Cupod) proves it defects against itself, so it does.

*A first attempt to refute the guard by the `search_f` floor was WRONG and the
kernel caught it: `no_provable_botSearcherElse_tail` excludes the ELSE-play (here
`.C`), but the guard atom is about the THEN-play `.D`, which `search_t` reaches.
The floor says nothing about it; Löb does.*

This is the tau image of base CupodBot's suspicion turning on itself — the
suspicious cooperator is exactly the bot its own test convicts. -/

/-- The Löb premise for Cupod's quine: S reads the frozen searcher's own source and
    concludes `□_k φ* → φ*` for `φ* = probeD (inst .cupod .cupod)`. Identical to
    Dupoc's construction with the branch actions swapped. -/
private theorem cupod_quine_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (probeD (inst (tauZoo k) .cupod .cupod)))
             (probeD (inst (tauZoo k) .cupod .cupod))) :=
  Pf.botSearchStep k (.plays .self .self .D) .D .C
    (.bot (inst (tauZoo k) .cupod .cupod)) (.bot (inst (tauZoo k) .cupod .cupod)) rfl
    (by
      simp only [inst_cupod_quine, Formula.subst, Prog.subst, Formula.size,
        Prog.size, numCost]
      omega)

/-- From an actual DEFECTING play of the wrapped quine against itself, the guard
    must have fired (eval inversion — a false guard forces the trusting C). -/
private theorem probeD_true_of_quine_play (k n : Nat)
    (h : play n (.bot (inst (tauZoo k) .cupod .cupod))
           (.bot (inst (tauZoo k) .cupod .cupod)) = some .D) :
    proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true := by
  cases hps : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) with
  | true => rfl
  | false =>
      exfalso
      have hps' : proofSearch k
          ((Formula.plays .self .self Action.D).subst
            (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
            (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C))))
          = false := hps
      rw [inst_cupod_quine] at h
      match n with
      | 0 => simp [play, eval] at h
      | 1 => simp [play, eval] at h
      | 2 => simp [play, eval, hps'] at h
      | n + 3 => simp [play, eval, hps'] at h

/-- **THE LÖB BIT, inverted**: past a threshold τ(Cupod)'s self-defection atom is
    provable at the probing budget itself. -/
theorem ps_probeD_inst_cupod_quine :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true := by
  have hφsz : ∀ k, (probeD (inst (tauZoo k) .cupod .cupod)).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [probeD, inst_cupod_quine, Formula.size, Prog.size, numCost]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150)
        (.impl (.box k (probeD (inst (tauZoo k) .cupod .cupod)))
               (probeD (inst (tauZoo k) .cupod .cupod))) :=
    fun k _ => cupod_quine_loeb_premise k
  obtain ⟨k₂, hk₂⟩ :=
    pblt_engine_id (fun k => probeD (inst (tauZoo k) .cupod .cupod))
      (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  exact probeD_true_of_quine_play k n hn

/-- **τ(Cupod) DEFECTS AGAINST ITSELF**: past the Löb threshold its punish-guard
    fires on its own diagonal. -/
theorem inst_cupod_quine_plays_D {k : Nat}
    (hq : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .cupod))
      (.bot (inst (tauZoo k) .cupod .cupod)) (inst (tauZoo k) .cupod .cupod)
      = some Action.D := by
  have h : proofSearch k ((Formula.plays Prog.self Prog.self Action.D).subst
      (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
      (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C))))
      = true := by simpa [probeD, inst_cupod_quine k, Formula.subst, Prog.subst] using hq
  refine ⟨2, ?_⟩
  conv_lhs => arg 4; rw [inst_cupod_quine k]
  rw [eval]
  rw [show (Formula.plays Prog.self Prog.self Action.D).subst
        (.bot (inst (tauZoo k) .cupod .cupod)) (.bot (inst (tauZoo k) .cupod .cupod))
      = (Formula.plays Prog.self Prog.self Action.D).subst
        (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
        (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
      from by rw [inst_cupod_quine k], h]
  rfl

/-! ## Cupod's own plays at the two constant hypotheses

Both reduce to shapes the shared `Helpers` already certifies: at the cooperator the
punish-probe is refutable (`ps_probeD_false_of_plays_C`), at the defector it fires
(`ps_probeD_constD`). Same structure as Guardian's row — Cupod is a punisher too,
differing only in WHOM it probes (the hypothesis-vs-me, not the hypothesis-vs-the
cooperator). -/

/-- τ(Cupod) TRUSTS the unconditional cooperator: nothing to convict. -/
theorem cupod_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .coop)) (.bot (inst (tauZoo k) .cupod .coop))
      (inst (tauZoo k) .cupod .coop) = some Action.C :=
  searchProbeD_plays_C _ _ (ps_probeD_false_of_plays_C k ⟨1, rfl⟩)

/-- τ(Cupod) PUNISHES the defector: its defection is a trivial positive atom. -/
theorem cupod_defect_plays_D {k : Nat} (hk : 2 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .defect))
      (.bot (inst (tauZoo k) .cupod .defect))
      (inst (tauZoo k) .cupod .defect) = some Action.D :=
  searchProbeD_plays_D _ _ (ps_probeD_constD hk)

/-! ## THE ENTANGLED CELL — the 2-cycle, CLOSED BY THE FLOOR (2026-08-21)

`inst .cupod .dupoc` is the 2-member system: component 0 (Cupod-seeing-Dupoc) fires
on proving component 1 DEFECTS; component 1 (Dupoc-seeing-Cupod) fires on proving
component 0 COOPERATES. Since the wrapped-emission fix each component freezes its
partner exactly as off-cycle guards freeze instances — `.bot (.selfIdx j)`, closing
to `.bot (.sys defs j)` — so component 0's closed guard is `probeD` of the wrapped
Dupoc component and component 1's is `probe` of the wrapped Cupod component.

**Neither guard is provable — a THEOREM, not a hypothesis**
(`ps_botSys_mismatch_false`, riding `no_provable_botSysSearcherElse_tail`): each
guard's target action MISMATCHES its subject component's then-action (Cupod wants
the trusting Dupoc component to defect; Dupoc wants the punishing Cupod component
to cooperate), so `search_t` cannot conclude it and the only other route prices in
the partner's `search_f` floor. The 2-cycle bounded Löb cannot close (opposite
actions — see the cross-implication record below), the floor DECIDES: both
components play their defaults — Cupod trusts (C), Dupoc defects (D) — the tau
image of the base red cell `outcome_DupocBot_vs_CupodBot = (D, C)`. What entered
the phase theorems as hypotheses (`hdc`, `hcdP`, and the δ_L column's
`hcupodDupoc`) is now supplied by the four closure theorems below. -/

/-- The pair's system, named once (the `inst .cupod .dupoc` orientation). -/
def cdSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
    (.const .D) (.const .C))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
    (.const .C) (.const .D)) .nil)

theorem inst_cupod_dupoc_eq (k : Nat) :
    inst (tauZoo k) .cupod .dupoc = .sys (cdSys k) 0 := rfl

theorem cdSys_get0 (k : Nat) :
    (cdSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
          (.const .D) (.const .C)) := rfl

theorem cdSys_get1 (k : Nat) :
    (cdSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.const .C) (.const .D)) := rfl

/-- The other orientation's system, `inst .dupoc .cupod`: Dupoc at the head. -/
def dcSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
    (.const .C) (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
    (.const .D) (.const .C)) .nil)

theorem inst_dupoc_cupod_eq (k : Nat) :
    inst (tauZoo k) .dupoc .cupod = .sys (dcSys k) 0 := rfl

theorem dcSys_get0 (k : Nat) :
    (dcSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.const .C) (.const .D)) := rfl

theorem dcSys_get1 (k : Nat) :
    (dcSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
          (.const .D) (.const .C)) := rfl

/-! ### The cross-implications — the record of WHY Löb cannot close this pair

**Proof-craft note (2026-08-21), the trap this milestone added.** Stating these with
the concrete `cdSys k` inlined makes the elaborator diverge: `.sys defs i` carries
its whole system, so `isDefEq` on the size side-condition unfolds the self-reference
without bound (a 10× heartbeat raise changed nothing — it is non-termination, not
slowness). The fix is to quantify over an ARBITRARY `defs` with the right component
shapes, supplied as `get?` hypotheses. `cdSys` is then only ever passed as an opaque
argument, never unfolded inside a unification.

The two implications `botSysSearchStep` yields for this pair are

    □(component 1 self-plays D) → component 0 plays D     (`sys_cross_D`)
    □(component 0 self-plays C) → component 1 plays C     (`sys_cross_C`)

whose consequents meet the other's antecedent at OPPOSITE ACTIONS, so no cycle
closes and `mutual_pblt_engine_id` has nothing to consume. (Contrast τ(CIMCIC) at
Dupoc, where the actions ALIGN and the mutual engine fires — `TauCIMCIC/Helpers`.)
That negative fact is what leaves the floor in charge here. -/

/-- **Cross-implication 1** (generic): a system whose component `i` is a punish-shaped
    searcher on component `j` gives "□(j self-plays D) → i plays D". -/
theorem sys_cross_D (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k
              (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) Action.D)
              (.const .D) (.const .C)))
    (hK : (Formula.impl (.box k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) Action.D))
            (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) Action.D))
                (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D)) := by
  have h := Pf.botSysSearchStep defs i k
    (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) Action.D) .D .C
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_botSelfIdx] using hK)
  rw [sysClose_subst_botSelfIdx] at h
  exact h

/-- **Cross-implication 2** (generic): a reward-shaped searcher gives
    "□(j self-plays C) → i plays C". -/
theorem sys_cross_C (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k
              (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) Action.C)
              (.const .C) (.const .D)))
    (hK : (Formula.impl (.box k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) Action.C))
            (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) Action.C))
                (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)) := by
  have h := Pf.botSysSearchStep defs i k
    (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) Action.C) .C .D
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_botSelfIdx] using hK)
  rw [sysClose_subst_botSelfIdx] at h
  exact h

/-! ### The closure: all four entangled facts, by the floor -/

/-- δ_L's `.cupod` bit: `probe (inst .cupod .dupoc)` is FALSE at every budget ≤ k —
    the probed head component is the PUNISHER (then-action D ≠ C). Was the δ_L
    column's `hcupodDupoc` hypothesis. -/
theorem ps_probe_inst_cupod_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .cupod .dupoc)) = false := by
  rw [show probe (inst (tauZoo k) .cupod .dupoc)
        = .plays (.bot (.sys (cdSys k) 0)) (.bot (.sys (cdSys k) 0)) Action.C
      from by rw [probe, inst_cupod_dupoc_eq]]
  exact ps_botSys_mismatch_false hK (cdSys k) 0 k _ .D .C _ (by decide)
    (Nat.le_refl k) (cdSys_get0 k) _

/-- δ_Cu's `.dupoc` bit: `probeD (inst .dupoc .cupod)` is FALSE — the probed head
    component is the TRUSTER (then-action C ≠ D). Was the `hdc` hypothesis. -/
theorem ps_probeD_inst_dupoc_cupod_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .dupoc .cupod)) = false := by
  rw [show probeD (inst (tauZoo k) .dupoc .cupod)
        = .plays (.bot (.sys (dcSys k) 0)) (.bot (.sys (dcSys k) 0)) Action.D
      from by rw [probeD, inst_dupoc_cupod_eq]]
  exact ps_botSys_mismatch_false hK (dcSys k) 0 k _ .C .D _ (by decide)
    (Nat.le_refl k) (dcSys_get0 k) _

/-- **τ(Cupod) at Dupoc TRUSTS**: its punish-guard aims D at the trusting Dupoc
    component — floor-false — so the else-constant C runs. Was `hcdP`. -/
theorem cupod_dupoc_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dupoc))
      (.bot (inst (tauZoo k) .cupod .dupoc)) (inst (tauZoo k) .cupod .dupoc)
      = some Action.C := by
  rw [inst_cupod_dupoc_eq]
  refine sysSearcher_plays_else _ _ (cdSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_botSys_mismatch_false (Nat.le_refl k) (cdSys k) 1 k _ .C .D _ (by decide)
    (Nat.le_refl k) (cdSys_get1 k) _

/-- **τ(Dupoc) at Cupod DEFECTS**: its trust-guard aims C at the punishing Cupod
    component — floor-false — so the else-constant D runs. The tau image of the red
    cell's D. -/
theorem dupoc_cupod_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cupod))
      (.bot (inst (tauZoo k) .dupoc .cupod)) (inst (tauZoo k) .dupoc .cupod)
      = some Action.D := by
  rw [inst_dupoc_cupod_eq]
  refine sysSearcher_plays_else _ _ (dcSys_get0 k) ?_
  rw [sysClose_subst_botSelfIdx]
  exact ps_botSys_mismatch_false (Nat.le_refl k) (dcSys k) 1 k _ .D .C _ (by decide)
    (Nat.le_refl k) (dcSys_get1 k) _

/-- τ(Cupod)'s TRUST is floor-priced: it reaches C through a FAILED punish-search,
    so the certificate pays `search_f` and no prover can cite it. The third floor bot
    of the zoo (after Guardian and CupodTroll), and by the same mechanism — trust by
    default is structurally uncitable. -/
theorem ps_probe_inst_cupod_coop_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .cupod .coop)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .cupod .coop)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k (probeD (.const .C)) .D .C (.const .C)
        (by decide) (Nat.le_refl k) (.bot (inst (tauZoo k) .cupod .coop))
        K _ ((proofSearch_spec _ _).1 h) hK
        (by simp only [probe, inst_cupod_peel_coop k, TailTo_plays]; rfl)

/-! ## Transcript certificates for Cupod's two constant cells

The `probeD` side of OBot's watch needs `PlaysProof` TERMS (not merely plays), so
these restate the two constant-hypothesis results as transcripts with explicit
costs. -/

/-- Cupod TRUSTS the cooperator, with a transcript: its punish-search fails
    (`search_f` citing the refutation) and the else-constant runs. -/
theorem pp_cupod_coop_C {k m : Nat}
    (hneg : Pf m (.neg (probeD (.const .C)))) :
    PlaysProof (.bot (inst (tauZoo k) .cupod .coop))
      (.bot (inst (tauZoo k) .cupod .coop)) (inst (tauZoo k) .cupod .coop)
      Action.C (c_leaf + m + k + c_node) := by
  rw [inst_cupod_peel_coop k]
  exact PlaysProof.search_f hneg PlaysProof.const

/-- Cupod PUNISHES the defector, with a transcript: `search_t` citing the trivial
    defection atom. -/
theorem pp_cupod_defect_D {k : Nat} (hk : 2 ≤ k) :
    PlaysProof (.bot (inst (tauZoo k) .cupod .defect))
      (.bot (inst (tauZoo k) .cupod .defect)) (inst (tauZoo k) .cupod .defect)
      Action.D (c_leaf + c_guard k + c_node) := by
  rw [inst_cupod_peel_defect k]
  exact PlaysProof.search_t (pf_probeD_constD hk) PlaysProof.const

/-! ## The τ̂ structure of the pair — kept for the record

The two orientations' systems are literal τ̂-images of each other, exactly as
`DupocBot`/`CupodBot` are in the base library. The base red-cell TRANSPORT argument
still does not transfer (τ̂ maps the system to a DIFFERENT system — the cell in the
other order — so `eval_det`'s "same program, two actions" move has no analogue);
the closure above goes through the floor instead, and gets the SAME values the
base cell has. -/

/-- τ̂ maps the `.cupod .dupoc` system to the `.dupoc .cupod` one: the pair is one
    object seen from two sides. -/
theorem cdSys_transpose (k : Nat) : (cdSys k).transpose = dcSys k := by
  simp [cdSys, dcSys, ProgList.transpose, Prog.transpose, Formula.transpose,
    Action.swap]

/-- The transposed system IS the cell in the other order. -/
theorem inst_dupoc_cupod_transpose (k : Nat) :
    inst (tauZoo k) .dupoc .cupod = .sys ((cdSys k).transpose) 0 := by
  rw [inst_dupoc_cupod_eq, cdSys_transpose]

/-! ## OBot's cell at Cupod — an EMBEDDED floor, `probeD` side

τ(OBot) at Cupod truly DEFECTS: its first watch sees Cupod trust the cooperator and
falls through, its second sees Cupod punish the defector and fires. But certifying
that defection means certifying the FALL — i.e. that Cupod trusts, which is itself
floor-priced (`ps_probe_inst_cupod_coop_false`, the `search_f` route). So the
defection is real and uncitable: the embedded-floor phenomenon of
`no_provable_botRunCascade_C`, one level up and on the `probeD` side.

**The kernel caught this.** The bit table first had this cell `true`, with a
positive `ite_f`/`ite_t` transcript; the cost goal came out as
`c_leaf + k + k + c_node + … ≤ k`, unsatisfiable because `search_f` charges the
failed budget TWICE over — once in the refutation, once as the floor. Two `k`s on
the left of `≤ k` is the signature of an embedded floor. -/

/-- The census: no proof of ≤ k characters says a `.bot`-frozen two-watch cascade
    DEFECTS, when its first watch tests a frozen budget-`kb` searcher whose
    then-action is the fire-action. Firing watch 1 gives `.D` directly (`ite_t`) —
    but only by certifying the watched searcher plays `.D`, i.e. its THEN-branch,
    which needs the guard PROVED; falling through (`ite_f`) needs it to play
    something else, and the searcher's else-play is `search_f`-floored at `kb ≥ k`.
    Either way the budget is blown. -/
theorem no_provable_botTwoWatchD (k kb : Nat) (hk : k ≤ kb) (g : Formula)
    (hgfalse : ¬ (g.subst (.bot (.search kb g (.const .D) (.const .C)))
                          (.bot (.search kb g (.const .D) (.const .C)))).interp)
    (cont : Prog) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.bot (.ite
        (.sim (.bot (.search kb g (.const .D) (.const .C)))
              (.bot (.search kb g (.const .D) (.const .C))))
        Action.D (.const .D) cont)) O .D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (.bot (.ite
      (.sim (.bot (.search kb g (.const .D) (.const .C)))
            (.bot (.search kb g (.const .D) (.const .C))))
      Action.D (.const .D) cont)) O .D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | bot hin =>
        cases hin with
        | ite_t hg hbeq hbr =>
            -- watch 1 FIRED: its guard says the searcher plays `.D` = its THEN
            -- branch, so `search_t` must have proved `g`… but `search_f` is the
            -- only other route and it pays the floor.
            cases hg with
            | sim hin2 =>
                cases hin2 with
                | bot hin3 =>
                    cases hin3 with
                    | search_t hProv hbr2 =>
                        -- watch 1 fires only if the searcher plays its THEN action,
                        -- which `search_t` gets by PROVING the guard — but the guard
                        -- is false, and `S` is sound
                        exact hgfalse (Pf_sound _ _ hProv)
                    | search_f hneg hbr2 => simp only [c_node] at hn; omega
        | ite_f hg hbeq hbr =>
            cases hg with
            | sim hin2 =>
                cases hin2 with
                | bot hin3 =>
                    cases hin3 with
                    | search_t hProv hbr2 => cases hbr2; exact absurd hbeq (by decide)
                    | search_f hneg hbr2 => simp only [c_node] at hn; omega
  · intro me oppo c hS g' ψ b hme
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · intro me oppo c hS p' q' hme
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · intro me oppo c hS p' q' hme
    injection hS with h1 h2 h3
    subst h1
    simp only [Prog.bot.injEq] at hme
    simp at hme
  · intro me oppo c hS g' ψ b hme
    injection hS with h1 h2 h3
    subst h1
    simp only [Prog.bot.injEq] at hme
    simp at hme
  · intro z a' g' ψ c0 c1 q' oppo hS
    injection hS with h1 h2 h3
    simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q' hme
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1
    cases L with
    | nil => simp [searchPlug] at hme
    | cons hd tl => obtain ⟨g', ψ, e⟩ := hd; simp [searchPlug] at hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1
    cases hd with
    | searchL g' ψ' e' => simp [ctxPlug] at hme
    | iteL z' aT' other' => simp [ctxPlug] at hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1
    cases hd <;> simp [plug2] at hme
  · intro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · -- hbotsyssim: the `.sys` RUN twin, same shape kill
    intro me oppo c hS defs i _ hme _
    injection hS with h1 h2 h3
    subst h1; simp at hme

/-- τ(OBot)'s defection against Cupod is unprovable at every budget ≤ k: any
    certificate crosses the floor-priced trust of Cupod's first watch. -/
theorem ps_probeD_obotCupod_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probeD (inst (tauZoo k) .obot .cupod)) = false := by
  cases h : proofSearch K (probeD (inst (tauZoo k) .obot .cupod)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botTwoWatchD k k (Nat.le_refl k) (probeD (.const .C))
        (by
          simp only [probeD, Formula.subst, Prog.subst]
          exact interp_probeD_false_of_plays_C ⟨1, rfl⟩)
        (.ite (.sim (.bot (inst (tauZoo k) .cupod .defect))
                    (.bot (inst (tauZoo k) .cupod .defect))) Action.D (.const .D) (.const .C))
        (.bot (inst (tauZoo k) .obot .cupod))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

/-! ### History: how this cell closed (2026-08-21)

Three routes were tried, in order:

1. **Mutual bounded Löb** — fails structurally: the two cross-implications meet at
   OPPOSITE actions (see the cross-implication record above), so no cycle closes.
   This is a real asymmetry with τ(CIMCIC)-at-Dupoc, where the actions align and
   `mutual_pblt_engine_id` fires.
2. **The base red-cell τ-transport** — fails structurally: in the base, the two
   guards live on two SEPARATE programs that name each other, so a transported
   proof lands on the SAME program and `eval_det` closes; in tau the binder makes
   the pair ONE object and τ̂ maps it to the OTHER orientation's system
   (`cdSys_transpose`), so there is no "same program, two actions" contradiction.
3. **The `search_f` floor** — SUCCEEDS, and is this file's closure: precisely
   BECAUSE route 1's actions mismatch, neither guard can be concluded by
   `search_t` (then-action ≠ target), and every remaining route prices in the
   partner's failed search at full budget. Both bits are provably FALSE
   (`ps_botSys_mismatch_false`), both components play their defaults, and the tau
   cell equals the base red cell `(D, C)` — Def 3 ≡ Def 4 holds on the entangled
   pair as a THEOREM.

The Löb-wall finding and the floor closure are two faces of one fact: an
anti-aligned 2-cycle is not bistable in `S` — the cost floor forbids the
self-fulfilling branch that would make it so. -/

end PD.Tau