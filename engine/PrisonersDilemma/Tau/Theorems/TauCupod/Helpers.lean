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

/-! ## THE ENTANGLED CELL — the 2-cycle, closed by MUTUAL bounded Löb

`inst .cupod .dupoc` is the 2-member system: component 0 (Cupod-seeing-Dupoc) fires
on proving component 1 DEFECTS; component 1 (Dupoc-seeing-Cupod) fires on proving
component 0 COOPERATES. Neither bit is settled by any column fact — this is a
genuine MUTUAL fixpoint, the first in the tau layer, and the reason the whole `.sys`
milestone exists.

The two cross-implications come from `Pf.botSysSearchStep`, which reads one
component through `sysClose` and concludes about its partner. `sysClose` sends
component 0's guard `.plays (.selfIdx 1) (.selfIdx 1) .D` to
`.plays (.sys defs 1) (.sys defs 1) .D` — literally "the partner defects" — so the
rule's conclusion is exactly the shape `mutual_pblt_engine_id` consumes. -/

/-- The pair's system, named once. -/
def cdSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.selfIdx 1) (.selfIdx 1) Action.D) (.const .D) (.const .C))
  (.cons (.search k (.plays (.selfIdx 0) (.selfIdx 0) Action.C) (.const .C) (.const .D)) .nil)

theorem inst_cupod_dupoc_eq (k : Nat) :
    inst (tauZoo k) .cupod .dupoc = .sys (cdSys k) 0 := rfl

theorem cdSys_get0 (k : Nat) :
    (cdSys k).get? 0
      = some (.search k (.plays (.selfIdx 1) (.selfIdx 1) Action.D) (.const .D) (.const .C)) :=
  rfl

theorem cdSys_get1 (k : Nat) :
    (cdSys k).get? 1
      = some (.search k (.plays (.selfIdx 0) (.selfIdx 0) Action.C) (.const .C) (.const .D)) :=
  rfl

/-! ### The cross-implications, stated GENERICALLY in the system

**Proof-craft note (2026-08-21), the trap this milestone added.** Stating these with
the concrete `cdSys k` inlined makes the elaborator diverge: `.sys defs i` carries
its whole system, so `isDefEq` on the size side-condition unfolds the self-reference
without bound (a 10× heartbeat raise changed nothing — it is non-termination, not
slowness). The fix is to quantify over an ARBITRARY `defs` with the right component
shapes, supplied as `get?` hypotheses. `cdSys` is then only ever passed as an opaque
argument, never unfolded inside a unification. -/

/-- The closed form of a system component's self-referential guard: `sysClose` sends
    `.selfIdx j` to `.sys defs j`, and `subst` cannot touch a `.bot`-frozen system. -/
theorem sysClose_subst_selfIdx (defs : ProgList) (j : Nat) (a : Action) (me o : Prog) :
    ((Formula.plays (.selfIdx j) (.selfIdx j) a).sysClose defs).subst me o
      = .plays (.sys defs j) (.sys defs j) a := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]

/-- **Cross-implication 1** (generic): a system whose component `i` is a punish-shaped
    searcher on component `j` gives "□(j defects) → i defects". -/
theorem sys_cross_D (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k (.plays (.selfIdx j) (.selfIdx j) Action.D)
              (.const .D) (.const .C)))
    (hK : (Formula.impl (.box k (.plays (.sys defs j) (.sys defs j) Action.D))
            (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.sys defs j) (.sys defs j) Action.D))
                (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D)) := by
  have h := Pf.botSysSearchStep defs i k (.plays (.selfIdx j) (.selfIdx j) Action.D) .D .C
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_selfIdx] using hK)
  rw [sysClose_subst_selfIdx] at h
  exact h

/-- **Cross-implication 2** (generic): a reward-shaped searcher gives
    "□(j cooperates) → i cooperates". -/
theorem sys_cross_C (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k (.plays (.selfIdx j) (.selfIdx j) Action.C)
              (.const .C) (.const .D)))
    (hK : (Formula.impl (.box k (.plays (.sys defs j) (.sys defs j) Action.C))
            (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.sys defs j) (.sys defs j) Action.C))
                (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)) := by
  have h := Pf.botSysSearchStep defs i k (.plays (.selfIdx j) (.selfIdx j) Action.C) .C .D
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_selfIdx] using hK)
  rw [sysClose_subst_selfIdx] at h
  exact h

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

/-! ## THE ENTANGLED CELL, RESOLVED BY τ — the tau image of the red cell

**The 2-cycle is not Löbian**, and that is a real obstruction, not a gap: the two
implications `sys_cross_D`/`sys_cross_C` yield are

    □(component 1 plays D) → component 0 plays D      (Cupod punishes a provable defector)
    □(component 0 plays C) → component 1 plays C      (Dupoc rewards a provable cooperator)

whose consequents meet the other's antecedent at OPPOSITE ACTIONS, so no cycle
closes and `mutual_pblt_engine_id` has nothing to consume. Dupoc's own diagonal is
self-SUPPORTING (hence Löbian); a mixed pair's would have to be self-DEFEATING, and
bounded Löb cannot manufacture one from an anti-monotone loop.

**But the cell is not open** — the base library's red-cell route settles it without
any fixpoint (`Theorems/DupocBot/vs_CupodBot.lean`, Thm 1.14): the two components
are each other's τ̂-transposes, so `Pf.transpose` maps either guard's proof onto the
other AT THE SAME BUDGET. If either were provable, one component would have to play
both `C` and `D`; `eval` determinism refutes that. Both guards fail, both components
take their defaults.

This is exactly why `Pf.transpose` needed its `sysStep` arm (2026-08-20): the
argument uses ONLY soundness and τ-closure — never the constructor list — so it is
robust to any τ-symmetric extension of `S`, and it needed the binder to be inside
that closure. -/

/-- τ̂ maps the pair's system to ITSELF with the two components swapped. -/
theorem cdSys_transpose (k : Nat) :
    (cdSys k).transpose
      = .cons (.search k (.plays (.selfIdx 1) (.selfIdx 1) Action.C) (.const .C) (.const .D))
        (.cons (.search k (.plays (.selfIdx 0) (.selfIdx 0) Action.D)
          (.const .D) (.const .C)) .nil) := by
  simp [cdSys, ProgList.transpose, Prog.transpose, Formula.transpose, Action.swap]

/-- The transposed system IS the cell in the other order: `inst .dupoc .cupod`. So
    the two entangled cells are literal τ-images of each other, exactly as
    `DupocBot`/`CupodBot` are in the base library. -/
theorem inst_dupoc_cupod_transpose (k : Nat) :
    inst (tauZoo k) .dupoc .cupod = .sys ((cdSys k).transpose) 0 := by
  rw [inst_dupoc_sys_cupod k, cdSys_transpose k]

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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
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
  · intro me oppo c hS defs i hme
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

/-! ### Why the base red-cell route does NOT transfer (checked, 2026-08-21)

The base proof (`Theorems/DupocBot/vs_CupodBot.lean`, Thm 1.14) closes the red cell
without any fixpoint, and the ingredients all exist here: the components ARE each
other's τ-images (`cdSys_transpose`), `Pf.transpose` has its `sysStep` arm, and the
transposed system is literally the cell in the other order
(`inst_dupoc_cupod_transpose`). The argument still does not go through, for a
structural reason worth recording.

**Base.** Dupoc and Cupod are two SEPARATE programs, and each guard names the other
directly: `ρ₁ = "Cupod plays C vs Dupoc"`, `ρ₂ = "Dupoc plays D vs Cupod"`, with
`τ̂(ρ₁) = ρ₂`. A proof of `ρ₁` both FIRES Dupoc's search (so Dupoc plays `C`) and
transports to `ρ₂`, whose soundness makes Dupoc play `D`. Both conclusions are about
**the same program**, so `eval_det` refutes them.

**Tau.** The binder makes the pair ONE object, and each component names the other by
INDEX. τ̂ swaps the roles IN PLACE, so it maps the system to a DIFFERENT system —
`cdSys.transpose = inst .dupoc .cupod`, the cell in the other order. Transporting a
proof about `cdSys` component 1 therefore yields a proof about
`cdSys.transpose` component 1, and those are different programs (checked: their
watched indices differ, so `(cdSys k).transpose.get? 0 ≠ (cdSys k).get? 1`). The
base proof's closing move — "same program, two actions" — has no analogue, and
`eval_det` does not apply.

**What would be needed.** Either (a) a τ-argument at the SYSTEM level rather than
the component level — relating `.sys defs i` to `.sys defs.transpose i` as plays of
one object, which the current `Prog.transpose` does not give since it descends into
members; or (b) an entirely different route to the two bits. Both are open. The
cells therefore remain genuinely open, and the phase theorems take them as
hypotheses — the honest state, and the same one the base library lived in before
the τ-transposition was found.
-/

end PD.Tau