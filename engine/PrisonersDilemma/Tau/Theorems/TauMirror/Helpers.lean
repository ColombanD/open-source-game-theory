import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb

/-!
# Tau/Theorems/TauMirror — the forwarder

τ(MirrorBot) is `Spec.sim .self` — literally the lift of base `.sim .opp .self`.
At hypothesis `T` it compiles to a bare `.sim (.bot (inst T .mirror)) (.bot (inst T
.mirror))`: run "the signal I am treating, facing me" and play what it plays. No
test, no fire, no fall-through: a FORWARDER, the zoo's only one (every other
`.sim`-using bot is a classifier that compares the observed play to a fixed
`test` and commits a fixed `fire`).

Until 2026-08-24 the mirror was encoded as a one-stage threshold test
(`if the watch plays C then C else D`). Behaviourally identical on the two-valued
`Action` type; intensionally a different program, and `S` reads programs: a bare
`.sim` is legible via ONE rule in both polarities, while an `.ite` needs a reading
rule per branch. The threshold encoding blocked the mirror×cupod cells (a Löb
fixpoint on DEFECTION, i.e. the else branch) and forced a then-branch-only engine
rule. The forwarder encoding dissolves both: `Pf.botSysSimStep` is action-generic,
and all three entangled mirror pairs close by the SAME single-formula Löb engine.

**Two structural facts.**

1. **The diagonal has NO play.** `inst .mirror .mirror` is `.sim .self .self` —
   base MirrorBot's self-play, proven `none`. It is the only cell in the zoo that
   does not evaluate; the vote reads a missing play as not-cooperating, so
   τ(Mirror) contributes `D` at its own slot — a recorded divergence from base.
2. **Mirror is a SELF-PROBER**, so it entangles with dupoc, cupod, cimcic and
   dimcid. The dupoc, cupod and cimcic pairs are CLOSED below; dimcid's is the
   `TailToA` debt (`TauDIMCID/Helpers`), unrelated to the mirror.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Off-cycle cells — forwarding -/

/-- τ(Mirror) plays what the watched instance plays. The peel is the off-cycle
    forwarder shape. -/
theorem mirror_copies {k : Nat} {T : Tmpl} {a : Action}
    (hpeel : inst (tauZoo k) .mirror T
      = .sim (.bot (inst (tauZoo k) T .mirror)) (.bot (inst (tauZoo k) T .mirror)))
    (h : ∃ N, eval N (.bot (inst (tauZoo k) T .mirror))
      (.bot (inst (tauZoo k) T .mirror)) (inst (tauZoo k) T .mirror) = some a) :
    ∃ N, eval N (.bot (inst (tauZoo k) .mirror T))
      (.bot (inst (tauZoo k) .mirror T)) (inst (tauZoo k) .mirror T) = some a := by
  rw [hpeel]
  exact simFwd_plays _ _ h

/-- At the constant cooperator: the watch plays `C`, so τ(Mirror) cooperates. -/
theorem mirror_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .mirror .coop))
      (.bot (inst (tauZoo k) .mirror .coop)) (inst (tauZoo k) .mirror .coop)
      = some Action.C :=
  mirror_copies (T := .coop) rfl ⟨1, rfl⟩

/-- At the constant defector: the watch plays `D`, so τ(Mirror) defects. -/
theorem mirror_defect_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .mirror .defect))
      (.bot (inst (tauZoo k) .mirror .defect)) (inst (tauZoo k) .mirror .defect)
      = some Action.D :=
  mirror_copies (T := .defect) rfl ⟨1, rfl⟩

/-- If the watched instance has a COOPERATION transcript, τ(Mirror)'s copy is
    provable: `bot ∘ sim ∘ bot` over that transcript. -/
theorem pf_mirror_copies_C {k K : Nat} {T : Tmpl} {m : Nat}
    (hpeel : inst (tauZoo k) .mirror T
      = .sim (.bot (inst (tauZoo k) T .mirror)) (.bot (inst (tauZoo k) T .mirror)))
    (hw : PlaysProof (.bot (inst (tauZoo k) T .mirror))
            (.bot (inst (tauZoo k) T .mirror)) (inst (tauZoo k) T .mirror)
            Action.C m)
    (hK : m + c_node + c_node + c_node ≤ K) :
    Pf K (probe (inst (tauZoo k) .mirror T)) := by
  rw [probe, hpeel]
  exact Pf.atom ⟨PlaysProof.bot (playsProof_simFwd hw), by have := hcn; omega⟩

/-- At the constant cooperator the transcript is the constant's own. -/
theorem ps_probe_mirror_coop {k : Nat} (h10 : 10 ≤ k) :
    proofSearch k (probe (inst (tauZoo k) .mirror .coop)) = true :=
  (proofSearch_spec _ _).2
    (pf_mirror_copies_C (T := .coop) (m := c_leaf) rfl PlaysProof.const
      (by have := hcl; have := hcn; omega))

/-! ## The cell τ(EBot)'s third watch reads

`inst .ebot .mirror` is EBot facing the forwarder. Its first watch sees
`inst .mirror .defect` (the mirror forwards the defector: `D`) and falls; its
second sees `inst .mirror .coop` (`C`) and FIRES. So EBot cooperates with the
mirror — which is what lets EBot's SELF cell agree with base
`outcome_EBot_vs_EBot = (C, C)`. -/

/-- τ(EBot) COOPERATES with τ(Mirror): its reciprocity watch fires. -/
theorem ebot_mirror_plays_C {k : Nat} (hpeel : inst (tauZoo k) .ebot .mirror
      = .ite (.sim (.bot (inst (tauZoo k) .mirror .defect))
                   (.bot (inst (tauZoo k) .mirror .defect)))
          .C (.const .D)
          (.ite (.sim (.bot (inst (tauZoo k) .mirror .coop))
                      (.bot (inst (tauZoo k) .mirror .coop)))
            .C (.const .C)
            (.ite (.sim (.bot (inst (tauZoo k) .mirror .mirror))
                        (.bot (inst (tauZoo k) .mirror .mirror)))
              .C (.const .C) (.const .D)))) :
    ∃ N, eval N (.bot (inst (tauZoo k) .ebot .mirror))
      (.bot (inst (tauZoo k) .ebot .mirror)) (inst (tauZoo k) .ebot .mirror)
      = some Action.C := by
  rw [hpeel]
  exact simWatchC_falls _ _ mirror_defect_plays_D
    (simWatchC_fires _ _ mirror_coop_plays_C)

/-! ## The entangled systems

Six orientations, three pairs. Naming: `mirDupSys`/`dupMirSys` = Mirror×Dupoc in
each order, `mirCupSys`/`cupMirSys` = Mirror×Cupod, `cimMirSys` = CIMCIC×Mirror.
The mirror member is always the bare copy `.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))`
of its partner.

**The two orientations of a pair are DIFFERENT terms** — the component lists are
ordered the other way and `.sys` is intensional (`rfl` fails between them) — so
each Löb construction is run once per orientation.

**All three pairs use the SINGLE-formula engine.** The mirror's leg is an UNBOXED
implication (`Pf.botSysSimStep`: partner plays `a` → mirror plays `a`), so the
mutual engine — which wants both legs boxed — does not fit. Instead the partner's
BOXED leg (`sys_cross_at` / `sys_cross_impl_cim`) is chained AFTER the mirror's by
`implTrans` into `□φ → φ` for the right subject, and `pblt_engine_id_bounded`
finishes: `Pf m φ` with `2m ≤ k`, so the bit re-certifies at budget `k`. -/

/-- `inst .mirror .dupoc`: Mirror at the head, Dupoc probing it. -/
def mirDupSys (k : Nat) : ProgList :=
  .cons (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1)))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
    (.const .C) (.const .D)) .nil)

theorem inst_mirror_dupoc_eq (k : Nat) :
    inst (tauZoo k) .mirror .dupoc = .sys (mirDupSys k) 0 := rfl
theorem mirDupSys_get0 (k : Nat) :
    (mirDupSys k).get? 0 = some (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))) := rfl
theorem mirDupSys_get1 (k : Nat) :
    (mirDupSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.const .C) (.const .D)) := rfl

/-- `inst .dupoc .mirror`: Dupoc at the head. -/
def dupMirSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
    (.const .C) (.const .D))
  (.cons (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) .nil)

theorem inst_dupoc_mirror_eq (k : Nat) :
    inst (tauZoo k) .dupoc .mirror = .sys (dupMirSys k) 0 := rfl
theorem dupMirSys_get0 (k : Nat) :
    (dupMirSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.const .C) (.const .D)) := rfl
theorem dupMirSys_get1 (k : Nat) :
    (dupMirSys k).get? 1 = some (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) := rfl

/-- `inst .mirror .cupod`: Mirror at the head, Cupod punishing it. -/
def mirCupSys (k : Nat) : ProgList :=
  .cons (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1)))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
    (.const .D) (.const .C)) .nil)

theorem inst_mirror_cupod_eq (k : Nat) :
    inst (tauZoo k) .mirror .cupod = .sys (mirCupSys k) 0 := rfl
theorem mirCupSys_get0 (k : Nat) :
    (mirCupSys k).get? 0 = some (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))) := rfl
theorem mirCupSys_get1 (k : Nat) :
    (mirCupSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
          (.const .D) (.const .C)) := rfl

/-- `inst .cupod .mirror`: Cupod at the head. -/
def cupMirSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
    (.const .D) (.const .C))
  (.cons (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) .nil)

theorem inst_cupod_mirror_eq (k : Nat) :
    inst (tauZoo k) .cupod .mirror = .sys (cupMirSys k) 0 := rfl
theorem cupMirSys_get0 (k : Nat) :
    (cupMirSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
          (.const .D) (.const .C)) := rfl
theorem cupMirSys_get1 (k : Nat) :
    (cupMirSys k).get? 1 = some (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) := rfl

/-- `inst .cimcic .mirror`: CIMCIC at the head, the mirror forwarding it. -/
def cimMirSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.C))
    (.const .C) (.const .D))
  (.cons (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) .nil)

theorem inst_cimcic_mirror_eq (k : Nat) :
    inst (tauZoo k) .cimcic .mirror = .sys (cimMirSys k) 0 := rfl
theorem cimMirSys_get0 (k : Nat) :
    (cimMirSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.C))
          (.const .C) (.const .D)) := rfl
theorem cimMirSys_get1 (k : Nat) :
    (cimMirSys k).get? 1 = some (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))) := rfl

/-- The `log`-arithmetic every engine-size obligation below needs. -/
private theorem log_facts (k : Nat) :
    Nat.log2 k ≤ k ∧ Nat.log2 0 = 0 ∧ Nat.log2 1 = 0 :=
  ⟨Nat.log2_le_self k, by decide, by decide⟩

/-! ### Mirror × Dupoc — a Löb fixpoint on COOPERATION -/

/-- Löb subject, mirror at the head: the mirror member cooperates with itself. -/
private def mdAf (k : Nat) : Formula :=
  .plays (.bot (.sys (mirDupSys k) 0)) (.bot (.sys (mirDupSys k) 0)) Action.C
/-- Dupoc's member cooperating with ITSELF — the mirror's watch is the partner's
    SELF-play (the Def-4 consultation convention), so this is the frame. -/
private def mdBf (k : Nat) : Formula :=
  .plays (.bot (.sys (mirDupSys k) 1)) (.bot (.sys (mirDupSys k) 1)) Action.C

/-- `□Af → Af`: dupoc's boxed search reading, then the mirror's unboxed copy. -/
theorem mirDup_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (mdAf k)) (mdBf k)).size
        + (Formula.impl (mdBf k) (mdAf k)).size
        + (Formula.impl (.box k (mdAf k)) (mdAf k)).size)
      (.impl (.box k (mdAf k)) (mdAf k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_cross_at (mirDupSys k) 1 0 k _ (.bot (.sys (mirDupSys k) 1)) .C .D
      (mirDupSys_get1 k) le_rfl)
    (sys_mirror_fwd (mirDupSys k) 0 1 .C _ (.bot (.sys (mirDupSys k) 0))
      (mirDupSys_get0 k) le_rfl)
    le_rfl

theorem mirDup_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (mdAf k) := by
  refine pblt_engine_id_bounded mdAf
    (fun k => (Formula.impl (.box k (mdAf k)) (mdBf k)).size
            + (Formula.impl (mdBf k) (mdAf k)).size
            + (Formula.impl (.box k (mdAf k)) (mdAf k)).size) 0 ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [mdAf, Formula.size, Prog.size, ProgList.psize, mirDupSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [mdAf, mdBf, Formula.size, Prog.size, ProgList.psize, mirDupSys, numCost]; omega
  · intro k _; exact mirDup_loeb_premise k

/-- **τ(Mirror) at Dupoc COOPERATES** (Löb-gated). -/
theorem mirror_dupoc_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .mirror .dupoc))
        (.bot (inst (tauZoo k) .mirror .dupoc)) (inst (tauZoo k) .mirror .dupoc)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := mirDup_loeb
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, -, hm⟩ := hLb k hk
  rw [inst_mirror_dupoc_eq k]
  exact entry_of_interp (Pf_sound m _ hm)

/-- **The `hmir` gate**: `probe (inst .mirror .dupoc)` is PROVABLE at budget `k`
    past a threshold — the Löb bit IS the probe, and the bounded engine puts it
    under `k/2`. -/
theorem ps_probe_mirror_dupoc :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probe (inst (tauZoo k) .mirror .dupoc)) = true := by
  obtain ⟨kL, hLb⟩ := mirDup_loeb
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k hk
  show proofSearch k (mdAf k) = true
  exact (proofSearch_spec _ _).2 (Pf_mono hm (by omega))

/-- Löb subject, dupoc at the head: the mirror member (index 1) cooperates with itself. -/
private def dmAf (k : Nat) : Formula :=
  .plays (.bot (.sys (dupMirSys k) 1)) (.bot (.sys (dupMirSys k) 1)) Action.C
private def dmBf (k : Nat) : Formula :=
  .plays (.bot (.sys (dupMirSys k) 0)) (.bot (.sys (dupMirSys k) 0)) Action.C

theorem dupMir_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (dmAf k)) (dmBf k)).size
        + (Formula.impl (dmBf k) (dmAf k)).size
        + (Formula.impl (.box k (dmAf k)) (dmAf k)).size)
      (.impl (.box k (dmAf k)) (dmAf k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_cross_at (dupMirSys k) 0 1 k _ (.bot (.sys (dupMirSys k) 0)) .C .D
      (dupMirSys_get0 k) le_rfl)
    (sys_mirror_fwd (dupMirSys k) 1 0 .C _ (.bot (.sys (dupMirSys k) 1))
      (dupMirSys_get1 k) le_rfl)
    le_rfl

theorem dupMir_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (dmAf k) := by
  refine pblt_engine_id_bounded dmAf
    (fun k => (Formula.impl (.box k (dmAf k)) (dmBf k)).size
            + (Formula.impl (dmBf k) (dmAf k)).size
            + (Formula.impl (.box k (dmAf k)) (dmAf k)).size) 0 ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [dmAf, Formula.size, Prog.size, ProgList.psize, dupMirSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [dmAf, dmBf, Formula.size, Prog.size, ProgList.psize, dupMirSys, numCost]; omega
  · intro k _; exact dupMir_loeb_premise k

/-- A searcher component at the head FIRES once its guard is provable at `k`:
    `search_t` cites the guard at `c_guard k` (a pointer, not the transcript), and
    the play is the then-constant. Generic in the polarity. -/
theorem sysSearcher_head_plays {defs : ProgList} {k i : Nat} {aT aE : Action}
    (hget : defs.get? 0 = some (.search k
      (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) aT) (.const aT) (.const aE)))
    (hcg : c_leaf + c_guard k + c_node + c_node + c_node ≤ k)
    (hAf : Pf k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) aT)) :
    ∃ N, eval N (.bot (.sys defs 0)) (.bot (.sys defs 0)) (.sys defs 0) = some aT := by
  have hpre : Pf k (((Formula.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) aT).sysClose defs).subst
      (.bot (.sys defs 0)) (.bot (.sys defs 0))) := by
    rw [sysClose_subst_botSelfIdx]; exact hAf
  have h1 := PlaysProof.search_t (q := .const aE) hpre
    (PlaysProof.const (me := .bot (.sys defs 0)) (opponent := .bot (.sys defs 0)) (a := aT))
  have hbody : PlaysProof (.bot (.sys defs 0)) (.bot (.sys defs 0)) (.sys defs 0) aT
      (c_leaf + c_guard k + c_node + c_node) :=
    PlaysProof.sysStep hget (by simp only [Prog.sysClose]; exact h1)
  exact entry_of_interp (Pf_sound (c_leaf + c_guard k + c_node + c_node + c_node) _
    (Pf.atom ⟨PlaysProof.bot hbody, by omega⟩))

/-- The `c_guard` headroom every head-fires cell needs, past a threshold. -/
private theorem cg_headroom : ∃ kC, ∀ k, kC ≤ k → c_leaf + c_guard k + c_node + c_node + c_node ≤ k := by
  obtain ⟨kC, hkC⟩ := linear_log2_add_le 200 4000
  refine ⟨kC, fun k hk => ?_⟩
  have := hkC k hk; have := hcl; have := hcn
  simp only [c_guard, numCost]; omega

/-- **The `hmirP` gate**: τ(Dupoc) COOPERATES with τ(Mirror) — its searcher's
    guard is the mirror member's self-cooperation, which Löb certifies. -/
theorem dupoc_mirror_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
        (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := dupMir_loeb
  obtain ⟨kC, hkC⟩ := cg_headroom
  refine ⟨max kL kC, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  rw [inst_dupoc_mirror_eq k]
  exact sysSearcher_head_plays (dupMirSys_get0 k)
    (hkC k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk)))
    (Pf_mono hm (by omega))

/-! ### Mirror × Cupod — a Löb fixpoint on DEFECTION

Cupod probes for `D` and the forwarder plays whatever cupod plays, so the pair is
ALIGNED ON `D`: cupod defects iff it can prove the mirror defects, and the mirror
defects iff cupod does. The SAME two lemmas as the dupoc pair, at the other
polarity — which is exactly what the forwarder encoding bought. Base analogue:
`outcome_CupodBot_vs_MirrorBot = (D, D)`. -/

private def mcAf (k : Nat) : Formula :=
  .plays (.bot (.sys (mirCupSys k) 0)) (.bot (.sys (mirCupSys k) 0)) Action.D
private def mcBf (k : Nat) : Formula :=
  .plays (.bot (.sys (mirCupSys k) 1)) (.bot (.sys (mirCupSys k) 1)) Action.D

theorem mirCup_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (mcAf k)) (mcBf k)).size
        + (Formula.impl (mcBf k) (mcAf k)).size
        + (Formula.impl (.box k (mcAf k)) (mcAf k)).size)
      (.impl (.box k (mcAf k)) (mcAf k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_cross_at (mirCupSys k) 1 0 k _ (.bot (.sys (mirCupSys k) 1)) .D .C
      (mirCupSys_get1 k) le_rfl)
    (sys_mirror_fwd (mirCupSys k) 0 1 .D _ (.bot (.sys (mirCupSys k) 0))
      (mirCupSys_get0 k) le_rfl)
    le_rfl

theorem mirCup_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (mcAf k) := by
  refine pblt_engine_id_bounded mcAf
    (fun k => (Formula.impl (.box k (mcAf k)) (mcBf k)).size
            + (Formula.impl (mcBf k) (mcAf k)).size
            + (Formula.impl (.box k (mcAf k)) (mcAf k)).size) 0 ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [mcAf, Formula.size, Prog.size, ProgList.psize, mirCupSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [mcAf, mcBf, Formula.size, Prog.size, ProgList.psize, mirCupSys, numCost]; omega
  · intro k _; exact mirCup_loeb_premise k

/-- **τ(Mirror) at Cupod DEFECTS** (Löb-gated). -/
theorem mirror_cupod_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .mirror .cupod))
        (.bot (inst (tauZoo k) .mirror .cupod)) (inst (tauZoo k) .mirror .cupod)
        = some Action.D := by
  obtain ⟨kL, hLb⟩ := mirCup_loeb
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, -, hm⟩ := hLb k hk
  rw [inst_mirror_cupod_eq k]
  exact entry_of_interp (Pf_sound m _ hm)

/-- **The `hmirCu` gate**: `probeD (inst .mirror .cupod)` is PROVABLE at `k`. -/
theorem ps_probeD_mirror_cupod :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probeD (inst (tauZoo k) .mirror .cupod)) = true := by
  obtain ⟨kL, hLb⟩ := mirCup_loeb
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k hk
  show proofSearch k (mcAf k) = true
  exact (proofSearch_spec _ _).2 (Pf_mono hm (by omega))

private def cmAf (k : Nat) : Formula :=
  .plays (.bot (.sys (cupMirSys k) 1)) (.bot (.sys (cupMirSys k) 1)) Action.D
private def cmBf (k : Nat) : Formula :=
  .plays (.bot (.sys (cupMirSys k) 0)) (.bot (.sys (cupMirSys k) 0)) Action.D

theorem cupMir_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (cmAf k)) (cmBf k)).size
        + (Formula.impl (cmBf k) (cmAf k)).size
        + (Formula.impl (.box k (cmAf k)) (cmAf k)).size)
      (.impl (.box k (cmAf k)) (cmAf k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_cross_at (cupMirSys k) 0 1 k _ (.bot (.sys (cupMirSys k) 0)) .D .C
      (cupMirSys_get0 k) le_rfl)
    (sys_mirror_fwd (cupMirSys k) 1 0 .D _ (.bot (.sys (cupMirSys k) 1))
      (cupMirSys_get1 k) le_rfl)
    le_rfl

theorem cupMir_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (cmAf k) := by
  refine pblt_engine_id_bounded cmAf
    (fun k => (Formula.impl (.box k (cmAf k)) (cmBf k)).size
            + (Formula.impl (cmBf k) (cmAf k)).size
            + (Formula.impl (.box k (cmAf k)) (cmAf k)).size) 0 ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [cmAf, Formula.size, Prog.size, ProgList.psize, cupMirSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [cmAf, cmBf, Formula.size, Prog.size, ProgList.psize, cupMirSys, numCost]; omega
  · intro k _; exact cupMir_loeb_premise k

/-- **The `hmirCuP` gate**: τ(Cupod) DEFECTS against τ(Mirror) — its punish-search
    fires on the mirror member's certified self-defection. -/
theorem cupod_mirror_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .cupod .mirror))
        (.bot (inst (tauZoo k) .cupod .mirror)) (inst (tauZoo k) .cupod .mirror)
        = some Action.D := by
  obtain ⟨kL, hLb⟩ := cupMir_loeb
  obtain ⟨kC, hkC⟩ := cg_headroom
  refine ⟨max kL kC, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  rw [inst_cupod_mirror_eq k]
  exact sysSearcher_head_plays (cupMirSys_get0 k)
    (hkC k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk)))
    (Pf_mono hm (by omega))

/-! ### CIMCIC × Mirror — Löb on the GUARD itself

Base `llm_outcome_CIMCIC_vs_MirrorBot` gets CIMCIC's guard
`(I play C vs them) → (they play C vs me)` in ONE step: base MirrorBot sims `.opp`
against `.self` — the opponent facing ME, i.e. exactly the guard's antecedent frame
— so `simStep` IS the guard. The tau layer consults an instance by its SELF-play
(`.sim (.bot P) (.bot P)`, the Def-4 convention), so the forwarder's premise is
CIMCIC's self-play, not the cross frame the antecedent names. Semantically the
same play (the components are `.opp`-free, so frame-independent); syntactically
not, and `S` has no frame-transfer rule. The repair costs one Löb pass: the guard
`G` follows from its CONSEQUENT by `implK`, the consequent from CIMCIC's self-play
by the forwarder, and CIMCIC's self-play from `□G` by its own search reading —
so `□G → G`, and the engine certifies `G`. -/

/-- The closed guard of the CIMCIC member. -/
private def cmG (k : Nat) : Formula :=
  .impl (.plays (.bot (.sys (cimMirSys k) 0)) (.bot (.sys (cimMirSys k) 1)) Action.C)
        (.plays (.bot (.sys (cimMirSys k) 1)) (.bot (.sys (cimMirSys k) 0)) Action.C)
/-- CIMCIC's self-cooperation in the system. -/
private def cmA (k : Nat) : Formula :=
  .plays (.bot (.sys (cimMirSys k) 0)) (.bot (.sys (cimMirSys k) 0)) Action.C
/-- The guard's consequent: the mirror cooperates with CIMCIC. -/
private def cmC (k : Nat) : Formula :=
  .plays (.bot (.sys (cimMirSys k) 1)) (.bot (.sys (cimMirSys k) 0)) Action.C

/-- `□G → G`. -/
theorem cimMir_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (cmG k)) (cmA k)).size
        + ((Formula.impl (cmA k) (cmC k)).size
           + (Formula.impl (cmC k) (cmG k)).size
           + (Formula.impl (cmA k) (cmG k)).size)
        + (Formula.impl (.box k (cmG k)) (cmG k)).size)
      (.impl (.box k (cmG k)) (cmG k)) :=
  Pf.implTrans _ _ _ _ _
    -- □G → A : CIMCIC's own search reading, in the self frame
    (sys_cross_impl_cim (cimMirSys k) 0 1 k _ (cimMirSys_get0 k) le_rfl)
    -- A → G : forwarder (A → C), then `implK` (C → (ant → C) = G)
    (Pf.implTrans _ _ _ _ _
      (sys_mirror_fwd (cimMirSys k) 1 0 .C _ (.bot (.sys (cimMirSys k) 0))
        (cimMirSys_get1 k) le_rfl)
      (Pf.implK (cmC k)
        (.plays (.bot (.sys (cimMirSys k) 0)) (.bot (.sys (cimMirSys k) 1)) Action.C)
        le_rfl)
      le_rfl)
    le_rfl

theorem cimMir_loeb : ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (cmG k) := by
  refine pblt_engine_id_bounded cmG
    (fun k => (Formula.impl (.box k (cmG k)) (cmA k)).size
        + ((Formula.impl (cmA k) (cmC k)).size
           + (Formula.impl (cmC k) (cmG k)).size
           + (Formula.impl (cmA k) (cmG k)).size)
        + (Formula.impl (.box k (cmG k)) (cmG k)).size) 0 ?_ ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [cmG, Formula.size, Prog.size, ProgList.psize, cimMirSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts k
    simp only [cmG, cmA, cmC, Formula.size, Prog.size, ProgList.psize, cimMirSys, numCost]
    omega
  · intro k _; exact cimMir_loeb_premise k

/-- **The `hmirC` gate**: τ(CIMCIC) COOPERATES with τ(Mirror) — its guard is
    Löb-certified at `k`, so the search fires. -/
theorem cimcic_mirror_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .mirror))
        (.bot (inst (tauZoo k) .cimcic .mirror)) (inst (tauZoo k) .cimcic .mirror)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := cimMir_loeb
  obtain ⟨kC, hkC⟩ := cg_headroom
  refine ⟨max kL kC, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hcg := hkC k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  rw [inst_cimcic_mirror_eq k]
  have hpre : Pf k (((Formula.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
      (.plays (.bot (.selfIdx 1)) .self Action.C)).sysClose (cimMirSys k)).subst
      (.bot (.sys (cimMirSys k) 0)) (.bot (.sys (cimMirSys k) 0))) := by
    rw [sysClose_subst_cimSelfIdx]; exact Pf_mono hm (by omega)
  have h1 := PlaysProof.search_t (q := .const .D) hpre
    (PlaysProof.const (me := .bot (.sys (cimMirSys k) 0))
      (opponent := .bot (.sys (cimMirSys k) 0)) (a := Action.C))
  have hbody : PlaysProof (.bot (.sys (cimMirSys k) 0)) (.bot (.sys (cimMirSys k) 0))
      (.sys (cimMirSys k) 0) Action.C (c_leaf + c_guard k + c_node + c_node) :=
    PlaysProof.sysStep (cimMirSys_get0 k) (by simp only [Prog.sysClose]; exact h1)
  exact entry_of_interp (Pf_sound (c_leaf + c_guard k + c_node + c_node + c_node) _
    (Pf.atom ⟨PlaysProof.bot hbody, by omega⟩))

/-! ## What is NOT proven here, and why

**τ(Mirror)'s own `VoteBits` row is UNSTATEABLE.** `VoteBits.cons` demands a play
witness for EVERY entry, and the diagonal has none — base MirrorBot's self-play is
proven `none`. Not an effort gap: the roadmap's "a TauBot always terminates" made
concrete. Every OTHER row carries its `.mirror` slot fine.

**The dimcid pair is not the mirror's problem.** `inst .mirror .dimcid` /
`inst .dimcid .mirror` would close by the same forwarder mechanism, but DIMCID's
own row is blocked on the `TailToA` kernel refactor (`TauDIMCID/Helpers`) and no
statement currently needs those two cells. -/

end PD.Tau
