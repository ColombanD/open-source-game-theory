import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb

/-!
# Tau/Theorems/TauMirror — the pure copier

τ(MirrorBot) is one `run` stage on the SELF target: at hypothesis `T` it watches
`inst T .mirror` — "the signal I am treating, facing me" — and COPIES its play.
`simCopy_plays` is already action-generic over exactly this shape, so every
off-cycle cell is a one-liner once the watched instance's play is known.

**Two structural facts worth stating up front.**

1. **The diagonal has NO play.** `inst .mirror .mirror` compiles to
   `.ite (.sim .self .self) …`, i.e. base MirrorBot's self-play, whose `outcome`
   is proven `none`. It is the only cell in the zoo that does not evaluate, and
   the vote reads a missing play as not-cooperating (`tau_play` thresholds a
   cooperation mass), so τ(Mirror) contributes `D` at its own slot — a
   deliberate, recorded divergence from the base `none`.

2. **Mirror is a SELF-PROBER**, so it entangles with dupoc, cupod, cimcic and
   dimcid — eight `.sys` orientations. Its stage is a `run` WATCH rather than a
   prove-guard, so the alignment rule that closed the earlier pairs (about what
   `search_t` can conclude) does not apply verbatim; those cells get their own
   treatment below.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(Mirror) copies whatever the watched instance plays — the whole bot, in one
    lemma. The peel is the `.name`-free `run`-stage shape. -/
theorem mirror_copies {k : Nat} {T : Tmpl} {a : Action}
    (hpeel : inst (tauZoo k) .mirror T
      = .ite (.sim (.bot (inst (tauZoo k) T .mirror))
                   (.bot (inst (tauZoo k) T .mirror)))
          Action.C (.const .C) (.const .D))
    (h : ∃ N, eval N (.bot (inst (tauZoo k) T .mirror))
      (.bot (inst (tauZoo k) T .mirror)) (inst (tauZoo k) T .mirror) = some a) :
    ∃ N, eval N (.bot (inst (tauZoo k) .mirror T))
      (.bot (inst (tauZoo k) .mirror T)) (inst (tauZoo k) .mirror T) = some a := by
  rw [hpeel]
  exact simCopy_plays _ _ h

/-- At the constant cooperator: the watch sees `C`, so τ(Mirror) cooperates. -/
theorem mirror_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .mirror .coop))
      (.bot (inst (tauZoo k) .mirror .coop)) (inst (tauZoo k) .mirror .coop)
      = some Action.C :=
  mirror_copies (T := .coop) rfl ⟨1, rfl⟩

/-- At the constant defector: the watch sees `D`, so τ(Mirror) defects. -/
theorem mirror_defect_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .mirror .defect))
      (.bot (inst (tauZoo k) .mirror .defect)) (inst (tauZoo k) .mirror .defect)
      = some Action.D :=
  mirror_copies (T := .defect) rfl ⟨1, rfl⟩

/-! ## Provability of the copy — via `PlaysProof`, not a `Pf` reading rule

`S` has no rule concluding "a run-stage `.ite` over a FROZEN sim plays `a`"
(`iteBranchSearch_t`'s guard is `.sim .opp (.bot z)`, a different shape). It does
not need one: the run stage is an ATOM, and `AtomProvable` is reached by
assembling a `PlaysProof` — `ite_t` over `sim` over `bot` — exactly as
`pf_simCopy_constC` does for τ(TFTSim). Behaviour is certified by transcript, not
by a modal rule.

Cost, once, for the whole family: `bot` + `ite_t` (guard-run + branch + node) +
`sim` + `bot` + the watched instance's own transcript. -/

/-- If the watched instance has a COOPERATION transcript, τ(Mirror)'s copy is
    provable. -/
theorem pf_mirror_copies_C {k K : Nat} {T : Tmpl} {m : Nat}
    (hpeel : inst (tauZoo k) .mirror T
      = .ite (.sim (.bot (inst (tauZoo k) T .mirror))
                   (.bot (inst (tauZoo k) T .mirror)))
          Action.C (.const .C) (.const .D))
    (hw : PlaysProof (.bot (inst (tauZoo k) T .mirror))
            (.bot (inst (tauZoo k) T .mirror)) (inst (tauZoo k) T .mirror)
            Action.C m)
    (hK : m + c_node + c_node + c_leaf + c_node + c_node ≤ K) :
    Pf K (probe (inst (tauZoo k) .mirror T)) := by
  rw [probe, hpeel]
  refine Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot hw)) rfl PlaysProof.const), ?_⟩
  have := hcl; have := hcn; omega

/-- At the constant cooperator the transcript is the constant's own, so the bit
    is provable from a small budget. -/
theorem ps_probe_mirror_coop {k : Nat} (h10 : 10 ≤ k) :
    proofSearch k (probe (inst (tauZoo k) .mirror .coop)) = true := by
  refine (proofSearch_spec _ _).2
    (pf_mirror_copies_C (T := .coop) (m := c_leaf) rfl PlaysProof.const ?_)
  have := hcl; have := hcn; omega

/-! ## The two cells τ(EBot)'s third watch reads

A FULL "what does each hypothesis play against mirror" column is not available:
five of its fifteen cells are entangled (Löb-gated) and the diagonal has no play
at all. τ(EBot) does not need the column — its third watch fires or falls on
specific hypotheses — so those cells are given directly.

`inst .ebot .mirror` is the interesting one: EBot facing the copier. Its own
first watch sees `inst .mirror .defect` (mirror copies the defector: `D`) and
falls; its second sees `inst .mirror .coop` (mirror copies the cooperator: `C`)
and FIRES. So EBot cooperates with the mirror — and that is what makes EBot's
SELF cell flip from `D` to `C`, restoring agreement with base
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

Mirror is a SELF-PROBER, so it entangles with dupoc, cupod, cimcic and dimcid.
Naming: `mdSys`/`dmSys` = Mirror×Dupoc in each order, `mcSys`/`cmSys` =
Mirror×Cupod, `mmcSys` = CIMCIC×Mirror.

The mirror component is an `.ite` over a FROZEN `.sim` of the partner — a RUN
stage, not a prove-guard. Reading it inside the binder is exactly
`Pf.botSysRunStep` (the `.sys` twin of `botSimStep`), added for this: it concludes
`me plays fire` from the PLAYS premise `partner plays test against itself`. That
is the structural difference from every earlier entangled pair, whose components
were searchers reading a BOX. -/

/-- `inst .mirror .dupoc`: Mirror at the head, Dupoc probing it. -/
def mirDupSys (k : Nat) : ProgList :=
  .cons (.ite (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1)))
          Action.C (.const .C) (.const .D))
  (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
    (.const .C) (.const .D)) .nil)

theorem inst_mirror_dupoc_eq (k : Nat) :
    inst (tauZoo k) .mirror .dupoc = .sys (mirDupSys k) 0 := rfl

theorem mirDupSys_get0 (k : Nat) :
    (mirDupSys k).get? 0
      = some (.ite (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1)))
          Action.C (.const .C) (.const .D)) := rfl

theorem mirDupSys_get1 (k : Nat) :
    (mirDupSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.const .C) (.const .D)) := rfl

/-- `inst .dupoc .mirror`: Dupoc at the head. -/
def dupMirSys (k : Nat) : ProgList :=
  .cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
    (.const .C) (.const .D))
  (.cons (.ite (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0)))
          Action.C (.const .C) (.const .D)) .nil)

theorem inst_dupoc_mirror_eq (k : Nat) :
    inst (tauZoo k) .dupoc .mirror = .sys (dupMirSys k) 0 := rfl

theorem dupMirSys_get0 (k : Nat) :
    (dupMirSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.const .C) (.const .D)) := rfl

theorem dupMirSys_get1 (k : Nat) :
    (dupMirSys k).get? 1
      = some (.ite (.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0)))
          Action.C (.const .C) (.const .D)) := rfl

/-! ### The mirror component's reading rule, specialised

`Pf.botSysRunStep` at the mirror shape: from "the partner component plays C
against itself" conclude "the mirror component plays C against anything". -/

/-- The mirror component copies, INSIDE the binder — the `botSysRunStep` instance. -/
theorem sys_mirror_copies_C (defs : ProgList) (i j : Nat) (K : Nat) (opp : Prog)
    (hget : defs.get? i = some (.ite (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j)))
              Action.C (.const .C) (.const .D)))
    (hK : (Formula.impl
        (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) Action.C)
        (.plays (.bot (.sys defs i)) opp Action.C)).size ≤ K) :
    Pf K (.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) Action.C)
                (.plays (.bot (.sys defs i)) opp Action.C)) :=
  Pf.botSysRunStep defs i j Action.C Action.C (.const .D)
    (.bot (.sys defs i)) opp rfl hget hK

/-! ### Mirror × Dupoc — CLOSED COOPERATIVELY BY BOUNDED LÖB

The two legs do NOT have the shape `mutual_pblt_engine_id` wants (it needs BOTH
premises boxed). Mirror's component is a RUN stage: it concludes from the PLAYS
premise "dupoc's component cooperates with itself", not from a box of it — and `S`
has no reflection rule turning `□(plays)` into `plays`, by design.

They compose the other way round. With

    Af k := the mirror component cooperates with itself,

dupoc's searcher gives `□Af → (dupoc plays C)` (`sys_cross_C_at`) and mirror's run
stage gives `(dupoc plays C) → Af` (`sys_mirror_copies_C`). `implTrans` chains them
into `□Af → Af`, which is exactly `pblt_engine_id`'s hypothesis. So this pair needs
only the SINGLE-formula Löb engine — cheaper than every earlier entangled cell. -/

/-- Abbreviation: the mirror component's self-cooperation, the Löb subject. -/
private def mdAf (k : Nat) : Formula :=
  .plays (.bot (.sys (mirDupSys k) 0)) (.bot (.sys (mirDupSys k) 0)) Action.C

/-- Abbreviation: dupoc's component cooperating with ITSELF — the mirror's watch
    is `.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))`, i.e. the SELF-play of the
    partner, so the frame here is the dupoc component, not the mirror one. -/
private def mdBf (k : Nat) : Formula :=
  .plays (.bot (.sys (mirDupSys k) 1)) (.bot (.sys (mirDupSys k) 1)) Action.C

/-- Dupoc's leg: `□Af → Bf`, at the SELF frame. -/
theorem mirDup_leg_dupoc (k K : Nat)
    (hK : (Formula.impl (.box k (mdAf k)) (mdBf k)).size ≤ K) :
    Pf K (.impl (.box k (mdAf k)) (mdBf k)) :=
  sys_cross_C_at (mirDupSys k) 1 0 k K (.bot (.sys (mirDupSys k) 1))
    (mirDupSys_get1 k) hK

/-- Mirror's leg: `Bf → Af`, the run-stage copy. -/
theorem mirDup_leg_mirror (k K : Nat)
    (hK : (Formula.impl (mdBf k) (mdAf k)).size ≤ K) :
    Pf K (.impl (mdBf k) (mdAf k)) :=
  sys_mirror_copies_C (mirDupSys k) 0 1 K (.bot (.sys (mirDupSys k) 0))
    (mirDupSys_get0 k) hK

/-- **The Löb premise**: `□Af → Af`, by chaining dupoc's search reading with
    mirror's copy reading. -/
theorem mirDup_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (mdAf k)) (mdBf k)).size
        + (Formula.impl (mdBf k) (mdAf k)).size
        + (Formula.impl (.box k (mdAf k)) (mdAf k)).size)
      (.impl (.box k (mdAf k)) (mdAf k)) :=
  Pf.implTrans _ _ _ _ _
    (mirDup_leg_dupoc k _ le_rfl) (mirDup_leg_mirror k _ le_rfl) le_rfl

/-- **The fixpoint**: past a threshold, the mirror component's self-cooperation is
    provable. Single-formula `pblt_engine_id`, not the mutual engine. -/
theorem mirDup_loeb :
    ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (mdAf k) := by
  refine pblt_engine_id_bounded mdAf
    (fun k => (Formula.impl (.box k (mdAf k)) (mdBf k)).size
            + (Formula.impl (mdBf k) (mdAf k)).size
            + (Formula.impl (.box k (mdAf k)) (mdAf k)).size) 0 ?_ ?_ ?_
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [mdAf, Formula.size, Prog.size, ProgList.psize, mirDupSys, numCost]
    omega
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [mdAf, mdBf, Formula.size, Prog.size, ProgList.psize, mirDupSys, numCost]
    omega
  · intro k _
    exact mirDup_loeb_premise k

/-- **τ(Mirror) at Dupoc COOPERATES** (Löb-gated) — discharges `hmir`'s content. -/
theorem mirror_dupoc_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .mirror .dupoc))
        (.bot (inst (tauZoo k) .mirror .dupoc)) (inst (tauZoo k) .mirror .dupoc)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := mirDup_loeb
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, -, hm⟩ := hLb k hk
  have hint : (probe (.sys (mirDupSys k) 0)).interp := Pf_sound m _ hm
  rw [inst_mirror_dupoc_eq k]
  exact entry_C_of_interp hint

/-- The dupoc component's OWN transcript, from the Löb bit: `search_t` cites the
    guard at `c_guard k` — a POINTER, not the premise's transcript — so the large
    Löb budget collapses to a `log`-sized citation. -/
theorem ps_dupoc_transcript {k : Nat} (hAf : Pf k (mdAf k)) :
    PlaysProof (.bot (.sys (mirDupSys k) 1)) (.bot (.sys (mirDupSys k) 1))
      (.sys (mirDupSys k) 1) Action.C (c_leaf + c_guard k + c_node + c_node) := by
  have hpre : Pf k (((Formula.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C).sysClose
      (mirDupSys k)).subst (.bot (.sys (mirDupSys k) 1)) (.bot (.sys (mirDupSys k) 1))) := by
    rw [sysClose_subst_botSelfIdx]; exact hAf
  have h1 := PlaysProof.search_t (q := .const .D) hpre
    (PlaysProof.const (me := .bot (.sys (mirDupSys k) 1))
      (opponent := .bot (.sys (mirDupSys k) 1)) (a := Action.C))
  exact PlaysProof.sysStep (mirDupSys_get1 k) (by
    simp only [Prog.sysClose]
    exact h1)

/-- **The `hmir` gate**: `probe (inst .mirror .dupoc)` is PROVABLE past a threshold.
    The mirror's copy transcript wraps the dupoc component's, which the Löb bit
    certifies at budget `k`. -/
theorem pf_probe_mirror_dupoc {k K : Nat} (hAf : Pf k (mdAf k))
    (hK : (c_leaf + c_guard k + c_node + c_node) + c_node
            + c_node + c_leaf + c_node + c_node + c_node ≤ K) :
    Pf K (probe (inst (tauZoo k) .mirror .dupoc)) := by
  rw [probe, inst_mirror_dupoc_eq k]
  -- build the transcript FIRST so its cost index is concrete before `Pf.atom`
  have hbody : PlaysProof (.bot (.sys (mirDupSys k) 0)) (.bot (.sys (mirDupSys k) 0))
      ((Prog.ite (.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1)))
          Action.C (.const .C) (.const .D)).sysClose (mirDupSys k)) Action.C
      ((c_leaf + c_guard k + c_node + c_node) + c_node + c_node + c_leaf + c_node) := by
    simp only [Prog.sysClose]
    exact PlaysProof.ite_t
      (PlaysProof.sim (PlaysProof.bot (ps_dupoc_transcript hAf))) rfl PlaysProof.const
  exact Pf.atom ⟨PlaysProof.bot (PlaysProof.sysStep (mirDupSys_get0 k) hbody),
    by have := hcl; have := hcn; omega⟩

/-- **The `hmir` gate**: `probe (inst .mirror .dupoc)` is PROVABLE past a threshold.

    The Löb bit arrives at the engine's own budget `m = O(log k)`; `Pf_mono` lifts it
    to `k`, and `pf_probe_mirror_dupoc` wraps it in the mirror's copy transcript. The
    threshold absorbs both the engine's and the transcript's `log`-sized costs. -/
theorem ps_probe_mirror_dupoc :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probe (inst (tauZoo k) .mirror .dupoc)) = true := by
  obtain ⟨kL, hLb⟩ := mirDup_loeb
  obtain ⟨kC, hkC⟩ := linear_log2_add_le 200 4000
  refine ⟨max kL kC, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hcg := hkC k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  refine (proofSearch_spec _ _).2 (pf_probe_mirror_dupoc (k := k) ?_ ?_)
  · exact Pf_mono hm (by omega)
  · have := hcl; have := hcn
    simp only [c_guard, numCost]
    have hlog := Nat.log2_le_self k
    omega

/-! ### The DUPOC-at-the-head orientation

`inst .dupoc .mirror` is `dupMirSys 0`, a DIFFERENT `.sys` term from `mirDupSys 1`
(the component lists are ordered the other way, and `.sys` is intensional). So the
same Löb construction is run again with the indices swapped: dupoc is component 0,
mirror is component 1. -/

private def dmAf (k : Nat) : Formula :=
  .plays (.bot (.sys (dupMirSys k) 1)) (.bot (.sys (dupMirSys k) 1)) Action.C

private def dmBf (k : Nat) : Formula :=
  .plays (.bot (.sys (dupMirSys k) 0)) (.bot (.sys (dupMirSys k) 0)) Action.C

/-- The Löb premise, dupoc-at-the-head: `□(mirror self-coops) → (mirror self-coops)`,
    chaining dupoc's search reading with mirror's copy reading. -/
theorem dupMir_loeb_premise (k : Nat) :
    Pf ((Formula.impl (.box k (dmAf k)) (dmBf k)).size
        + (Formula.impl (dmBf k) (dmAf k)).size
        + (Formula.impl (.box k (dmAf k)) (dmAf k)).size)
      (.impl (.box k (dmAf k)) (dmAf k)) :=
  Pf.implTrans _ _ _ _ _
    (sys_cross_C_at (dupMirSys k) 0 1 k _ (.bot (.sys (dupMirSys k) 0))
      (dupMirSys_get0 k) le_rfl)
    (sys_mirror_copies_C (dupMirSys k) 1 0 _ (.bot (.sys (dupMirSys k) 1))
      (dupMirSys_get1 k) le_rfl)
    le_rfl

theorem dupMir_loeb :
    ∃ k₂, ∀ k, k₂ < k → ∃ m, 2 * m ≤ k ∧ Pf m (dmAf k) := by
  refine pblt_engine_id_bounded dmAf
    (fun k => (Formula.impl (.box k (dmAf k)) (dmBf k)).size
            + (Formula.impl (dmBf k) (dmAf k)).size
            + (Formula.impl (.box k (dmAf k)) (dmAf k)).size) 0 ?_ ?_ ?_
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [dmAf, Formula.size, Prog.size, ProgList.psize, dupMirSys, numCost]
    omega
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [dmAf, dmBf, Formula.size, Prog.size, ProgList.psize, dupMirSys, numCost]
    omega
  · intro k _
    exact dupMir_loeb_premise k

/-- **The `hmirP` gate**: τ(Dupoc) COOPERATES with τ(Mirror). Its searcher's guard is
    the mirror component's self-cooperation, which Löb certifies. -/
theorem dupoc_mirror_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
        (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := dupMir_loeb
  obtain ⟨kC, hkC⟩ := linear_log2_add_le 200 4000
  refine ⟨max kL kC, fun k hk => ?_⟩
  obtain ⟨m, hmk, hm⟩ := hLb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hcg := hkC k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hlog := Nat.log2_le_self k
  have hpre : Pf k (((Formula.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C).sysClose
      (dupMirSys k)).subst (.bot (.sys (dupMirSys k) 0)) (.bot (.sys (dupMirSys k) 0))) := by
    rw [sysClose_subst_botSelfIdx]; exact Pf_mono hm (by omega)
  have h1 := PlaysProof.search_t (q := .const .D) hpre
    (PlaysProof.const (me := .bot (.sys (dupMirSys k) 0))
      (opponent := .bot (.sys (dupMirSys k) 0)) (a := Action.C))
  have hbody : PlaysProof (.bot (.sys (dupMirSys k) 0)) (.bot (.sys (dupMirSys k) 0))
      (.sys (dupMirSys k) 0) Action.C (c_leaf + c_guard k + c_node + c_node) :=
    PlaysProof.sysStep (dupMirSys_get0 k) (by simp only [Prog.sysClose]; exact h1)
  have hint : (probe (.sys (dupMirSys k) 0)).interp :=
    Pf_sound (c_leaf + c_guard k + c_node + c_node + c_node) _
      (Pf.atom ⟨PlaysProof.bot hbody,
        by have := hcl; have := hcn
           simp only [c_guard, numCost]
           omega⟩)
  rw [inst_dupoc_mirror_eq k]
  exact entry_C_of_interp hint

/-! ## What is NOT proven here, and why

**τ(Mirror)'s own `VoteBits` row is UNSTATEABLE.** `VoteBits.cons` demands a play
witness `∃ N, eval N (.bot I) (.bot I) I = some a` for EVERY entry, and the
diagonal has none — base MirrorBot's self-play is proven `none`. This is not an
effort gap: it is the roadmap's §8c.7 item 4 ("a TauBot always terminates") made
concrete. Every OTHER row carries its `.mirror` slot fine, because those need a
witness for `inst A .mirror`, which does play.

**The dupoc pair is CLOSED (2026-08-24), the other three remain gated.** Mirror is
a self-prober, so it entangles with dupoc, cupod, cimcic and dimcid. The DUPOC
orientation pair is now proven in both directions — `ps_probe_mirror_dupoc` (the
`hmir` bit) and `dupoc_mirror_plays_C` (the `hmirP` play) — by bounded Löb through
the binder, and `Tau/Theorems/Matrix` no longer takes either as a hypothesis:
`outcome_TauDupoc_vs_TauDupoc`, `outcome_TauJust_vs_TauJust`,
`outcome_TauDupoc_vs_TauJust` and `outcome_TauDupoc_vs_TauTFTPf` are
UNCONDITIONAL. The cupod and cimcic cells (`hmirCu`, `hmirCuP`, `hmirC`) are still
Löb-gated hypotheses.

**How the dupoc closure works, and why it needed a new rule.** The mirror component
is an `.ite` over a FROZEN `.sim` — a RUN stage, so its reading rule takes a PLAYS
premise, not a box. `mutual_pblt_engine_id` needs BOTH legs boxed and therefore does
not fit. `Pf.botSysRunStep` (the `.sys` twin of `botSimStep`, added for this and
certified in `Base/ValuationSoundness` + `Base/Transpose`) supplies the mirror's leg;
composing it AFTER dupoc's boxed leg via `implTrans` yields `□Af → Af`, so the pair
needs only the SINGLE-formula `pblt_engine_id_bounded` — cheaper than every earlier
entangled cell, which all needed the mutual engine.

**Why the bounded engine.** Re-certifying a Löb bit at budget `k` (a `proofSearch k`
gate, as opposed to merely consuming an `∃ m` play witness) needs the fixpoint's
transcript to FIT in `k`. `pblt_engine_id` threw that bound away; the new
`pblt_engine_id_bounded` (`Base/Loeb`) reports `2 * m ≤ k`, which the engine's own
size hypothesis already forced. No new mathematics — it just stops discarding it.

**The two orientations are DIFFERENT terms.** `inst .mirror .dupoc = .sys (mirDupSys k) 0`
and `inst .dupoc .mirror = .sys (dupMirSys k) 0` are not definitionally equal (the
component lists are ordered the other way, and `.sys` is intensional), so the Löb
construction is run TWICE, once per orientation. Checked by a failing `rfl`, not
assumed.

**What else IS proven**: the copy lemma, both ground cells, the provability route,
and the cell τ(EBot)'s restored third watch reads — which is what let EBot's
self-bit flip from `D` to `C` and agree with base. -/

end PD.Tau
