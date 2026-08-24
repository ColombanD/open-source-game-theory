import PrisonersDilemma.Tau.Theorems.Helpers

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

/-! ## What is NOT proven here, and why

**τ(Mirror)'s own `VoteBits` row is UNSTATEABLE.** `VoteBits.cons` demands a play
witness `∃ N, eval N (.bot I) (.bot I) I = some a` for EVERY entry, and the
diagonal has none — base MirrorBot's self-play is proven `none`. This is not an
effort gap: it is the roadmap's §8c.7 item 4 ("a TauBot always terminates") made
concrete. Every OTHER row carries its `.mirror` slot fine, because those need a
witness for `inst A .mirror`, which does play.

**The five entangled pairs are GATED, not proven.** Mirror is a self-prober, so
it entangles with dupoc, cupod, cimcic and dimcid. Their cells enter the columns
and rows as Löb-gated hypotheses (`hmir`, `hmirP`, `hmirCu`, …) exactly as
`hquine` and `hcim` already did. The mathematics is a MUTUAL SIMULATION — mirror
copies while the partner proves — whose base analogue is
`outcome_DupocBot_vs_MirrorBot = (C, C)`, closed by Löb. Discharging those gates
is the natural next step and needs no new engine rule: `PlaysProof.sysStep` is
shape-generic and closes an `.ite` component as readily as a `.search` one.

**What IS proven**: the copy lemma, both ground cells, the provability route, and
the cell τ(EBot)'s restored third watch reads — which is what let EBot's self-bit
flip from `D` to `C` and agree with base. -/

end PD.Tau
