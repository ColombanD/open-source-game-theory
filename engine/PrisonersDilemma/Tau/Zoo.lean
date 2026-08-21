import PrisonersDilemma.Tau.Bots.TauCooperate
import PrisonersDilemma.Tau.Bots.TauDefect
import PrisonersDilemma.Tau.Bots.TauTFTSim
import PrisonersDilemma.Tau.Bots.TauTFTPf
import PrisonersDilemma.Tau.Bots.TauDupoc
import PrisonersDilemma.Tau.Bots.TauEBot
import PrisonersDilemma.Tau.Bots.TauJust
import PrisonersDilemma.Tau.Bots.TauOBot
import PrisonersDilemma.Tau.Bots.TauGuardian
import PrisonersDilemma.Tau.Bots.TauDBot
import PrisonersDilemma.Tau.Bots.TauCupodTroll
import PrisonersDilemma.Tau.Bots.TauCupod
import PrisonersDilemma.Tau.Bots.TauCIMCIC

/-!
# Tau/Zoo — the assembled six-template zoo, its players, and Gate D1

The binding step of the base-bot-style layout: `Tau/Roster.lean` declared the cast,
each `Tau/Bots/<TauBot>.lean` wrote one spec row, and this file glues the rows into
the zoo function, builds the players, and carries the Gate-D1 byte-identity checks.
Adding a bot: one constructor in the roster, one bot file, one arm in `tmplSpec`
below (and its arms in the consulted `InstCerts` columns — the mathematics).
-/

open PD

namespace PD.Tau

/-- The zoo function: one arm per roster member, each delegating to that bot's own
    file. This match IS the zoo. -/
def tmplSpec : Tmpl → Spec Tmpl
  | .coop   => tauCoopSpec
  | .defect => tauDefectSpec
  | .tftSim => tauTFTSimSpec
  | .tftPf  => tauTFTPfSpec
  | .dupoc  => tauDupocSpec
  | .ebot   => tauEBotSpec
  | .just   => tauJustSpec
  | .obot   => tauOBotSpec
  | .guardian => tauGuardianSpec
  | .dbot     => tauDBotSpec
  | .cupodTroll => tauCupodTrollSpec
  | .cupod    => tauCupodSpec
  | .cimcic   => tauCIMCICSpec

def tauZoo (k : Nat) : Zoo Tmpl := ⟨tmplSpec, k⟩

/-- **The tau player**: bot A of the six-template zoo at prover budget k, signal
    weights `w`, caution threshold θ. -/
def TauBotZ (k : Nat) (A : Tmpl) (w : Tmpl → Nat) (θ : Nat) : Prog :=
  tauPlayer (vecOf (tauZoo k) A w tauOrder) θ

/-! ## Gate D1 — the compiler pinned, one peel at a time

With the hand-written closure retired (2026-08-18 cleanup), the compiler is pinned
against EXPLICIT one-level unfoldings: each equation exposes exactly one compile
step, with the probed subterms still written as `inst …` — whose own equations pin
them in turn, so the composition pins every instance byte-for-byte. All by `rfl`
(kernel computation). These double as the peel handles the `Certs` proofs rewrite
with. Any future change to `instGo` (e.g. the `.sys` rewrite of the probed-object
resolution) must reproduce them or consciously replace them. -/

/-- Constants ignore their hypothesis. -/
theorem inst_coop_peel (k : Nat) : ∀ T, inst (tauZoo k) .coop T = .const .C :=
  fun T => by cases T <;> rfl

theorem inst_defect_peel (k : Nat) : ∀ T, inst (tauZoo k) .defect T = .const .D :=
  fun T => by cases T <;> rfl

/-- τ(TFTPf)'s row: one prove-stage on the hypothesis's δ_C instance. -/
theorem inst_tftPf_peel (k : Nat) : ∀ T, inst (tauZoo k) .tftPf T
    = .search k (probe (inst (tauZoo k) T .coop)) (.const .C) (.const .D) :=
  fun T => by cases T <;> rfl

/-- τ(TFTSim)'s row: one run-stage on the same instance — the behavioral read. -/
theorem inst_tftSim_peel (k : Nat) : ∀ T, inst (tauZoo k) .tftSim T
    = .ite (.sim (.bot (inst (tauZoo k) T .coop)) (.bot (inst (tauZoo k) T .coop)))
        Action.C (.const .C) (.const .D) :=
  fun T => by cases T <;> rfl

/-- τ(EBot)'s row: the two-stage RUN cascade (base EBot's own sim modality) over
    the hypothesis's δ_D and δ_C instances. -/
theorem inst_ebot_peel (k : Nat) : ∀ T, inst (tauZoo k) .ebot T
    = .ite (.sim (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect)))
        .C (.const .D)
        (.ite (.sim (.bot (inst (tauZoo k) T .coop)) (.bot (inst (tauZoo k) T .coop)))
          .C (.const .C) (.const .D)) :=
  fun T => by cases T <;> rfl

/-- τ(DBot)'s row: ONE run-stage watching the hypothesis's δ_D instance, with a
    trusting constant tail. -/
theorem inst_dbot_peel (k : Nat) : ∀ T, inst (tauZoo k) .dbot T
    = .ite (.sim (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect)))
        .C (.const .D) (.const .C) :=
  fun T => by cases T <;> rfl

/-- τ(CupodTroll)'s row: one `proveEq` stage — a structural identity test against
    the probed instance. The `.opp` subject stays a pronoun (resolved by `subst` at
    consultation, exactly as base CupodTrollBot's `.eq .opp …` does). -/
theorem inst_cupodTroll_peel (k : Nat) : ∀ T, inst (tauZoo k) .cupodTroll T
    = .search k (.eq .opp (.bot (inst (tauZoo k) T .dupoc)))
        (.const .D) (.const .C) :=
  fun T => by cases T <;> rfl

/-! ### τ(Cupod)'s row — the FIRST `.sys` row (2026-08-20)

Three shapes, because Cupod is a self-prober meeting another self-prober:
* off-cycle hypotheses compile to an ordinary prove-stage (the partner is not a
  self-prober, so the §6.3 rank argument bottoms out);
* the DIAGONAL is the quine pronoun, exactly like Dupoc's;
* the ENTANGLED cell (`.dupoc`) is the 2-member `.sys` system — the shape that had
  no term at all before the binder. -/

theorem inst_cupod_peel_coop (k : Nat) : inst (tauZoo k) .cupod .coop
    = .search k (probeD (inst (tauZoo k) .coop .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_defect (k : Nat) : inst (tauZoo k) .cupod .defect
    = .search k (probeD (inst (tauZoo k) .defect .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_tftSim (k : Nat) : inst (tauZoo k) .cupod .tftSim
    = .search k (probeD (inst (tauZoo k) .tftSim .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_tftPf (k : Nat) : inst (tauZoo k) .cupod .tftPf
    = .search k (probeD (inst (tauZoo k) .tftPf .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_ebot (k : Nat) : inst (tauZoo k) .cupod .ebot
    = .search k (probeD (inst (tauZoo k) .ebot .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_just (k : Nat) : inst (tauZoo k) .cupod .just
    = .search k (probeD (inst (tauZoo k) .just .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_obot (k : Nat) : inst (tauZoo k) .cupod .obot
    = .search k (probeD (inst (tauZoo k) .obot .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_guardian (k : Nat) : inst (tauZoo k) .cupod .guardian
    = .search k (probeD (inst (tauZoo k) .guardian .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_dbot (k : Nat) : inst (tauZoo k) .cupod .dbot
    = .search k (probeD (inst (tauZoo k) .dbot .cupod)) (.const .D) (.const .C) := rfl
theorem inst_cupod_peel_cupodTroll (k : Nat) : inst (tauZoo k) .cupod .cupodTroll
    = .search k (probeD (inst (tauZoo k) .cupodTroll .cupod)) (.const .D) (.const .C) := rfl

/-- τ(Cupod)'s DIAGONAL — the quine, mirroring Dupoc's with inverted polarity. -/
theorem inst_cupod_quine (k : Nat) : inst (tauZoo k) .cupod .cupod
    = .search k (.plays .self .self Action.D) (.const .D) (.const .C) := rfl

/-- **THE ENTANGLED CELL** — τ(Cupod) meeting τ(Dupoc). Component 0 is Cupod-seeing-
    Dupoc, component 1 is Dupoc-seeing-Cupod, and each probes the other by INDEX.
    This term did not exist before the `.sys` binder. -/
theorem inst_cupod_sys_dupoc (k : Nat) : inst (tauZoo k) .cupod .dupoc
    = .sys (.cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
                     (.const .D) (.const .C))
           (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
                     (.const .C) (.const .D)) .nil)) 0 := rfl

/-- …and the same system seen from Dupoc's side: component 0 is now Dupoc-seeing-
    Cupod. The two cells share one system, with the roles of the indices swapped. -/
theorem inst_dupoc_sys_cupod (k : Nat) : inst (tauZoo k) .dupoc .cupod
    = .sys (.cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
                     (.const .C) (.const .D))
           (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
                     (.const .D) (.const .C)) .nil)) 0 := rfl

/-! ### τ(CIMCIC)'s row — the first `.impl`-guard row, three shapes (2026-08-21)

* off-cycle hypotheses: a `proveImpl` stage — NOTE the guard is NOT closed under
  `subst` (its antecedent subject is the `.self` pronoun), unlike every
  plays-atom row;
* the DIAGONAL: the pronoun on BOTH sides — after subst the guard is literally
  `φ → φ`, closed by `Pf.implRefl` (no Löb needed);
* the ENTANGLED cells (`.dupoc`, `.cupod`): 2-member `.sys` systems, emitted
  UNIFORMLY with the `.prove` pairs (the asymmetric alternative — recursing here
  while the partner's arm emits — would create two syntactic representations of
  one instance). -/

theorem inst_cimcic_peel_coop (k : Nat) : inst (tauZoo k) .cimcic .coop
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .coop .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .coop .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_defect (k : Nat) : inst (tauZoo k) .cimcic .defect
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .defect .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .defect .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_tftSim (k : Nat) : inst (tauZoo k) .cimcic .tftSim
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .tftSim .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .tftSim .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_tftPf (k : Nat) : inst (tauZoo k) .cimcic .tftPf
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .tftPf .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .tftPf .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_ebot (k : Nat) : inst (tauZoo k) .cimcic .ebot
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .ebot .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .ebot .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_just (k : Nat) : inst (tauZoo k) .cimcic .just
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .just .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .just .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_obot (k : Nat) : inst (tauZoo k) .cimcic .obot
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .obot .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .obot .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_guardian (k : Nat) : inst (tauZoo k) .cimcic .guardian
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .guardian .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .guardian .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_dbot (k : Nat) : inst (tauZoo k) .cimcic .dbot
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .dbot .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .dbot .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl
theorem inst_cimcic_peel_cupodTroll (k : Nat) : inst (tauZoo k) .cimcic .cupodTroll
    = .search k (.impl (.plays .self (.bot (inst (tauZoo k) .cupodTroll .cimcic)) Action.C)
                       (.plays (.bot (inst (tauZoo k) .cupodTroll .cimcic)) .self Action.C))
        (.const .C) (.const .D) := rfl

/-- τ(CIMCIC)'s DIAGONAL: after subst the guard is `φ → φ` — `implRefl` territory. -/
theorem inst_cimcic_quine (k : Nat) : inst (tauZoo k) .cimcic .cimcic
    = .search k (.impl (.plays .self .self Action.C) (.plays .self .self Action.C))
        (.const .C) (.const .D) := rfl

/-- The CIMCIC↔Dupoc entangled system. -/
theorem inst_cimcic_sys_dupoc (k : Nat) : inst (tauZoo k) .cimcic .dupoc
    = .sys (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                                    (.plays (.bot (.selfIdx 1)) .self Action.C))
                     (.const .C) (.const .D))
           (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
                     (.const .C) (.const .D)) .nil)) 0 := rfl

/-- The CIMCIC↔Cupod entangled system. -/
theorem inst_cimcic_sys_cupod (k : Nat) : inst (tauZoo k) .cimcic .cupod
    = .sys (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                                    (.plays (.bot (.selfIdx 1)) .self Action.C))
                     (.const .C) (.const .D))
           (.cons (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.D)
                     (.const .D) (.const .C)) .nil)) 0 := rfl

/-- …and the mirrored systems, seen from the partners' sides. -/
theorem inst_dupoc_sys_cimcic (k : Nat) : inst (tauZoo k) .dupoc .cimcic
    = .sys (.cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
                     (.const .C) (.const .D))
           (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                                    (.plays (.bot (.selfIdx 0)) .self Action.C))
                     (.const .C) (.const .D)) .nil)) 0 := rfl
theorem inst_cupod_sys_cimcic (k : Nat) : inst (tauZoo k) .cupod .cimcic
    = .sys (.cons (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.D)
                     (.const .D) (.const .C))
           (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                                    (.plays (.bot (.selfIdx 0)) .self Action.C))
                     (.const .C) (.const .D)) .nil)) 0 := rfl

/-- τ(Dupoc)'s row, OFF the diagonal: one prove-stage on the hypothesis's δ_L
    instance ("does T, seeing me, cooperate?"). -/
theorem inst_dupoc_peel_coop (k : Nat) : inst (tauZoo k) .dupoc .coop
    = .search k (probe (inst (tauZoo k) .coop .dupoc)) (.const .C) (.const .D) := rfl
theorem inst_dupoc_peel_defect (k : Nat) : inst (tauZoo k) .dupoc .defect
    = .search k (probe (inst (tauZoo k) .defect .dupoc)) (.const .C) (.const .D) := rfl
theorem inst_dupoc_peel_tftSim (k : Nat) : inst (tauZoo k) .dupoc .tftSim
    = .search k (probe (inst (tauZoo k) .tftSim .dupoc)) (.const .C) (.const .D) := rfl
theorem inst_dupoc_peel_tftPf (k : Nat) : inst (tauZoo k) .dupoc .tftPf
    = .search k (probe (inst (tauZoo k) .tftPf .dupoc)) (.const .C) (.const .D) := rfl
theorem inst_dupoc_peel_ebot (k : Nat) : inst (tauZoo k) .dupoc .ebot
    = .search k (probe (inst (tauZoo k) .ebot .dupoc)) (.const .C) (.const .D) := rfl

/-- τ(Dupoc)'s DIAGONAL — the QUINE, fully literal: the compiler cannot embed the
    instance in its own guard, so it emits the pronoun, and the guard becomes the
    Löb fixpoint sentence. -/
theorem inst_dupoc_quine (k : Nat) : inst (tauZoo k) .dupoc .dupoc
    = .search k (.plays .self .self Action.C) (.const .C) (.const .D) := rfl

/-- τ(Just)'s row: one prove-stage on the hypothesis's δ_L instance — the SAME
    probed objects as τ(Dupoc)'s row (JustBot consults the column by NAME, Dupoc by
    SELF; off Dupoc's diagonal the rows are byte-identical). -/
theorem inst_just_peel (k : Nat) : ∀ T, inst (tauZoo k) .just T
    = .search k (probe (inst (tauZoo k) T .dupoc)) (.const .C) (.const .D) :=
  fun T => by cases T <;> rfl

/-- τ(OBot)'s row: two run-stages TESTING DEFECTION (`test = .D`) over the
    hypothesis's δ_C and δ_D instances, default C. -/
theorem inst_obot_peel (k : Nat) : ∀ T, inst (tauZoo k) .obot T
    = .ite (.sim (.bot (inst (tauZoo k) T .coop)) (.bot (inst (tauZoo k) T .coop)))
        Action.D (.const .D)
        (.ite (.sim (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect)))
          Action.D (.const .D) (.const .C)) :=
  fun T => by cases T <;> rfl

/-- τ(Guardian)'s row: one prove-stage on a DEFECTION atom (`test = .D`) over the
    hypothesis's δ_C instance, default C. -/
theorem inst_guardian_peel (k : Nat) : ∀ T, inst (tauZoo k) .guardian T
    = .search k (.plays (.bot (inst (tauZoo k) T .coop))
                        (.bot (inst (tauZoo k) T .coop)) Action.D)
        (.const .D) (.const .C) :=
  fun T => by cases T <;> rfl

end PD.Tau
