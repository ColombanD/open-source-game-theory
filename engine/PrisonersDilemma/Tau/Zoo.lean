import PrisonersDilemma.Tau.Bots.TauCooperate
import PrisonersDilemma.Tau.Bots.TauDefect
import PrisonersDilemma.Tau.Bots.TauTFTSim
import PrisonersDilemma.Tau.Bots.TauTFTPf
import PrisonersDilemma.Tau.Bots.TauDupoc
import PrisonersDilemma.Tau.Bots.TauEBot
import PrisonersDilemma.Tau.Bots.TauJust
import PrisonersDilemma.Tau.Bots.TauOBot
import PrisonersDilemma.Tau.Bots.TauGuardian

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
