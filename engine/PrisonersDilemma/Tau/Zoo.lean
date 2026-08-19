import PrisonersDilemma.Tau.Bots.TauCooperate
import PrisonersDilemma.Tau.Bots.TauDefect
import PrisonersDilemma.Tau.Bots.TauTFTSim
import PrisonersDilemma.Tau.Bots.TauTFTPf
import PrisonersDilemma.Tau.Bots.TauDupoc
import PrisonersDilemma.Tau.Bots.TauEBot

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

def zoo6 (k : Nat) : Zoo Tmpl := ⟨tmplSpec, k⟩

/-- **The tau player**: bot A of the six-template zoo at prover budget k, signal
    weights `w`, caution threshold θ. -/
def TauBotZ (k : Nat) (A : Tmpl) (w : Tmpl → Nat) (θ : Nat) : Prog :=
  tauPlayer (vecOf (zoo6 k) A w order6) θ

/-! ## Gate D1 — byte-identity of the compiled closure

Every instance the compiler produces is `rfl`-equal to the hand-written Phase-4
closure (`Tau/Defs.lean`/`Tau/Vectors.lean`). A failed check = the COMPILER (or a
spec row) is wrong, not the closure. These persist as regression gates: any future
change to `instGo` (e.g. the `.sys` rewrite of the probed-object resolution) or to a
spec row must reproduce them or consciously replace them. -/

section GateD1
variable (k : Nat)

-- constants: signal-blind rows
example : ∀ T, inst (zoo6 k) .coop T = tauCoopδ := fun T => by cases T <;> rfl
example : ∀ T, inst (zoo6 k) .defect T = tauDefectδ := fun T => by cases T <;> rfl

-- τ(Dupoc)'s row — the δ_L column, incl. the QUINE and the FLOOR entry
example : inst (zoo6 k) .dupoc .coop   = searchOfCoopδ k := rfl
example : inst (zoo6 k) .dupoc .defect = searchOfDefectδ k := rfl
example : inst (zoo6 k) .dupoc .tftSim = probeSearchδ k (simOfSearchδ k) := rfl
example : inst (zoo6 k) .dupoc .tftPf  = probeSearchδ k (searchOfSearchδ k) := rfl
example : inst (zoo6 k) .dupoc .dupoc  = TauDupocδ k := rfl          -- the quine
example : inst (zoo6 k) .dupoc .ebot   = probeSearchδ k (eOfSearchδ k) := rfl  -- the floor

-- τ(TFTPf)'s row — the δ_C column, by proof
example : inst (zoo6 k) .tftPf .coop   = probeSearchδ k tauCoopδ := rfl
example : inst (zoo6 k) .tftPf .defect = probeSearchδ k tauDefectδ := rfl
example : inst (zoo6 k) .tftPf .tftSim = probeSearchδ k simOfCoopδ := rfl
example : inst (zoo6 k) .tftPf .tftPf  = probeSearchδ k (searchOfCoopδ k) := rfl
example : inst (zoo6 k) .tftPf .dupoc  = probeSearchδ k (searchOfCoopδ k) := rfl
example : inst (zoo6 k) .tftPf .ebot   = probeSearchδ k (eOfCoopδ k) := rfl

-- τ(TFTSim)'s row — the δ_C column, by simulation
example : inst (zoo6 k) .tftSim .coop   = tftSimδ tauCoopδ := rfl
example : inst (zoo6 k) .tftSim .defect = tftSimδ tauDefectδ := rfl
example : inst (zoo6 k) .tftSim .tftSim = tftSimδ simOfCoopδ := rfl
example : inst (zoo6 k) .tftSim .tftPf  = tftSimδ (searchOfCoopδ k) := rfl
example : inst (zoo6 k) .tftSim .dupoc  = tftSimδ (searchOfCoopδ k) := rfl
example : inst (zoo6 k) .tftSim .ebot   = tftSimδ (eOfCoopδ k) := rfl

-- τ(EBot)'s row — the whole cascade per hypothesis
example : inst (zoo6 k) .ebot .coop   = eOfCoopδ k := rfl
example : inst (zoo6 k) .ebot .defect = eOfDefectδ k := rfl
example : inst (zoo6 k) .ebot .tftSim = eOfSimδ k := rfl
example : inst (zoo6 k) .ebot .tftPf  = eOfPfδ k := rfl
example : inst (zoo6 k) .ebot .dupoc  = eOfSearchδ k := rfl
example : inst (zoo6 k) .ebot .ebot   = eOfSelfδ k := rfl

end GateD1

end PD.Tau
