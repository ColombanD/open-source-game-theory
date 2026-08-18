import PrisonersDilemma.Tau.Vote

/-!
# Tau/Vectors — the decision vectors of the refined Def-4 zoo (2026-08-18)

Under the source lift τ, a tau player is `tauPlayer v θ` where the DECISION VECTOR `v`
lists, per hypothesis `T`, the instance `inst(A, δ_T)` — base bot `A`'s ENTIRE decision
procedure run at point mass on `T`. All per-bot content lives here; the vote, the peel
and the phase theorem above are uniform.

**The instance layer is reused verbatim** from the 2026-08-11/12 milestone (`Tau/Defs`,
`Tau/Certs`): `probeSearchδ`, `tftSimδ`, `eδ`, the quine `TauDupocδ`, and every bit
lemma. That layer was always correct — the 2026-08-13 retraction hit only the σ-player
geometry, which is what this file replaces.

**The zoo is restricted to ≤ 1 self-prober** (TauDupoc), per the roadmap: two
self-probing bots need `inst(A,δ_B)` to contain `inst(B,δ_A)` and vice versa, which no
closed term can satisfy (`.self` cuts only the diagonal). The `.sys` binder is the
designated route to lift that restriction.

## The instance columns

Every entry below already exists in `Tau/Defs` — τ merely selects, per (bot,
hypothesis) pair, which instance the bot's own code produces:

| bot A | entry at hypothesis T | column read |
|---|---|---|
| TauCooperate | `.const C` | signal-blind |
| TauDefect | `.const D` | signal-blind |
| TauDupoc | `probeSearchδ k (T(δ_L))` | δ_L (self-probe: "does T, seeing me, cooperate?") |
| TauTFTPf | `probeSearchδ k (T(δ_C))` | δ_C |
| TauTFTSim | `tftSimδ (T(δ_C))` | δ_C, behaviorally |
| TauEBot | `eδ k (T(δ_D)) (T(δ_C))` | the CASCADE, per hypothesis — see below |

**τ(EBot) is the bot the retraction singled out.** Its entry per hypothesis is the
WHOLE cascade at point mass (exploit-check, then reciprocity-check), and the vote
happens ONCE over those compound decisions. The retracted "crowd-exploiter" instead put
a θ-threshold inside each cascade stage — a coherent agent, but not a lift of EBot.
Its bits here are Coop 0, Defect 0, TFTSim 1, TFTPf 1, Dupoc 1, EBot 0, giving the
ONE-SIDED boundary `θ ≤ wTs + wTp + wL` and NO window.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## τ(EBot)'s remaining instances

`eOfCoopδ`/`eOfDefectδ`/`eOfSearchδ` are in `Tau/Defs`. The lift needs two more: EBot
against the two TFT hypotheses, and against ITSELF. All ground — the cascade probes
only the closed δ_D/δ_C columns, so no quine is needed (this is what made the whole
E-family expressible without stipulation). -/

/-- `E(δ_Ts)`: TauEBot seeing TauTFTSim. Exploit-probe of `Ts(δ_D) = simOfDefectδ`
    (defects vs a defector ⇒ fails), reciprocity-probe of `Ts(δ_C) = simOfCoopδ`
    (cooperates ⇒ fires): TauEBot COOPERATES with the behavioral TFT. -/
def eOfSimδ (k : Nat) : Prog := eδ k simOfDefectδ simOfCoopδ

/-- `E(δ_Tp)`: TauEBot seeing TauTFTPf. Same shape over the prover TFT's instances;
    `Tp(δ_D) = searchOfDefectδ`, `Tp(δ_C) = searchOfCoopδ` — so this term is literally
    `eOfSearchδ`, since TauDupoc and TauTFTPf share both column entries. -/
def eOfPfδ (k : Nat) : Prog := eδ k (searchOfDefectδ k) (searchOfCoopδ k)

/-- `E(δ_E)`: TauEBot seeing ITSELF. Grounded, no quine: the exploit stage probes
    `E(δ_D) = eOfDefectδ` (defects ⇒ fails) and the reciprocity stage probes
    `E(δ_C) = eOfCoopδ` (also defects — it exploits a cooperator ⇒ fails), so the
    cascade falls through: **TauEBot DEFECTS against itself.** Faithful to base
    `EBot vs EBot`, whose Mirror-branch escape is not `.opp`-free-liftable (the one
    genuinely open lift convention, recorded in the design note). -/
def eOfSelfδ (k : Nat) : Prog := eδ k (eOfDefectδ k) (eOfCoopδ k)

/-! ## The decision vectors

Weights `wC wD wTs wTp wL wE` over the six hypotheses, in the fixed order
Coop, Defect, TFTSim, TFTPf, Dupoc, EBot. -/

/-- τ(CooperateBot): signal-blind, every entry cooperates. -/
def coopVec (wC wD wTs wTp wL wE : Nat) : VoteList :=
  .cons wC (.const .C) (.cons wD (.const .C) (.cons wTs (.const .C)
    (.cons wTp (.const .C) (.cons wL (.const .C) (.cons wE (.const .C) .nil)))))

/-- τ(DefectBot): signal-blind, every entry defects. -/
def defectVec (wC wD wTs wTp wL wE : Nat) : VoteList :=
  .cons wC (.const .D) (.cons wD (.const .D) (.cons wTs (.const .D)
    (.cons wTp (.const .D) (.cons wL (.const .D) (.cons wE (.const .D) .nil)))))

/-- τ(DupocBot): each entry asks "can I prove this hypothesis, seeing ME, cooperates?"
    — the δ_L column. The Dupoc entry is the `.self` quine (Löb); the EBot entry is
    the FLOOR cell: `E(δ_L)` really cooperates but only through a failed exploit
    search, so no ≤k certificate exists and the entry's own guard reads 0 ⇒ it plays D. -/
def dupocVec (k wC wD wTs wTp wL wE : Nat) : VoteList :=
  .cons wC (probeSearchδ k tauCoopδ)
    (.cons wD (probeSearchδ k tauDefectδ)
      (.cons wTs (probeSearchδ k (simOfSearchδ k))
        (.cons wTp (probeSearchδ k (searchOfSearchδ k))
          (.cons wL (TauDupocδ k)
            (.cons wE (probeSearchδ k (eOfSearchδ k)) .nil)))))

/-- τ(TitForTatBot), prover variant: the δ_C column ("does this hypothesis cooperate
    with a cooperator?"), read by proof. -/
def tftPfVec (k wC wD wTs wTp wL wE : Nat) : VoteList :=
  .cons wC (probeSearchδ k tauCoopδ)
    (.cons wD (probeSearchδ k tauDefectδ)
      (.cons wTs (probeSearchδ k simOfCoopδ)
        (.cons wTp (probeSearchδ k (searchOfCoopδ k))
          (.cons wL (probeSearchδ k (searchOfCoopδ k))
            (.cons wE (probeSearchδ k (eOfCoopδ k)) .nil)))))

/-- τ(TitForTatBot), behavioral variant: the δ_C column read by SIMULATION. Same
    α-boundary as the prover variant, reached at a far smaller budget — the
    prover/behavioral split is a budget-phase gap, not an α-gap. -/
def tftSimVec (k wC wD wTs wTp wL wE : Nat) : VoteList :=
  .cons wC (tftSimδ tauCoopδ)
    (.cons wD (tftSimδ tauDefectδ)
      (.cons wTs (tftSimδ simOfCoopδ)
        (.cons wTp (tftSimδ (searchOfCoopδ k))
          (.cons wL (tftSimδ (searchOfCoopδ k))
            (.cons wE (tftSimδ (eOfCoopδ k)) .nil)))))

/-- τ(EBot): each entry is the WHOLE exploiter cascade at point mass. One vote over
    compound decisions — NOT a vote per cascade stage (that was the retracted
    crowd-exploiter). -/
def eVec (k wC wD wTs wTp wL wE : Nat) : VoteList :=
  .cons wC (eOfCoopδ k)
    (.cons wD (eOfDefectδ k)
      (.cons wTs (eOfSimδ k)
        (.cons wTp (eOfPfδ k)
          (.cons wL (eOfSearchδ k)
            (.cons wE (eOfSelfδ k) .nil)))))

/-! ## The players -/

def TauCooperate (wC wD wTs wTp wL wE θ : Nat) : Prog :=
  tauPlayer (coopVec wC wD wTs wTp wL wE) θ

def TauDefect (wC wD wTs wTp wL wE θ : Nat) : Prog :=
  tauPlayer (defectVec wC wD wTs wTp wL wE) θ

def TauDupoc (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  tauPlayer (dupocVec k wC wD wTs wTp wL wE) θ

def TauTFTPf (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  tauPlayer (tftPfVec k wC wD wTs wTp wL wE) θ

def TauTFTSim (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  tauPlayer (tftSimVec k wC wD wTs wTp wL wE) θ

def TauEBot (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  tauPlayer (eVec k wC wD wTs wTp wL wE) θ

/-! ## Entry-play lemmas

What each instance template PLAYS, from the guard bits `Tau/Certs` already proves.
Probes are closed (`probe_subst`), so an entry's play never depends on the frame it is
consulted from — which is the term-level reason a tau player's action depends on its
signal alone. -/

/-- A `probeSearchδ` entry cooperates exactly when its probe fires. -/
theorem probeSearchδ_plays_C {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probe I) = true) :
    ∃ N, eval N me opp (probeSearchδ k I) = some Action.C := by
  refine ⟨2, ?_⟩
  rw [probeSearchδ, eval, probe_subst, h]
  rfl

/-- …and defects when it does not. -/
theorem probeSearchδ_plays_D {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probe I) = false) :
    ∃ N, eval N me opp (probeSearchδ k I) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [probeSearchδ, eval, probe_subst, h, if_neg (by simp)]
  rfl

/-- The exploiter cascade DEFECTS when its exploit-probe fires (the hypothesis is
    exploitable). -/
theorem eδ_plays_D_of_exploit {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = true) :
    ∃ N, eval N me opp (eδ k I_D I_C) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eδ, eval, probe_subst, h1]
  rfl

/-- …COOPERATES when the exploit fails but reciprocity fires. -/
theorem eδ_plays_C {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = false)
    (h2 : proofSearch k (probe I_C) = true) :
    ∃ N, eval N me opp (eδ k I_D I_C) = some Action.C := by
  refine ⟨3, ?_⟩
  rw [eδ, eval, probe_subst, h1, if_neg (by simp), eval, probe_subst, h2]
  rfl

/-- …and DEFECTS when neither fires (unreciprocating). -/
theorem eδ_plays_D_of_both_false {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = false)
    (h2 : proofSearch k (probe I_C) = false) :
    ∃ N, eval N me opp (eδ k I_D I_C) = some Action.D := by
  refine ⟨3, ?_⟩
  rw [eδ, eval, probe_subst, h1, if_neg (by simp), eval, probe_subst, h2,
      if_neg (by simp)]
  rfl

/-- A `tftSimδ` entry COPIES what its frozen hypothesis plays against itself — the
    behavioral read, so it sees TRUE plays and is blind to the provability floor. One
    lemma covers every behavioral entry. -/
theorem tftSimδ_plays {I : Prog} {a : Action} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some a) :
    ∃ N, eval N me opp (tftSimδ I) = some a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 3, ?_⟩
  rw [tftSimδ, eval]
  have hg : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some a := by
    rw [eval]
    simp only [Prog.subst]
    rw [eval]
    exact eval_mono_le hN _ (by omega)
  rw [hg]
  cases a with
  | C => simp only [bind, Option.bind]; rw [if_pos (by decide)]; rfl
  | D => simp only [bind, Option.bind]; rw [if_neg (by decide)]; rfl

/-- The `.const` instances play their constant, in any frame. -/
theorem constδ_plays (me opp : Prog) (a : Action) :
    ∃ N, eval N me opp (.const a) = some a := ⟨1, rfl⟩

end PD.Tau
