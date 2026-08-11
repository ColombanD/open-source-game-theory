import PrisonersDilemma.Dynamics

/-!
# Tau/Defs — the Def-4 TauBot zoo (milestone 1, 2026-08-11)

**Definition 4** (TAUBOT_TRANSPARENCY_DESIGN.md, Part III): tau-native agents whose
signal hypotheses AND probes are TauBots, every recursive reference routed through
`proofSearch` — the Löbian machinery breaks the regress that sank the old Def 1
(whose recursion was semantic, via `play`).

Fixed 5-template zoo: TauCooperate (`C`), TauDefect (`D`), TauDupoc (`L`),
TauTitForTatSim (`Ts`), TauTitForTatPf (`Tp`). Conventions:

* **Signals are weighted lists over template names**; a probe re-instantiates its
  hypothesis at a POINT-MASS signal. So the probed objects are the finite instance
  family `B(δ_T)`, closed terms defined below.
* **Probe atom** (`probe`): the instance is `.bot`-frozen (the subst barrier — a bare
  slot would have the enclosing player's `subst` rewrite the instance's internal
  `.self`) and asked to play C **against itself** (the second slot is inert for
  `.opp`-free programs; instance-vs-itself is the canonical closed choice).
* **Tau programs are `.opp`-free** — that IS partial transparency: the signal replaces
  the wire to the actual opponent. Consequently every tau player is extensionally
  constant (its play depends on its signal only), and the 25-cell outcome matrix
  factors through the 5 play theorems.
* **Guard order: Löbian guards LAST**, so low-budget/low-threshold regimes commit via
  the stepwise short-circuits before ever consulting the walled Löb guard.
* **Prover instances stay `.search` singletons** (a point-mass `tsearch` degenerates
  to `.search`), keeping the modal reading rules (`searchBranch`/`botSearchStep`)
  applicable; only the σ-players (never probed by anyone) use `.tsearch`.

**The instance closure is 7 terms.** TauDupoc's σ-player probes the δ_L column
(`B(δ_L)`: "does B, seeing exactly me, cooperate"); both TFTs probe the δ_C column
(`B(δ_C)`: "does B, seeing TauCooperate, cooperate"). Chasing references:
`C(δ_·) = .const C`, `D(δ_·) = .const D` (signal-blind);
`L(δ_C) = Tp(δ_C) = probeSearchδ tauCoopδ`; `Ts(δ_C) = tftSimδ tauCoopδ`;
`Ts(δ_L) = tftSimδ (L(δ_C))`; `Tp(δ_L) = probeSearchδ (L(δ_C))`;
`L(δ_L)` = the quine. Everything grounds in a DAG except the single `L(δ_L)`
self-loop, which the `.self` quine cuts.
-/

open PD

namespace PD.Tau

/-- Def-4 probe atom for a hypothesis instance `I` (frozen, vs itself). -/
def probe (I : Prog) : Formula := .plays (.bot I) (.bot I) Action.C

/-- One-hypothesis PROVER instance: cooperate iff the probe of `I` is provable within
    `k`. This is `B(δ_T)` for both prover templates (`L` and `Tp`) — which template it
    "came from" is recorded only by WHICH instance it is applied to. -/
def probeSearchδ (k : Nat) (I : Prog) : Prog :=
  .search k (probe I) (.const .C) (.const .D)

/-- One-hypothesis BEHAVIORAL instance (`Ts(δ_T)`): RUN the frozen hypothesis against
    itself and copy cooperation. Sees TRUE plays, not provable ones. -/
def tftSimδ (I : Prog) : Prog :=
  .ite (.sim (.bot I) (.bot I)) Action.C (.const .C) (.const .D)

/-- `L(δ_L)` — the quine: TauDupoc whose point-mass hypothesis is ITSELF. The only
    cyclic instance; `.self` is the built-in quine (an inductive term cannot contain
    its own frozen source, so the frozen-instance pattern of `probeSearchδ` is
    unwritable here). Running anywhere, `subst` closes the guard to the
    opponent-independent Löb sentence `.plays me me .C` with `me` the enclosing
    player — `.bot (TauDupocδ k)` when probed frozen, which is the fixpoint the
    Certs Löb lemma closes via `botSearchStep` + `pblt_engine_id`. -/
def TauDupocδ (k : Nat) : Prog :=
  .search k (.plays .self .self Action.C) (.const .C) (.const .D)

/-! ## The δ-instance closure (7 terms) -/

/-- `C(δ_T)` for every `T` — TauCooperate ignores its signal. -/
def tauCoopδ : Prog := .const .C

/-- `D(δ_T)` for every `T`. -/
def tauDefectδ : Prog := .const .D

/-- `L(δ_C) = Tp(δ_C)`: a prover seeing TauCooperate — guard trivially provable. -/
def searchOfCoopδ (k : Nat) : Prog := probeSearchδ k tauCoopδ

/-- `Ts(δ_C)`: the behavioral TFT seeing TauCooperate. -/
def simOfCoopδ : Prog := tftSimδ tauCoopδ

/-- `Ts(δ_L)`: the behavioral TFT seeing TauDupoc — runs `L(δ_C)`. -/
def simOfSearchδ (k : Nat) : Prog := tftSimδ (searchOfCoopδ k)

/-- `Tp(δ_L)`: the prover TFT seeing TauDupoc — probes `L(δ_C)`. -/
def searchOfSearchδ (k : Nat) : Prog := probeSearchδ k (searchOfCoopδ k)

/-! ## The σ-players

Weights `wC wD wTs wTp wL : Nat` over an implicit common denominator `W = Σw`;
`θ` is the α-threshold in that scale (`θ = ⌈α·W⌉`); cooperate iff fired mass `≥ θ`.
`TauCooperate`/`TauDefect` are signal-blind constants. -/

/-- TauDupoc's guard list: the δ_L column ("does B, seeing exactly me, cooperate"),
    Löbian guard last. -/
def dupocSig (k wC wD wTs wTp wL : Nat) : GuardList :=
  .cons wC (probe tauCoopδ)
    (.cons wD (probe tauDefectδ)
      (.cons wTs (probe (simOfSearchδ k))
        (.cons wTp (probe (searchOfSearchδ k))
          (.cons wL (probe (TauDupocδ k)) .nil))))

/-- TauTitForTatPf's guard list: the δ_C column ("does B, seeing TauCooperate,
    cooperate") — all shallow, no Löb guard. -/
def tftPfSig (k wC wD wTs wTp wL : Nat) : GuardList :=
  .cons wC (probe tauCoopδ)
    (.cons wD (probe tauDefectδ)
      (.cons wTs (probe simOfCoopδ)
        (.cons wTp (probe (searchOfCoopδ k))
          (.cons wL (probe (searchOfCoopδ k)) .nil))))

/-- The TauCooperate player. -/
def TauCooperate : Prog := .const .C

/-- The TauDefect player. -/
def TauDefect : Prog := .const .D

/-- The TauDupoc player at guard budget `k`, weights `w⃗`, threshold `θ`. -/
def TauDupoc (k θ wC wD wTs wTp wL : Nat) : Prog :=
  .tsearch k (dupocSig k wC wD wTs wTp wL) θ (.const .C) (.const .D)

/-- The TauTitForTatPf player (prover TFT): thresholds PROVABLE cooperation of the
    δ_C column. -/
def TauTFTPf (k θ wC wD wTs wTp wL : Nat) : Prog :=
  .tsearch k (tftPfSig k wC wD wTs wTp wL) θ (.const .C) (.const .D)

/-- Left-spine `.ite` decision tree over weighted action-guards — the behavioral
    mirror of the `tsearch` peel: each level runs one guard; a C-result subtracts the
    weight from the residual threshold; residual 0 commits C; exhaustion commits D. -/
def iteTree : List (Nat × Prog) → Nat → Prog
  | _, 0 => .const .C
  | [], _ => .const .D
  | (w, g) :: rest, θ => .ite g Action.C (iteTree rest (θ - w)) (iteTree rest θ)

/-- TauTitForTatSim's guard list: the δ_C column as `.sim` probes (run the frozen
    instance against itself and read off its action). -/
def tftSimSig (k wC wD wTs wTp wL : Nat) : List (Nat × Prog) :=
  [(wC, .sim (.bot tauCoopδ) (.bot tauCoopδ)),
   (wD, .sim (.bot tauDefectδ) (.bot tauDefectδ)),
   (wTs, .sim (.bot simOfCoopδ) (.bot simOfCoopδ)),
   (wTp, .sim (.bot (searchOfCoopδ k)) (.bot (searchOfCoopδ k))),
   (wL, .sim (.bot (searchOfCoopδ k)) (.bot (searchOfCoopδ k)))]

/-- The TauTitForTatSim player (behavioral TFT): thresholds TRUE cooperation of the
    δ_C column — sim probes yield actions, not provability bits, so `tsearch` does
    not apply and the threshold compiles to the `.ite` decision tree (recorded
    limitation; a `tsim` vote constructor is possible future work). -/
def TauTFTSim (k θ wC wD wTs wTp wL : Nat) : Prog :=
  iteTree (tftSimSig k wC wD wTs wTp wL) θ

end PD.Tau
