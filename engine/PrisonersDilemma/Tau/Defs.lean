import PrisonersDilemma.Dynamics

/-!
# Tau/Defs — the Def-4 TauBot zoo (milestone 1, 2026-08-11; EBot cascade refactor 2026-08-12)

**Definition 4** (TAUBOT_TRANSPARENCY_DESIGN.md, Part III): tau-native agents whose
signal hypotheses AND probes are TauBots, every recursive reference routed through
`proofSearch` — the Löbian machinery breaks the regress that sank the old Def 1
(whose recursion was semantic, via `play`).

**⚠ RETRACTION (2026-08-13) — the σ-PLAYER LAYER BELOW IS OUTDATED AND WRONG.**
The correct Def 4 is the uniform STRUCTURAL SOURCE LIFT τ (design note, Part III
retraction section): lift A's own code constructor-by-constructor and vote ONCE
over the compound per-hypothesis decisions `TauA(δ_Bᵢ)` — under which Def 4
COINCIDES with Def 3 (large k, terminating cells). The `TauEBot` σ-player below
moves θ INSIDE the cascade (one vote per STAGE) and is NOT τ(EBot) — it is a
different agent, the "crowd-exploiter"; its window / (D,D)-self-play phase claims
are retracted. TauDupoc/TauTFTPf/TauTFTSim conform to τ only by accident of
having a single decision point. The δ-INSTANCE layer (probe, `probeSearchδ`,
`tftSimδ`, `eδ`, the quine, the Gödelian pair) is CORRECT under the new reading
and is what the refined τ consumes; the σ-players await redefinition.

Six-template zoo: TauCooperate (`C`), TauDefect (`D`), TauDupoc (`L`),
TauTitForTatSim (`Ts`), TauTitForTatPf (`Tp`), TauEBot (`E`). Conventions:

* **Signals are weighted lists over template names**; a probe re-instantiates its
  hypothesis at a POINT-MASS signal. So the probed objects are the finite instance
  family `B(δ_T)`, closed terms defined below.
* **Probe atom** (`probe`): the instance is `.bot`-frozen (the subst barrier — a bare
  slot would have the enclosing player's `subst` rewrite the instance's internal
  `.self`) and asked to play C **against itself** (the second slot is inert for
  `.opp`-free programs; instance-vs-itself is the canonical closed choice).
* **Tau programs are `.opp`-free** — that IS partial transparency: the signal replaces
  the wire to the actual opponent. Consequently every tau player is extensionally
  constant (its play depends on its signal only), and the outcome matrix factors
  through the play theorems.
* **Guard order: Löbian guards LAST**, so low-budget/low-threshold regimes commit via
  the stepwise short-circuits before ever consulting the walled Löb guard.
* **Prover instances stay `.search` (singleton/cascade)** (a point-mass `tsearch`
  degenerates to `.search`), keeping the modal reading rules
  (`searchBranch`/`botSearchStep`) applicable; only the σ-players (never probed by
  anyone) use `.tsearch`.
* **Each template's instance family is its own point-mass instantiation** — the
  coherence rule the 2026-08-12 refactor restored. The zoo's instances resolve
  through THREE columns: δ_C ("does B, seeing TauCooperate, cooperate" — both TFTs
  and TauEBot's reciprocity stage), δ_D ("does B, seeing TauDefect, cooperate" —
  TauEBot's exploit stage), and δ_L ("does B, seeing TauDupoc, cooperate" —
  TauDupoc). No δ_E column exists anymore: TauEBot's cascade probes only δ_D/δ_C,
  which is exactly what grounds the whole family without stipulations (a δ_E-probing
  EBot and the δ_L-probing Dupoc would form a mutual-quine 2-cycle the language
  cannot express — the root cause of the retired 2026-08-11 stipulations).

**The instance columns and their bits** (`P` = provable at the probing budget,
large k):

| hypothesis | δ_C column | δ_D column | δ_L column |
|---|---|---|---|
| Coop   | C, P | C, P | C, P |
| Defect | D    | D    | D    |
| TFTSim | C, P | D    | C, P |
| TFTPf  | C, P | D    | C, P |
| Dupoc  | C, P | D    | C, P (quine, Löb) |
| EBot   | D    | D    | **C, UNPROVABLE (floor)** |

The starred cell is the tau image of base `outcome_DupocBot_vs_EBot = (D, C)`:
`E(δ_L)` really cooperates, but its cooperation sits behind a FAILED exploit-probe,
so any certificate pays the `search_f` floor `> k` and TauDupoc's budget-`k` probe
honestly reads 0 (`Base/Exclusion.no_provable_botSearcherElse_tail`). So the
provable-cooperation masses are: δ_C `wC+wTs+wTp+wL`, δ_D `wC`, δ_L `wC+wTs+wTp+wL`.

Everything grounds in a DAG except the single `L(δ_L)` self-loop, which the `.self`
quine cuts.
-/

open PD

namespace PD.Tau

/-- Def-4 probe atom for a hypothesis instance `I` (frozen, vs itself). -/
def probe (I : Prog) : Formula := .plays (.bot I) (.bot I) Action.C

/-- One-hypothesis PROVER instance: cooperate iff the probe of `I` is provable within
    `k`. This is `B(δ_T)` for both single-probe prover templates (`L` and `Tp`) —
    which template it "came from" is recorded only by WHICH instance it is applied
    to. -/
def probeSearchδ (k : Nat) (I : Prog) : Prog :=
  .search k (probe I) (.const .C) (.const .D)

/-- One-hypothesis BEHAVIORAL instance (`Ts(δ_T)`): RUN the frozen hypothesis against
    itself and copy cooperation. Sees TRUE plays, not provable ones. -/
def tftSimδ (I : Prog) : Prog :=
  .ite (.sim (.bot I) (.bot I)) Action.C (.const .C) (.const .D)

/-- One-hypothesis EBOT instance (`E(δ_T)`) — the tau lift of base EBot's decision
    CASCADE: if the hypothesis provably cooperates with the defector (exploitable),
    defect; else if it provably cooperates with the cooperator, cooperate; else
    defect. `I_D` is the hypothesis's δ_D instance, `I_C` its δ_C instance. (Base
    EBot's third, MirrorBot branch does not propagate: no tau instance ever runs
    Mirror against itself.)

    THE load-bearing consequence: when `I_D`'s cooperation is false-or-unprovable
    and `I_C`'s is provable, this instance PLAYS C **through a failed search** — so
    its own cooperation certificate carries the `search_f` floor and is invisible to
    any probe at budget ≤ k. That is the faithful mechanism of base
    `DupocBot vs EBot = (D, C)`, replacing the 2026-08-11 stipulation that modelled
    `E(δ_L)` as a provable cooperator (caught in review: Def 4 routes every bit
    through `proofSearch`, so a floor-priced cooperation must read 0). -/
def eδ (k : Nat) (I_D I_C : Prog) : Prog :=
  .search k (probe I_D) (.const .D)
    (.search k (probe I_C) (.const .C) (.const .D))

/-- `L(δ_L)` — the quine: TauDupoc whose point-mass hypothesis is ITSELF. The only
    cyclic instance; `.self` is the built-in quine (an inductive term cannot contain
    its own frozen source, so the frozen-instance pattern of `probeSearchδ` is
    unwritable here). Running anywhere, `subst` closes the guard to the
    opponent-independent Löb sentence `.plays me me .C` with `me` the enclosing
    player — `.bot (TauDupocδ k)` when probed frozen, which is the fixpoint the
    Certs Löb lemma closes via `botSearchStep` + `pblt_engine_id`. -/
def TauDupocδ (k : Nat) : Prog :=
  .search k (.plays .self .self Action.C) (.const .C) (.const .D)

/-! ## The δ-instance closure -/

/-- `C(δ_T)` for every `T` — TauCooperate ignores its signal. -/
def tauCoopδ : Prog := .const .C

/-- `D(δ_T)` for every `T`. -/
def tauDefectδ : Prog := .const .D

/-- `L(δ_C) = Tp(δ_C)`: a prover seeing TauCooperate — guard trivially provable. -/
def searchOfCoopδ (k : Nat) : Prog := probeSearchδ k tauCoopδ

/-- `Ts(δ_C)`: the behavioral TFT seeing TauCooperate. -/
def simOfCoopδ : Prog := tftSimδ tauCoopδ

/-- `L(δ_D) = Tp(δ_D)`: a prover seeing TauDefect — probes `D(δ_·) = tauDefectδ`,
    refutable, so it DEFECTS. (Formerly named `searchOfEδ` and stipulated as
    "a prover seeing TauEBot"; under the cascade refactor the term keeps only its
    honest role — the δ_D column entry TauEBot's exploit stage consults.) -/
def searchOfDefectδ (k : Nat) : Prog := probeSearchδ k tauDefectδ

/-- `Ts(δ_D)`: the behavioral TFT seeing TauDefect — runs `D(δ_C) = .const D` and
    copies the defection. (Formerly named `simOfEδ`, same term, honest role.) -/
def simOfDefectδ : Prog := tftSimδ tauDefectδ

/-- `Ts(δ_L)`: the behavioral TFT seeing TauDupoc — runs `L(δ_C)`. -/
def simOfSearchδ (k : Nat) : Prog := tftSimδ (searchOfCoopδ k)

/-- `Tp(δ_L)`: the prover TFT seeing TauDupoc — probes `L(δ_C)`. -/
def searchOfSearchδ (k : Nat) : Prog := probeSearchδ k (searchOfCoopδ k)

/-! ### TauEBot's instances (the SEPARATING bot; cascade-faithful since 2026-08-12)

`TauEBot` exists to make Def 3 and Def 4 actually differ. Base EBot is the zoo's
exploiter — a non-monotone strategy (it defects against BOTH the exploitable and
the unreciprocating) — and the cascade lift preserves exactly that structure, which
Def 3's outcome-averaged monotone thresholds cannot express. -/

/-- `E(δ_C)`: TauEBot seeing TauCooperate. **DEFECTS via a FIRING exploit-probe**:
    `C(δ_D) = tauCoopδ` provably cooperates with the defector, so the first guard
    fires and the then-branch `.const D` runs — base
    `EBot vs CooperateBot = (D, C)`, mechanism-faithfully (the 2026-08-11 version
    got this bit right but through a stipulated refutable guard). This is the
    hypothesis the δ_C-column bots (both TFTs, and TauEBot's own reciprocity stage)
    hold about TauEBot. -/
def eOfCoopδ (k : Nat) : Prog := eδ k tauCoopδ tauCoopδ

/-- `E(δ_D)`: TauEBot seeing TauDefect. **DEFECTS** — both probes are about
    `tauDefectδ`, false, so the cascade falls through to the final `.const D`
    (base `EBot vs DefectBot = (D, D)`). The δ_D-column entry TauEBot's own
    exploit stage holds about itself — grounded, NO quine needed. -/
def eOfDefectδ (k : Nat) : Prog := eδ k tauDefectδ tauDefectδ

/-- `E(δ_L)`: TauEBot seeing TauDupoc — the hypothesis TauDupoc holds about TauEBot.

    **COOPERATES — UNPROVABLY.** The exploit-probe of `L(δ_D)` (Dupoc is not
    exploitable: `searchOfDefectδ` plays D) FAILS, and the reciprocity-probe of
    `L(δ_C)` (`searchOfCoopδ` provably cooperates) fires: play C, matching base
    `EBot vs DupocBot = (C, D)`. But the cooperation sits behind the failed first
    search, so every certificate of it costs `> k`
    (`no_provable_botSearcherElse_tail`) and TauDupoc's budget-`k` probe reads 0 —
    the faithful tau image of the base floor, and the bit the 2026-08-11
    stipulation (`probeSearchδ k tauCoopδ`, a PROVABLE cooperator) got wrong. -/
def eOfSearchδ (k : Nat) : Prog := eδ k (searchOfDefectδ k) (searchOfCoopδ k)

/-! ## The σ-players

Weights `wC wD wTs wTp wL wE : Nat` over an implicit common denominator `W = Σw`;
`θ` is the α-threshold in that scale (`θ = ⌈α·W⌉`); a vote stage fires iff its fired
mass `≥ θ`. `TauCooperate`/`TauDefect` are signal-blind constants. -/

/-- TauDupoc's guard list: the δ_L column ("does B, seeing exactly me,
    cooperate"), Löbian guard last. Provable bits: everything but Defect AND EBot —
    `E(δ_L)` cooperates, but only floor-priced, so its bit is honestly 0 and the
    fired mass is `wC + wTs + wTp + wL`. -/
def dupocSig (k wC wD wTs wTp wL wE : Nat) : GuardList :=
  .cons wC (probe tauCoopδ)
    (.cons wD (probe tauDefectδ)
      (.cons wTs (probe (simOfSearchδ k))
        (.cons wTp (probe (searchOfSearchδ k))
          (.cons wE (probe (eOfSearchδ k))
            (.cons wL (probe (TauDupocδ k)) .nil)))))

/-- The δ_C-column guard list ("does B, seeing TauCooperate, cooperate") — all
    shallow, no Löb guard. Shared by TauTitForTatPf (its whole strategy) and by
    TauEBot (its reciprocity stage). EBot's own bit is 0 here (`eOfCoopδ` exploits
    a cooperator), so the fired mass is `wC + wTs + wTp + wL`. -/
def tftPfSig (k wC wD wTs wTp wL wE : Nat) : GuardList :=
  .cons wC (probe tauCoopδ)
    (.cons wD (probe tauDefectδ)
      (.cons wTs (probe simOfCoopδ)
        (.cons wTp (probe (searchOfCoopδ k))
          (.cons wE (probe (eOfCoopδ k))
            (.cons wL (probe (searchOfCoopδ k)) .nil)))))

/-- TauEBot's EXPLOIT guard list: the δ_D column ("does B, seeing TauDefect,
    cooperate"). Only the Coop hypothesis fires — everything else defects against
    a defector — so the fired mass is `wC`. -/
def exploitSig (k wC wD wTs wTp wL wE : Nat) : GuardList :=
  .cons wC (probe tauCoopδ)
    (.cons wD (probe tauDefectδ)
      (.cons wTs (probe simOfDefectδ)
        (.cons wTp (probe (searchOfDefectδ k))
          (.cons wE (probe (eOfDefectδ k))
            (.cons wL (probe (searchOfDefectδ k)) .nil)))))

/-- The TauCooperate player. -/
def TauCooperate : Prog := .const .C

/-- The TauDefect player. -/
def TauDefect : Prog := .const .D

/-- The TauDupoc player at guard budget `k`, weights `w⃗`, threshold `θ`. -/
def TauDupoc (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  .tsearch k (dupocSig k wC wD wTs wTp wL wE) θ (.const .C) (.const .D)

/-- The TauEBot player — base EBot's cascade lifted to the vote level, as a
    NESTED `tsearch`: if the signal's exploitable mass (δ_D column) reaches θ,
    defect; else if its reciprocating mass (δ_C column) reaches θ, cooperate; else
    defect. At a point-mass signal this is exactly the instance cascade `eδ`, so
    the σ-player and its instance family finally cohere (the 2026-08-11 version
    was a δ_E-probing reciprocity vote — Def 2's rejected geometry — whose
    instance family could only be stipulated, since two self-probing bots form an
    inexpressible mutual-quine 2-cycle).

    Both stages share the caution threshold θ (one α, two questions). The
    resulting cooperation region is a WINDOW, `wC < θ ≤ wC + wTs + wTp + wL`:
    TauEBot defects at BOTH extremes — a non-monotone α-profile no Def-3 lift can
    express, and the honest structural separation between the definitions.

    **[RETRACTED 2026-08-13: this is the CROWD-EXPLOITER, not τ(EBot). The source
    lift votes ONCE over the compound per-hypothesis cascade decisions; τ(EBot)'s
    bits on this zoo are Coop 0, Defect 0, TFT 1, Dupoc 1 — a one-sided boundary
    at `wTs + wTp + wL`, NO window, and no Def3/Def4 separation. Kept, with its
    kernel-true theorems, until the σ-player redefinition.]** -/
def TauEBot (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  .tsearch k (exploitSig k wC wD wTs wTp wL wE) θ (.const .D)
    (.tsearch k (tftPfSig k wC wD wTs wTp wL wE) θ (.const .C) (.const .D))

/-- The TauTitForTatPf player (prover TFT): thresholds PROVABLE cooperation of
    the δ_C column. -/
def TauTFTPf (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  .tsearch k (tftPfSig k wC wD wTs wTp wL wE) θ (.const .C) (.const .D)

/-- Left-spine `.ite` decision tree over weighted action-guards — the behavioral
    mirror of the `tsearch` peel: each level runs one guard; a C-result subtracts
    the weight from the residual threshold; residual 0 commits C; exhaustion
    commits D. -/
def iteTree : List (Nat × Prog) → Nat → Prog
  | _, 0 => .const .C
  | [], _ => .const .D
  | (w, g) :: rest, θ => .ite g Action.C (iteTree rest (θ - w)) (iteTree rest θ)

/-- TauTitForTatSim's guard list: the δ_C column as `.sim` probes (run the
    frozen instance against itself and read off its action). -/
def tftSimSig (k wC wD wTs wTp wL wE : Nat) : List (Nat × Prog) :=
  [(wC, .sim (.bot tauCoopδ) (.bot tauCoopδ)),
   (wD, .sim (.bot tauDefectδ) (.bot tauDefectδ)),
   (wTs, .sim (.bot simOfCoopδ) (.bot simOfCoopδ)),
   (wTp, .sim (.bot (searchOfCoopδ k)) (.bot (searchOfCoopδ k))),
   (wE, .sim (.bot (eOfCoopδ k)) (.bot (eOfCoopδ k))),
   (wL, .sim (.bot (searchOfCoopδ k)) (.bot (searchOfCoopδ k)))]

/-- The TauTitForTatSim player (behavioral TFT): thresholds TRUE cooperation of
    the δ_C column — sim probes yield actions, not provability bits, so
    `tsearch` does not apply and the threshold compiles to the `.ite` decision
    tree (recorded limitation; a `tsim` vote constructor is possible future
    work). -/
def TauTFTSim (k θ wC wD wTs wTp wL wE : Nat) : Prog :=
  iteTree (tftSimSig k wC wD wTs wTp wL wE) θ

end PD.Tau
