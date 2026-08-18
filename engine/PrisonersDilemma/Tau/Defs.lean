import PrisonersDilemma.Dynamics

/-!
# Tau/Defs — the Def-4 TauBot zoo (milestone 1, 2026-08-11; EBot cascade refactor 2026-08-12)

**Definition 4** (TAUBOT_TRANSPARENCY_DESIGN.md, Part III): tau-native agents whose
signal hypotheses AND probes are TauBots, every recursive reference routed through
`proofSearch` — the Löbian machinery breaks the regress that sank the old Def 1
(whose recursion was semantic, via `play`).

**THIS FILE IS THE δ-INSTANCE LAYER ONLY** (the σ-players it used to also carry were
retracted 2026-08-13 and DELETED 2026-08-18 — see the note at the bottom).

The correct Def 4 is the uniform STRUCTURAL SOURCE LIFT τ: lift A's own code
constructor-by-constructor and vote ONCE over the compound per-hypothesis decisions
`TauA(δ_Bᵢ)`, read by EVALUATION. Everything in this file — the probe atom, the
instance templates (`probeSearchδ`, `tftSimδ`, `eδ`), the δ-closure, the quine,
the Gödelian pair — is what that lift CONSUMES, and it survived the retraction
unchanged. The players themselves are built in `Tau/Vectors.lean` on top of the
uniform `tauPlayer` of `Tau/Vote.lean`.

Authoritative plan: `Research/Notes/DEF4_TVOTE_ROADMAP.md`.

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

/-! ## The σ-players — REMOVED 2026-08-18 (Phase 4 of DEF4_TVOTE_ROADMAP)

The guard lists (`dupocSig`/`tftPfSig`/`exploitSig`/`tftSimSig`), the `iteTree`
compiler and the six `.tsearch`-based players that used to live here are GONE. They
implemented the σ-player geometry retracted on 2026-08-13 — per-bot vote shapes, and
in `TauEBot`'s case a threshold INSIDE the cascade, which is a different agent (the
"crowd-exploiter") rather than a lift of EBot.

Their replacement is uniform and lives in `Tau/Vote.lean` + `Tau/Vectors.lean`: ONE
player `tauPlayer v θ` (a `.tvote` action-vote), one peel lemma, one phase theorem,
and per-bot DECISION VECTORS. Everything ABOVE this line — the probe atom, the
instance templates, the δ-closure, the quine — is unchanged and is exactly what the
lift consumes.

Git history holds the removed terms (see the Phase-4 commit); the design record is in
`Research/Notes/DEF4_TVOTE_ROADMAP.md` and the retraction section of
`TAUBOT_TRANSPARENCY_DESIGN.md` Part III. -/

end PD.Tau
