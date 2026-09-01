import PrisonersDilemma.Tau.Spec

/-!
# Tau/Roster — the cast list of the six-template tau zoo

The one structural difference from the base-bot layout, and why this file must
exist BEFORE the per-bot files: a base bot references another bot by IMPORTING its
finished term, but a tau spec references other bots by NAME in a shared index (a
stage target like `.name .coop`), resolved later by the compiler — that indirection
is what makes mutual reference expressible at all. So the roster is declared first,
each `Tau/Bots/<TauBot>.lean` writes its spec against it, and `Tau/Zoo.lean` glues
the rows into the zoo. Adding a bot touches exactly: one constructor here, one new
bot file, one arm in `Zoo.lean`.
-/

namespace PD.Tau

/-- The templates. (A readable enum, not `Fin n` — roadmap open question 5.)
    Extended 2026-08-18 with every base bot liftable WITHOUT `.sys`: `just`
    (JustBot — third-party prover, target Dupoc), `obot` (OBot — the behavioral
    defection-detector), `guardian` (GuardianBot — the norm enforcer, the zoo's
    first `test = .D` prover). Excluded and why: CupodBot/PrudentBot/MirrorBot/
    LegibleBot/OptimBot are self-probers (the mutual-quine wall — `.sys`);
    CIMCIC/DIMCID (implication guards), WaryBot (`.neg`), CupodTrollBot (`.eq`)
    were outside the cascade fragment. `cupodTroll` (CupodTrollBot — the identity
    checker, `.eq .opp (.bot CupodBot)`) was ADDED 2026-08-20: it is the ONLY
    remaining bot whose guard names a LITERAL third party rather than the opponent's
    view of me, so it is the only one liftable without `.sys`.

    **`cupod` (CupodBot) ADDED 2026-08-20 — the FIRST bot through the `.sys`
    binder.** It self-probes (`.plays .opp .self D`), so with TauDupoc and TauJust
    already self-probing it forms genuine 2-cycles; `instGo` now emits the
    mutual-fixpoint system for those pairs instead of failing to terminate.

    **`cimcic` (CIMCIC) ADDED 2026-08-21 — the first `.impl`-guard bot, and the
    THIRD self-prober.** Its `proveImpl` stage targets `self`, so it entangles with
    BOTH `dupoc` and `cupod`: three 2-cycles in the zoo, each compiled to its own
    2-member `.sys` system. The `Mode.proveImpl` machinery built for it on
    2026-08-20 (before its self-probing was recognized) is finally consumed.

    **Correction recorded 2026-08-20 (Gate D1 caught it):** CIMCIC and DIMCID
    (`.impl (.plays .self .opp _) (.plays .opp .self _)`) and WaryBot
    (`.neg (.plays .opp .self C)`) all mention BOTH `.self` and `.opp`, so they are
    SELF-PROBERS and belong to the `.sys`-blocked class, not the fragment class. The
    `Mode.proveImpl` machinery for CIMCIC's guard shape is LANDED and correct — it
    simply cannot be used until `.sys` provides the term.

    **`dimcid` (DIMCID) ADDED 2026-08-21 — CIMCIC's polarity twin, the FOURTH
    self-prober.** Its guard is the same implication with an ASYMMETRIC consequent
    ("if I cooperate, they DEFECT"), which needed the new `Mode.proveImplD`; it
    entangles with `dupoc`, `cupod` and `cimcic`, giving the zoo four 2-cycles.
    Unlike CIMCIC's `implRefl` diagonal, its own is a genuine Löb fixpoint on
    defection. `dbot` (DBot — the defection-punisher: one
    run-stage watching δ_D, trusting by default) was ADDED 2026-08-19 once its
    blocker cleared: its δ_L cell needs a frozen run-stage player sim-embedding a
    floor-priced searcher, which is exactly `no_provable_botRunStage_C`, the
    single-stage twin of the embedded-floor census the run-mode EBot fix forced.

    **`maxconfidence` (MaxConfidenceBot) ADDED 2026-08-27 — the first NATIVE player, and
    the first roster member that is NOT the lift of a base bot.** A tau player is a
    (bit row, aggregator) pair; every lift aggregates by `sum ≥ θ`, MaxConfidenceBot
    aggregates by `max ≥ θ` ("cooperate iff some SINGLE hypothesis carrying at least
    θ of the signal provably cooperates with me" — `Tau/Bots/TauMaxConfidence.lean`).
    Its per-hypothesis TEST is Dupoc's (`tauMaxConfidenceSpec = tauDupocSpec`), so in the
    HYPOTHESIS role — what others see at point mass — it IS Dupoc: `inst` depends only
    on specs, so its instances are Dupoc's by `rfl` except at the `maxconfidence × dupoc`
    pair, where two Dupoc-spec self-probers meet in a symmetric `.sys` system
    (mutual Löb, C). Its row is Dupoc's row; the aggregator is the novelty, and it is
    invisible at point mass (the anchor). The roster slot exists so the app's EGT zoo
    can contain it as a hypothesis with kernel-certified bits.

    **`minconfidence` (MinConfidenceBot) ADDED 2026-09-01 — the second native player,
    MaxConfidenceBot's C/D-transposition dual.** Same test (Dupoc's:
    `tauMinConfidenceSpec = tauDupocSpec`), the MIN / worst-case aggregator
    (`Tau/Vote.lean::minPlayer`): cooperate iff NO single hypothesis carrying at
    least θ of the signal on its own provably defects — the Gilboa–Schmeidler
    pessimist to MaxConfidenceBot's optimist. In the hypothesis role it too IS Dupoc:
    a THIRD Dupoc-spec self-prober, whose entangled pairs (with `dupoc` AND with
    `maxconfidence`) all compile to the SAME symmetric `.sys` term `cfdSys` —
    `sysGo` never consults the template name for this spec — so every mutual-Löb
    lemma of `TauMaxConfidence/Helpers.lean` covers them by `rfl` and no new Löb work
    exists. Its row is Dupoc's row; only the aggregator differs. -/
inductive Tmpl
  | coop | defect | tftSim | tftPf | dupoc | ebot | just | obot | guardian | dbot
  | cupodTroll | cupod | cimcic | dimcid | prudent | maxconfidence | minconfidence | mirror
deriving DecidableEq, Repr

/-- The canonical hypothesis order — the entry order of every decision vector. -/
def tauOrder : List Tmpl :=
  [.coop, .defect, .tftSim, .tftPf, .dupoc, .ebot, .just, .obot, .guardian, .dbot,
   .cupodTroll, .cupod, .cimcic, .dimcid, .prudent, .maxconfidence, .minconfidence, .mirror]

/-- `tauOrder` without its last slot — the PREFIX row order for a template whose own
    diagonal diverges (τ(Mirror)): the vote never reaches the last entry in the C-regime,
    so its row is stated over the prefix and the app records the missing slot as `N`. -/
def tauOrderInit : List Tmpl :=
  [.coop, .defect, .tftSim, .tftPf, .dupoc, .ebot, .just, .obot, .guardian, .dbot,
   .cupodTroll, .cupod, .cimcic, .dimcid, .prudent, .maxconfidence, .minconfidence]

theorem tauOrder_eq : tauOrder = tauOrderInit ++ [.mirror] := rfl

end PD.Tau
