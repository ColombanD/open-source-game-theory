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

    **Correction recorded 2026-08-20 (Gate D1 caught it):** CIMCIC and DIMCID
    (`.impl (.plays .self .opp _) (.plays .opp .self _)`) and WaryBot
    (`.neg (.plays .opp .self C)`) all mention BOTH `.self` and `.opp`, so they are
    SELF-PROBERS and belong to the `.sys`-blocked class, not the fragment class. The
    `Mode.proveImpl` machinery for CIMCIC's guard shape is LANDED and correct — it
    simply cannot be used until `.sys` provides the term. `dbot` (DBot — the defection-punisher: one
    run-stage watching δ_D, trusting by default) was ADDED 2026-08-19 once its
    blocker cleared: its δ_L cell needs a frozen run-stage player sim-embedding a
    floor-priced searcher, which is exactly `no_provable_botRunStage_C`, the
    single-stage twin of the embedded-floor census the run-mode EBot fix forced. -/
inductive Tmpl
  | coop | defect | tftSim | tftPf | dupoc | ebot | just | obot | guardian | dbot
  | cupodTroll | cupod
deriving DecidableEq, Repr

/-- The canonical hypothesis order — the entry order of every decision vector. -/
def tauOrder : List Tmpl :=
  [.coop, .defect, .tftSim, .tftPf, .dupoc, .ebot, .just, .obot, .guardian, .dbot,
   .cupodTroll, .cupod]

end PD.Tau
