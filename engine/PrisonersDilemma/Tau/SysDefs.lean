import PrisonersDilemma.Tau.Defs

/-!
# Tau/SysDefs — the Def-5 σ-zoo as ONE mutual system (Phase 5, milestone 1)

Design fixed by Colomban 2026-08-13 (`DEF5_SYS_BINDER_ROADMAP.md`, Phase-5
blueprint): probe DIRECTION survives from Def 4, only the SIGNAL blurs —
TauDupoc's bit `i` probes `Bᵢ(σ_Dupoc)` ("would Bᵢ, whose own signal is the blur
of ME, cooperate" — reciprocity with a blurred self-image); TauTFTSim watches
`Bᵢ(σ_Coop)` behaviorally. TauTFTPf is OUT of milestone 1 (zoo decision); TauEBot
is milestone 2 (blocked on the Def-4 τ(EBot) redefinition).

## The system (`sigmaZoo`, 6 members)

| # | member | reads | notes |
|---|---|---|---|
| 0 | `C` | — | signal-ignoring |
| 1 | `D` | — | signal-ignoring |
| 2 | `Dupoc(σ_D)` | probes {0,1,2,3} | slot 2 = ITSELF — **the quine bit φ₁** |
| 3 | `TFTSim(σ_D)` | runs {0,1,4,5} | behavioral watcher of the σ_C column |
| 4 | `Dupoc(σ_C)` | probes {0,1,2,3} | same template as 2, σ_C weights — its L-slot probes MEMBER 2, not itself |
| 5 | `TFTSim(σ_C)` | runs {0,1,4,5} | slot 5 sims ITSELF — regime-dependent divergence (below) |

The same guard list gives the right reference structure for both Dupoc
instances by construction: Dupoc's rule always probes the σ_Dupoc column, so
member 2's L-slot is a self-loop while member 4's L-slot points at member 2.
Top-level players (`TauDupocSys`/`TauTFTSimSys`) are SEPARATE programs over the
closed system (free weights `w⃗`, threshold θ) — outside the binder, they
reference members as `.sys defs j` directly (never `.selfIdx`, which would
dangle).

## Structural findings (established at design time, to be theorem'd)

1. **The Löb core is UNARY.** Without TauTFTPf no prover probes the σ_C column,
   so `probe (Dupoc(σ_C))` never needs to be PROVABLE — only Dupoc(σ_C)'s PLAY
   matters (to the behavioral watchers), and that follows semantically once φ₁'s
   bit is settled. Milestone 1 needs `pblt_engine_id`, not the vector engine
   (which waits for milestone 2 / TauTFTPf's return).
2. **Regime-dependent divergence — a genuine Def-5 finding.** Member 5's slot-5
   guard sims ITSELF: under a full-support σ-signal the behavioral bot observes
   its own reflection, and that sim diverges at every fuel (Def-4's point-mass
   instances could not express this). BUT `iteTree` bakes the threshold
   short-circuit into the TREE (`θ = 0 ↦ .const .C`), so in regimes where the
   residual hits 0 before the self-slot (e.g. `θ ≤ cC + cL` with member 4
   cooperating) member 5 CONVERGES without ever running the divergent guard.
   Outside those regimes its bits are false-but-IRREFUTABLE (no play exists for
   `atomNeg` to cite) — bands where they'd matter are honest OPEN cells.
   Guard-order convention extended: shallow-citable first, Löbian next,
   IRREFUTABLE-RISK LAST.
3. **The one missing proof rule (next engine step).** φ₁'s Löb premise
   `□_k φ₁ → φ₁` needs S to read member 2's `.tsearch` source with the L-bit
   supplied by the box ANTECEDENT — `tsearchCons_t` cannot (it wants an actual
   `Pf k guard` premise). ONE new Pf modal rule is needed
   (`botSysTsearchBranch`: read `.bot (.sys defs i)` with member `i` a
   `.tsearch`; peel prefix discharged by actual cite/refutation premises; ONE
   deferred guard becomes the `□`-antecedent; θ-arithmetic as side conditions) —
   `botSearchStep`'s exact generalization, integrated via the constructor
   playbook (the `sound_upto` arm is the machine gate).
-/

open PD

namespace PD.Tau

/-- The σ_Dupoc-column guard list: probes of members {0,1,2,3} at the given
    weights. GUARD ORDER (fixed by the Löb COST analysis, 2026-08-13):
    shallow-citable (C) first, **Löbian (the member-2 slot) SECOND**, then the
    refutable (D) and irrefutable-risk (behavioral) slots trailing. The Löb
    premise `□_k φ₁ → φ₁` must have an O(log k) transcript (`pblt` needs
    `pm ≪ k`), so the peel prefix before the deferred Löb guard may only contain
    CITED guards (`c_guard` each) — a refutation in the prefix pays the
    `search_f` floor `≥ k` and sinks the chain. With this order the cooperative
    regime `wC < θ ≤ wC + wL` commits at the L-guard without consulting D or Ts
    at all (`botSysTsearchDefer`). Used by BOTH Dupoc instances (members 2 and
    4) — with σ_D and σ_C weights respectively — and, over `.sys` references,
    by the top player. -/
def sysDupocSig (wC wD wL wT : Nat) : GuardList :=
  .cons wC (probe (.selfIdx 0))
    (.cons wL (probe (.selfIdx 2))
      (.cons wD (probe (.selfIdx 1))
        (.cons wT (probe (.selfIdx 3)) .nil)))

/-- The behavioral watch list over the σ_C column (members {0,1,4,5}): run each
    frozen member against itself and read off its action. Slot order: constants,
    then the Löb-gated `Dupoc(σ_C)`, then the DIVERGENT-risk self-sim slot LAST
    (never reached when the residual threshold hits 0 first). -/
def sysTFTWatch (wC wD wL wT : Nat) : List (Nat × Prog) :=
  [(wC, .sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))),
   (wD, .sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))),
   (wL, .sim (.bot (.selfIdx 4)) (.bot (.selfIdx 4))),
   (wT, .sim (.bot (.selfIdx 5)) (.bot (.selfIdx 5)))]

/-- **THE σ-ZOO** — the milestone-1 Def-5 instance closure as one mutual system.
    `k` = proof budget; `θ₂ θ₃ θ₄ θ₅` = the four non-constant members'
    thresholds; `dC dD dL dT` = the σ_Dupoc signal's weights; `cC cD cL cT` =
    the σ_Coop signal's weights. -/
def sigmaZoo (k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat) : ProgList :=
  .cons (.const .C)                                                        -- 0
    (.cons (.const .D)                                                     -- 1
      (.cons (.tsearch k (sysDupocSig dC dD dL dT) θ₂ (.const .C) (.const .D))  -- 2
        (.cons (iteTree (sysTFTWatch dC dD dL dT) θ₃)                      -- 3
          (.cons (.tsearch k (sysDupocSig cC cD cL cT) θ₄ (.const .C) (.const .D))  -- 4
            (.cons (iteTree (sysTFTWatch cC cD cL cT) θ₅)                  -- 5
              .nil)))))

/-- The top-level Def-5 TauDupoc player: probes the σ_D column of a CLOSED
    system (members as `.sys defs j` — the player lives outside the binder) at
    free weights `w⃗` and threshold `θ`. The received signal (about the
    opponent) supplies `w⃗`; the probed hypotheses carry the blur of the player
    itself, per the fixed probe direction. -/
def TauDupocSys (defs : ProgList) (k wC wD wL wT θ : Nat) : Prog :=
  .tsearch k
    (.cons wC (probe (.sys defs 0))
      (.cons wL (probe (.sys defs 2))
        (.cons wD (probe (.sys defs 1))
          (.cons wT (probe (.sys defs 3)) .nil))))
    θ (.const .C) (.const .D)

/-- The top-level Def-5 behavioral TFT: watches the σ_C column of a closed
    system at free weights and threshold. -/
def TauTFTSimSys (defs : ProgList) (wC wD wL wT θ : Nat) : Prog :=
  iteTree
    [(wC, .sim (.bot (.sys defs 0)) (.bot (.sys defs 0))),
     (wD, .sim (.bot (.sys defs 1)) (.bot (.sys defs 1))),
     (wL, .sim (.bot (.sys defs 4)) (.bot (.sys defs 4))),
     (wT, .sim (.bot (.sys defs 5)) (.bot (.sys defs 5)))] θ

/-! ## Structural sanity (definitional — the reference wiring is exactly as
designed) -/

section Sanity

variable (k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)

/-- Member lookup lands as tabled. -/
example : (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT).get? 0
    = some (.const .C) := rfl
example : (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT).get? 2
    = some (.tsearch k (sysDupocSig dC dD dL dT) θ₂ (.const .C) (.const .D)) := rfl
example : (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT).get? 5
    = some (iteTree (sysTFTWatch cC cD cL cT) θ₅) := rfl
example : (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT).get? 6 = none := rfl

/-- `sysClose` closes a probed reference to the closed member — the quine bit's
    closed form: member 2's L-guard becomes a probe of `.sys … 2` ITSELF. -/
example (defs : ProgList) :
    (probe (.selfIdx 2)).sysClose defs = probe (.sys defs 2) := rfl

/-- The behavioral self-sim slot closes to a sim of the member itself. -/
example (defs : ProgList) :
    Prog.sysClose defs (.sim (.bot (.selfIdx 5)) (.bot (.selfIdx 5)))
      = .sim (.bot (.sys defs 5)) (.bot (.sys defs 5)) := rfl

/-- Positivity (Def-5 convention 6, milestone-1 form): every prover guard in the
    zoo is a positive cooperation atom — no `.neg` anywhere above a
    sys-referencing atom, so the shared sentence system is monotone and the
    anti-diagonal inconsistency has no entry point. -/
def GuardList.allCoopAtoms : GuardList → Bool
  | .nil => true
  | .cons _ (.plays _ _ .C) rest => allCoopAtoms rest
  | .cons _ _ _ => false

example : GuardList.allCoopAtoms (sysDupocSig dC dD dL dT) = true := rfl

end Sanity

end PD.Tau
