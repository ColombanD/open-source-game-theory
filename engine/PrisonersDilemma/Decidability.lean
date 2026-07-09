import PrisonersDilemma.Decidability.T31EngineDecider
import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T43ModestUniverse
import PrisonersDilemma.Decidability.T44BoundedDecider
import PrisonersDilemma.Decidability.T45CertReads
import PrisonersDilemma.Decidability.T46LogicSpace
import PrisonersDilemma.Decidability.T47Stabilization
import PrisonersDilemma.Decidability.T48CutRelevance
import PrisonersDilemma.Decidability.T49TreeSubstrate
import PrisonersDilemma.Decidability.T50InstanceLob
import PrisonersDilemma.Decidability.T51Regress
import PrisonersDilemma.Decidability.T52DecInst
import PrisonersDilemma.Decidability.T53StabInst
import PrisonersDilemma.Decidability.T54ZooCert

/-!
# Decidability — the T3.2c/T4 chain (promoted 2026-07-03 from `Research/Spikes/transcript/`)

The engine's computability results, on Lean's three standard axioms throughout, no sorries.
Detailed history and design rationale: `Research/Notes/DECIDABILITY_ROADMAP.md` (the STATUS
table at its top maps every result to its file). The modules keep their milestone names
(`T31`, `T42`, …) and namespaces — the roadmap and the paper cross-reference them.

**The story in five steps:**

1. **`Provable` is absolutely SEMIDECIDABLE** (`T31EngineDecider`, §7–8):
   `decFull` is a verified computable enumerator with
   `Provable k φ ↔ ∃ fuel, decFull fuel k φ = true` — logic and atom layers tied by fuel
   stratification, no oracle, no hypothesis.
2. **Search bots RUN** (`T31EngineDecider`, §9): `evalG` is a computable evaluator whose
   3-valued guard commits soundly in BOTH polarities — `true` via `decFull`, `false` via a
   DERIVABLE refutation plus soundness/consistency. Every commit equals the classical
   `eval` at the same fuel (`evalG_sound`); `#eval` demos print real outcomes, answering
   `none` only at the Löb boundary. Supersedes `ComputableEval/evalC`.
3. **The gate-parametric strata** (`T42ProvableB`): `ProvableG G` gates the six
   conclusion-absent premise formulas; `Provable ↔ ∃ N, ProvableB N` (every derivation is
   finitely-cut); `CutRelevance` states THE remaining open conjecture (T4.1b).
4. **The modest universe** (`T43ModestUniverse`): bots whose substitution positions are
   `.self`/`.opp`/frozen — the WHOLE zoo, each by `rfl` — have finite query universes
   closed under the evaluation dynamics.
5. **DECIDABILITY over the zoo universe** (`T44`–`T47`): the bounded decider `decB`
   (sound + complete for `ProvableG (modestGate N)`), the certificate layer's read
   interface (`CertRead`), the global query universe with its non-circular budget ceiling,
   and the countP stabilization give
   `ProvableG (modestGate N) k φ ↔ decB N |SL| k φ = true` — a terminating decision
   procedure with a computable fuel bound (`decideProvableG : Decidable …`).

**Open (T4.1b, deferred):** `CutRelevance` — a computable `N₀` with
`Provable k φ → ProvableG (modestGate (N₀ k φ)) k φ`. Given it, `proofSearch` becomes
decidable and `eval` computable outright; if it fails, `Provable` is a candidate
undecidable bounded-provability predicate. Also deferred: rewiring `proofSearch` (its right
form depends on how the conjecture resolves — see the roadmap's T5 notes).
-/

namespace PD.Decidability

-- The headline API under one roof (implementations keep their milestone namespaces).
export PD.T31 (decFull decFull_sound decFull_complete Provable_iff_decFull
  GuardSound guardFull guardFast guardFull_sound guardFast_sound
  guardFull_converges_pos guardFull_converges_neg
  evalG evalG_sound playG playG_sound outcomeG outcomeG_sound)
export PD.T42 (maxLitP maxLitF PlaysProofG AtomProvableG ProvableG
  litGate PlaysProofB AtomProvableB ProvableB
  ProvableG_sound ProvableB_sound ProvableG_monoG ProvableB_monoN
  Provable_exists_ProvableB Provable_iff_exists_ProvableB
  CutRelevance Provable_iff_ProvableB_of_cutRelevance)
export PD.T43 (closedP closedF modestP modestF argOK subsP subsF playsArgsF
  certU players guardU step_sim step_search guardU_args)
export PD.T44 (modestGate cutOKb stepB decB decB_sound decB_complete decB_mono
  ProvableG_modest_iff_decB)
export PD.T45 (CertRead decCertG_congr certOG_congr certRead_mem_guardU)
export PD.T46 (LU allowedProgs GF certRead_budget certRead_mem_GF)
export PD.T47 (SL ZS InvP stepB_congr decB_bound
  ProvableG_iff_decB_bound decideProvableG)

end PD.Decidability
