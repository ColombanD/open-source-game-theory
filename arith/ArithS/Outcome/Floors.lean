import ArithS.Outcome.Floor
import ArithS.Outcome.Attr
import ArithS.Cells.FloorDichotomy
import ArithS.Cells.PrudentLoose

/-!
# ArithS.Outcome.Floors — the 26 genuine floors, engine side, on the `FloorSpecA` template

One `@[floorA]` theorem per `dich_<L>_vs_<R>` of `Cells/FloorDichotomy.lean`:

    @[floorA] theorem outcome_<L>_vs_<R>_floor : FloorSpecA (bot L) (bot R) (fun k ↦ <hinge>) (some (a, b))

with `(a, b)` the ENGINE's value (`Research/Notes/ROUTE_B_CENSUS.md`, column "engine") and `<hinge>` written
inline in the `□[k] φ` notation. For the single-hinge cells the hinge is the dichotomy's own `A_k`; for the
NESTED cells (the prudence floors and the bistable-modulo-reflection pairs) it is the boolean combination of the
outer hinges under which the engine's value is forced — read off the `dich_` statement, so that `¬ hinge k` is
exactly the branch the dichotomy settles at the engine's value. Where `Cells/PrudentLoose.lean` has the prudence
hinge discharged (`dich_…_prudenceFound`) or the partner's side built (`dich_PrudentBot_vs_EBot_full`), that
sharper dichotomy is the one used, so the hinge names only the questions `S'` genuinely leaves open.

Validated by `#check_floorA_theorems` (`Outcome/Lint.lean`), exported to `app/generated/sprime_outcome_theorems.json`
(`floors`, provenance `floor_dichotomy`). Design note: `Research/Notes/SPRIME_SOURCE_OF_TRUTH.md` §1.1.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD.Bots
open Classical

/-! ### 1. Single hinge, the `¬A_k` branch first -/

/-- `dich_DupocBot_vs_DBot` -/
@[floorA] theorem outcome_DupocBot_vs_DBot_floor :
    FloorSpecA (bot DupocBot) (const DBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_DupocBot_vs_DBot

/-- `dich_DupocBot_vs_EBot` -/
@[floorA] theorem outcome_DupocBot_vs_EBot_floor :
    FloorSpecA (bot DupocBot) (const EBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_DupocBot_vs_EBot

/-- `dich_DupocBot_vs_CupodTrollBot` -/
@[floorA] theorem outcome_DupocBot_vs_CupodTrollBot_floor :
    FloorSpecA (bot DupocBot) (bot CupodTrollBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_DupocBot_vs_CupodTrollBot

/-- `dich_JustBot_vs_DBot` -/
@[floorA] theorem outcome_JustBot_vs_DBot_floor :
    FloorSpecA (bot JustBot) (const DBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode DBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_JustBot_vs_DBot

/-- `dich_JustBot_vs_EBot` -/
@[floorA] theorem outcome_JustBot_vs_EBot_floor :
    FloorSpecA (bot JustBot) (const EBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode EBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_JustBot_vs_EBot

/-- `dich_JustBot_vs_CupodTrollBot` -/
@[floorA] theorem outcome_JustBot_vs_CupodTrollBot_floor :
    FloorSpecA (bot JustBot) (bot CupodTrollBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (CupodTrollBot k)) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_JustBot_vs_CupodTrollBot

/-- `dich_CIMCIC_vs_CupodTrollBot` -/
@[floorA] theorem outcome_CIMCIC_vs_CupodTrollBot_floor :
    FloorSpecA (bot CIMCIC) (bot CupodTrollBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_CIMCIC_vs_CupodTrollBot

/-- `dich_CIMCIC_vs_DBot` -/
@[floorA] theorem outcome_CIMCIC_vs_DBot_floor :
    FloorSpecA (bot CIMCIC) (const DBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode DBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_CIMCIC_vs_DBot

/-- `dich_CIMCIC_vs_EBot` -/
@[floorA] theorem outcome_CIMCIC_vs_EBot_floor :
    FloorSpecA (bot CIMCIC) (const EBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode EBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_CIMCIC_vs_EBot

/-- `dich_GuardianBot_vs_CIMCIC` (the hinge is CIMCIC's guard against Guardian) -/
@[floorA] theorem outcome_GuardianBot_vs_CIMCIC_floor :
    FloorSpecA (bot GuardianBot) (bot CIMCIC)
      (fun k ↦ □[k] (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (GuardianBot k)) k))
      (some (.C, .D)) :=
  FloorSpecA.of_dich dich_GuardianBot_vs_CIMCIC

/-- `dich_GuardianBot_vs_DupocBot` (the hinge is Dupoc's guard against Guardian) -/
@[floorA] theorem outcome_GuardianBot_vs_DupocBot_floor :
    FloorSpecA (bot GuardianBot) (bot DupocBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (GuardianBot k)) k))
      (some (.C, .D)) :=
  FloorSpecA.of_dich dich_GuardianBot_vs_DupocBot

/-- `dich_GuardianBot_vs_JustBot` (the hinge is Just's guard against Guardian) -/
@[floorA] theorem outcome_GuardianBot_vs_JustBot_floor :
    FloorSpecA (bot GuardianBot) (bot JustBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (GuardianBot k)) k))
      (some (.C, .D)) :=
  FloorSpecA.of_dich dich_GuardianBot_vs_JustBot

/-- `dich_CupodBot_vs_OBot` -/
@[floorA] theorem outcome_CupodBot_vs_OBot_floor :
    FloorSpecA (bot CupodBot) (const OBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode OBot) k))
      (some (.C, .D)) :=
  FloorSpecA.of_dich dich_CupodBot_vs_OBot

/-! ### 2. The prudence floors: one outer hinge settles the engine's value -/

/-- `dich_PrudentBot_vs_DupocBot` -/
@[floorA] theorem outcome_PrudentBot_vs_DupocBot_floor :
    FloorSpecA (bot PrudentBot) (bot DupocBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (DupocBot k)) k))
      (some (.D, .D)) :=
  FloorSpecA.of_dich dich_PrudentBot_vs_DupocBot

/-- `dich_PrudentBot_vs_PrudentBot` -/
@[floorA] theorem outcome_PrudentBot_vs_PrudentBot_floor :
    FloorSpecA (bot PrudentBot) (bot PrudentBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (PrudentBot k)) k))
      (some (.D, .D)) :=
  FloorSpecA.of_dich dich_PrudentBot_vs_PrudentBot

/-- `dich_JustBot_vs_PrudentBot` (the outer hinge, Just's guard, settles `(D, D)`) -/
@[floorA] theorem outcome_JustBot_vs_PrudentBot_floor :
    FloorSpecA (bot JustBot) (bot PrudentBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (PrudentBot k)) k))
      (some (.D, .D)) :=
  FloorSpecA.of_dich dich_JustBot_vs_PrudentBot

/-- `dich_CIMCIC_vs_PrudentBot` (the outer hinge, Prudent's guard against CIMCIC, settles `(D, D)`) -/
@[floorA] theorem outcome_CIMCIC_vs_PrudentBot_floor :
    FloorSpecA (bot CIMCIC) (bot PrudentBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CIMCIC k)) k))
      (some (.D, .D)) :=
  FloorSpecA.of_dich dich_CIMCIC_vs_PrudentBot

/-- `dich_PrudentBot_vs_EBot` — via `dich_PrudentBot_vs_EBot_full` (`Cells/PrudentLoose`), which has EBot's C
built in the `¬A_k` world (Prudent's Löb cooperation with `.bot MirrorBot`). -/
@[floorA] theorem outcome_PrudentBot_vs_EBot_floor :
    FloorSpecA (bot PrudentBot) (const EBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode EBot) k))
      (some (.D, .C)) :=
  FloorSpecA.of_dich dich_PrudentBot_vs_EBot_full

/-! ### 3. Nested dichotomies: the engine's value needs two hinges to fail -/

/-- `dich_GuardianBot_vs_PrudentBot` — via `dich_GuardianBot_vs_PrudentBot_prudenceFound`: the engine's `(C, D)`
is the world where neither Guardian's guard nor Prudent's outer guard is found. -/
@[floorA] theorem outcome_GuardianBot_vs_PrudentBot_floor :
    FloorSpecA (bot GuardianBot) (bot PrudentBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiG) (progCode (GuardianBot k)) (progCode (PrudentBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k))
      (some (.C, .D)) := by
  obtain ⟨k₀, h⟩ := dich_GuardianBot_vs_PrudentBot_prudenceFound
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ ((h k hk).2 hn.1).1 (((h k hk).2 hn.1).2.1 hn.2)

/-- `dich_WaryBot_vs_DupocBot`: the engine's `(C, D)` is the world where neither Wary's guard nor Dupoc's guard
against Wary is found. -/
@[floorA] theorem outcome_WaryBot_vs_DupocBot_floor :
    FloorSpecA (bot WaryBot) (bot DupocBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (DupocBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (WaryBot k)) k))
      (some (.C, .D)) := by
  obtain ⟨k₀, h⟩ := dich_WaryBot_vs_DupocBot
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ ((h k hk).2 hn.1).1 (((h k hk).2 hn.1).2.1 hn.2)

/-- `dich_WaryBot_vs_JustBot`: the engine's `(C, D)` is the world where neither Just's guard against Wary nor
Wary's guard is found. -/
@[floorA] theorem outcome_WaryBot_vs_JustBot_floor :
    FloorSpecA (bot WaryBot) (bot JustBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (WaryBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (JustBot k)) k))
      (some (.C, .D)) := by
  obtain ⟨k₀, h⟩ := dich_WaryBot_vs_JustBot
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ (((h k hk).2 hn.1).2.2 hn.2) ((h k hk).2 hn.1).1

/-- `dich_WaryBot_vs_PrudentBot` — via `dich_WaryBot_vs_PrudentBot_prudenceFound`: the engine's `(C, D)` is the
world where neither Prudent's outer guard against Wary nor Wary's guard is found. -/
@[floorA] theorem outcome_WaryBot_vs_PrudentBot_floor :
    FloorSpecA (bot WaryBot) (bot PrudentBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (WaryBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (PrudentBot k)) k))
      (some (.C, .D)) := by
  obtain ⟨k₀, h⟩ := dich_WaryBot_vs_PrudentBot_prudenceFound
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ (((h k hk).2 hn.1).2.2 hn.2) ((h k hk).2 hn.1).1

/-- `dich_CupodBot_vs_PrudentBot` — via `dich_CupodBot_vs_PrudentBot_prudenceFound`: the engine's `(C, D)` is the
world where neither Cupod's guard nor Prudent's outer guard against Cupod is found. -/
@[floorA] theorem outcome_CupodBot_vs_PrudentBot_floor :
    FloorSpecA (bot CupodBot) (bot PrudentBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k))
      (some (.C, .D)) := by
  obtain ⟨k₀, h⟩ := dich_CupodBot_vs_PrudentBot_prudenceFound
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ ((h k hk).2 hn.1).1 (((h k hk).2 hn.1).2.1 hn.2)

/-- `dich_PrudentBot_vs_CupodBot` — via `dich_PrudentBot_vs_CupodBot_prudenceFound`: the same pair, Prudent's side
first; the engine's `(D, C)` is the world where neither Cupod's guard nor Prudent's outer guard is found. -/
@[floorA] theorem outcome_PrudentBot_vs_CupodBot_floor :
    FloorSpecA (bot PrudentBot) (bot CupodBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k))
      (some (.D, .C)) := by
  obtain ⟨k₀, h⟩ := dich_PrudentBot_vs_CupodBot_prudenceFound
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ (((h k hk).2 hn.1).2.1 hn.2) ((h k hk).2 hn.1).1

/-- `dich_JustBot_vs_CupodBot`: the engine's `(D, C)` is the world where neither Just's guard nor Cupod's guard
against Just is found. -/
@[floorA] theorem outcome_JustBot_vs_CupodBot_floor :
    FloorSpecA (bot JustBot) (bot CupodBot)
      (fun k ↦ □[k] (guardCodeB (templateCode (phiJ k)) (progCode (JustBot k)) (progCode (CupodBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (JustBot k)) k))
      (some (.D, .C)) := by
  obtain ⟨k₀, h⟩ := dich_JustBot_vs_CupodBot
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ ((h k hk).2 hn.1).1 (((h k hk).2 hn.1).2.2 hn.2)

/-- `dich_CIMCIC_vs_CupodBot`: the engine's `(D, C)` is the world where neither CIMCIC's guard nor Cupod's guard
against CIMCIC is found. -/
@[floorA] theorem outcome_CIMCIC_vs_CupodBot_floor :
    FloorSpecA (bot CIMCIC) (bot CupodBot)
      (fun k ↦ □[k] (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodBot k)) k) ∨
               □[k] (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (CIMCIC k)) k))
      (some (.D, .C)) := by
  obtain ⟨k₀, h⟩ := dich_CIMCIC_vs_CupodBot
  refine ⟨k₀, fun k hk hn ↦ ?_⟩
  rw [not_or] at hn
  exact OutcomeAtA.of_evalGraph₂ ((h k hk).2 hn.1).1 (((h k hk).2 hn.1).2.2 hn.2)

end ArithS
