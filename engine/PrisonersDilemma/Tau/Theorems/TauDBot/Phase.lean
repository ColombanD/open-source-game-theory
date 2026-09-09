import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(DBot)'s phase — the punisher's boundary, `θ ≤ dbotMass`.

DBot trusts everyone whose δ_D instance DEFECTS — i.e. everyone who is not a
pushover. Two hypotheses fail that test, and the second is the interesting one:

* the constant cooperator (it cooperates with anyone, defector included);
* **ITSELF** — DBot's own instance at the defector TRUSTS (a defector is not a
  pushover), so DBot's self-watch sees cooperation-against-a-defector and fires.
  τ(DBot) PUNISHES ITSELF: the punisher's test cannot distinguish "cooperates
  with a defector because it is naive" from "…because the defector passed its
  own test". Self-defeating detection, the behavioral analogue of single-tier
  PrudentBot's `(D, D)` self-play.

So its mass excludes `w .coop` and `w .dbot`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(DBot)'s bit ROW: D exactly at the exploitable constant cooperator. -/
def dbotRow : Tmpl → Action
  | .coop => .D
  | .dbot => .D
  | .cupod      => .C
  | .cupodTroll => .D
  | _     => .C

/-- The row's witness: one run-stage watching the δ_D behavioral column — every
    hypothesis but the constant cooperator defects against a defector, so the
    watch falls through to trust. -/
theorem dbotRow_plays {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .dbot T)) (.bot (inst (tauZoo k) .dbot T))
              (inst (tauZoo k) .dbot T) = some (dbotRow T) :=
  let pD := inst_defect_plays (k := k) hk hL
  fun T => match T with
  | .coop     => dbot_coop_plays_D
  | .defect   => dbot_plays_C_of_defect .defect (pD .defect)
  | .tftSim   => dbot_plays_C_of_defect .tftSim (pD .tftSim)
  | .tftPf    => dbot_plays_C_of_defect .tftPf (pD .tftPf)
  | .dupoc    => dbot_plays_C_of_defect .dupoc (pD .dupoc)
  | .ebot     => dbot_plays_C_of_defect .ebot (pD .ebot)
  | .just     => dbot_plays_C_of_defect .just (pD .just)
  | .obot     => dbot_plays_C_of_defect .obot (pD .obot)
  | .guardian => dbot_plays_C_of_defect .guardian (pD .guardian)
  | .dbot     => -- DBot's OWN δ_D instance TRUSTS the defector (defectColPlay .dbot
                 -- = .C), so DBot's self-watch FIRES: it punishes itself.
                 dbot_selfWatch_fires
  | .cupod      => dbot_plays_C_of_defect .cupod (pD .cupod)
  | .cupodTroll => -- CupodTroll TRUSTS the defector (its identity check fails), and
                   -- trust-toward-a-defector is the punisher's fire condition
                   dbot_watch_fires_of_trust .cupodTroll (pD .cupodTroll)
  | .cimcic     => dbot_plays_C_of_defect .cimcic (pD .cimcic)
  | .dimcid     => dbot_plays_C_of_defect .dimcid (pD .dimcid)
  | .prudent    => dbot_plays_C_of_defect .prudent (pD .prudent)
  | .mirror     => dbot_plays_C_of_defect .mirror (pD .mirror)
  | .maxconfidence => dbot_plays_C_of_defect .maxconfidence (pD .maxconfidence)
  | .minconfidence => dbot_plays_C_of_defect .minconfidence (pD .minconfidence)

/-- **τ(DBot)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem dbotRowSpec : RowSpec .dbot tauOrder dbotRow := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 100 1000
  exact ⟨K + 1, fun k hk T _ => dbotRow_plays (by omega) (hK k (by omega)) T⟩

/-- **τ(DBot)** — boundary `θ ≤ dbotMass` (everything but `w .coop`). -/
theorem tauDBot_phase {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (opponent : Prog) :
    (θ ≤ dbotMass w → ∃ N, play N (TauBotZ k .dbot w θ) opponent = some .C)
    ∧ (¬ θ ≤ dbotMass w → ∃ N, play N (TauBotZ k .dbot w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .dbot w dbotRow tauOrder θ opponent
    (fun T _ => dbotRow_plays hk hL T)
  simp only [bitMass, tauOrder, List.map, dbotRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [dbotMass, -forall_const] using h

end PD.Tau
