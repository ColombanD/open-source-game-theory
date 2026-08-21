import PrisonersDilemma.Tau.Theorems.Columns

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
theorem dbotRow_plays {k : Nat} (hk : 2 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .dbot T)) (.bot (inst (tauZoo k) .dbot T))
              (inst (tauZoo k) .dbot T) = some (dbotRow T) :=
  let pD := inst_defect_plays (k := k) hk
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

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem dbotBits {k : Nat} (hk : 2 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .dbot w tauOrder)
      [(w .coop, .D), (w .defect, .C), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .D), (w .cupodTroll, .D), (w .cupod, .C), (w .cimcic, .C)] :=
  vecOf_bits (tauZoo k) .dbot w dbotRow tauOrder fun T _ => dbotRow_plays hk T

/-- **τ(DBot)** — boundary `θ ≤ dbotMass` (everything but `w .coop`). -/
theorem tauDBot_phase {k : Nat} (hk : 2 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (opponent : Prog) :
    (θ ≤ dbotMass w → ∃ N, play N (TauBotZ k .dbot w θ) opponent = some .C)
    ∧ (¬ θ ≤ dbotMass w → ∃ N, play N (TauBotZ k .dbot w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .dbot w dbotRow tauOrder θ opponent
    (fun T _ => dbotRow_plays hk T)
  simp only [bitMass, tauOrder, List.map, dbotRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [dbotMass] using h

end PD.Tau
