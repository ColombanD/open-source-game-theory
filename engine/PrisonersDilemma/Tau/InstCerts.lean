import PrisonersDilemma.Tau.Zoo

/-!
# Tau/InstCerts — the bit lemmas, stated over `inst Z A T` (the DSL vocabulary)

The "second era" interface: every probe bit the zoo consults, restated as a
**column theorem** over the COMPILED instances, indexed by the hypothesis. A column
is one question asked of every zoo member — "does T's instance, seeing X, provably
cooperate?" — and the zoo's specs consult exactly three of them:

* the **δ_C column** (`X = coop`) — TauTFTPf's whole strategy, TauEBot's
  reciprocity stage, and TauTFTSim's behavioral read (the `plays` variant below);
* the **δ_D column** (`X = defect`) — TauEBot's exploit stage;
* the **δ_L column** (`X = dupoc`) — TauDupoc's self-probe, with the QUINE at its
  diagonal and the FLOOR at its EBot cell.

Each column theorem is `∀ T`, one quantified statement per question instead of six
named lemmas per bot — the shape the NEXT zoo extends (add a bot: each column gains
one arm). The proofs are the `Tau/Certs` mathematics unchanged: Gate D1 makes every
compiled instance definitionally equal to the named instance the Certs lemma speaks
about, so each arm is a plain `exact`. `Certs` remains the proof layer; THIS file is
the API the vote layer reads.

**Scope, honestly:** only the CONSULTED columns are stated. A full 6×6 bit table
would need ~15 new floor/certificate lemmas for cells no bot ever probes (e.g.
"is `inst ebot tftSim`'s cooperation provable?" — floor-priced, but no consumer);
write those when a spec first consults their column, not before.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The δ_C column — "does T, seeing the COOPERATOR, provably cooperate?" -/

/-- δ_C column bits. Zero rows: Defect (refutable) and EBot (it EXPLOITS a
    cooperator — a firing exploit-probe, so its instance plays D). -/
def coopColBit : Tmpl → Bool
  | .defect => false
  | .ebot   => false
  | _       => true

theorem ps_probe_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .coop)) = coopColBit T
  | .coop   => ps_probe_coop hk
  | .defect => ps_probe_defect k
  | .tftSim => ps_probe_simOfCoop h6
  | .tftPf  => ps_probe_searchOfCoop hk hkk
  | .dupoc  => ps_probe_searchOfCoop hk hkk
  | .ebot   => ps_probe_eOfCoop_false hk k

/-! ## The δ_D column — "does T, seeing the DEFECTOR, provably cooperate?" -/

/-- δ_D column bits. Only the unconditional cooperator is exploitable. -/
def defectColBit : Tmpl → Bool
  | .coop => true
  | _     => false

theorem ps_probe_inst_defect {k : Nat} (hk : 2 ≤ k) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .defect)) = defectColBit T
  | .coop   => ps_probe_coop hk
  | .defect => ps_probe_defect k
  | .tftSim => ps_probe_simOfDefect k
  | .tftPf  => ps_probe_searchOfDefect k k
  | .dupoc  => ps_probe_searchOfDefect k k
  | .ebot   => ps_probe_eOfDefect k k

/-! ## The δ_L column — "does T, seeing DUPOC, provably cooperate?" -/

/-- δ_L column bits. Zero rows: Defect, and EBot — THE FLOOR: `inst ebot dupoc`
    really cooperates (see the Gödelian pair below), but only through a failed
    exploit-search, so no ≤k certificate exists and the bit honestly reads 0. The
    diagonal (`T = dupoc`) is the Löb quine, supplied as a hypothesis because it
    holds past a THRESHOLD (`ps_probe_inst_quine`), not at a fixed budget bound. -/
def dupocColBit : Tmpl → Bool
  | .defect => false
  | .ebot   => false
  | _       => true

theorem ps_probe_inst_dupoc {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .dupoc)) = dupocColBit T
  | .coop   => ps_probe_coop hk
  | .defect => ps_probe_defect k
  | .tftSim => ps_probe_simOfSearch hk hk7
  | .tftPf  => ps_probe_searchOfSearch hk hkk
  | .dupoc  => hquine
  | .ebot   => ps_probe_eOfSearch_false (le_refl k)

/-- **THE LÖB BIT, inst-native**: past a threshold, the quine's probe is provable at
    the probing budget itself. -/
theorem ps_probe_inst_quine :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true :=
  ps_probe_quine

/-! ## The Gödelian pair, inst-native — the δ_L column's EBot cell -/

/-- TRUE: `inst ebot dupoc` really cooperates (through its failed exploit-probe). -/
theorem interp_probe_inst_ebot_dupoc {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) :
    (probe (inst (zoo6 k) .ebot .dupoc)).interp :=
  interp_probe_eOfSearch hk hkk

/-- UNPROVABLE: that cooperation sits behind a `search_f` floor, so its bit is 0 at
    every budget up to k. Together with the previous theorem: a true bit that
    honestly reads 0. -/
theorem ps_probe_inst_ebot_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (zoo6 k) .ebot .dupoc)) = false :=
  ps_probe_eOfSearch_false hK

/-! ## The δ_C column, BEHAVIORAL — true plays, for `run`-mode consumers -/

/-- What T's instance seeing the cooperator TRULY plays (floor-blind — this is the
    `run`-mode read, TauTFTSim's). Note EBot's row: its instance plays D against a
    cooperator (it exploits), so behavioral and prover reads AGREE on this column;
    they part ways only where truth and provability part (the δ_L column's floor). -/
def coopColPlay : Tmpl → Action
  | .defect => .D
  | .ebot   => .D
  | _       => .C

theorem inst_coop_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (zoo6 k) T .coop)) (.bot (inst (zoo6 k) T .coop))
              (inst (zoo6 k) T .coop) = some (coopColPlay T)
  | .coop   => ⟨1, rfl⟩
  | .defect => ⟨1, rfl⟩
  | .tftSim => entry_C_of_interp (Pf_sound _ _ (pf_probe_simOfCoop h6))
  | .tftPf  => entry_C_of_interp (Pf_sound _ _ (pf_probe_searchOfCoop hk hkk))
  | .dupoc  => entry_C_of_interp (Pf_sound _ _ (pf_probe_searchOfCoop hk hkk))
  | .ebot   => by
      -- state the play against the NAMED instance; defeq (Gate D1) bridges
      have hb : proofSearch k (probe tauCoopδ) = true := ps_probe_coop hk
      have hplay : eval 3 (.bot (eOfCoopδ k)) (.bot (eOfCoopδ k)) (eOfCoopδ k)
          = some Action.D := by
        rw [eOfCoopδ, eδ, eval, probe_subst, hb]; rfl
      exact ⟨3, hplay⟩

/-! ## The quine entry's play -/

/-- The diagonal entry of τ(Dupoc)'s vector: running `.bot`-framed, `subst` closes
    `.self` to the wrapped quine, whose guard IS its own probe — the Löb fixpoint.
    Past the threshold it fires and the entry plays C. -/
theorem inst_quine_plays {k : Nat}
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true) :
    ∃ N, eval N (.bot (inst (zoo6 k) .dupoc .dupoc)) (.bot (inst (zoo6 k) .dupoc .dupoc))
         (inst (zoo6 k) .dupoc .dupoc) = some Action.C := by
  have h : proofSearch k ((Formula.plays Prog.self Prog.self Action.C).subst
      (.bot (TauDupocδ k)) (.bot (TauDupocδ k))) = true := hquine
  have hq : eval 2 (.bot (TauDupocδ k)) (.bot (TauDupocδ k)) (TauDupocδ k)
      = some Action.C := by
    rw [TauDupocδ, eval] at *
    rw [h]
    rfl
  exact ⟨2, hq⟩

end PD.Tau
