import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Research.Spikes.computable_eval.Exclusion

/-!
# ⚠️ T3.2 finding — `atom_complete_false_guard` is INCONSISTENT (machine-checked `False`).

Discovered while designing the atom-layer decider (T3.2): the **anti-diagonal bot**

  `G := .search 100 (.plays .self .self .D) (.const .C) (.const .D)`

("if I can prove I defect against myself, cooperate — else defect") refutes the axiom:

* If `proofSearch 100 (G plays D vs G) = true`: soundness gives a real play of `D`, but the
  guard being true makes `eval` take the `.const .C` branch at every fuel — contradiction.
* If it is `false`: `play 2 G G = some .D` (the else-branch), the else-play has NO certificate
  (`Exclusion.no_pp_else` — the very irreducibility result), so the axiom fires and injects
  `AtomProvable (atom_cost 2) (G plays D vs G)` with `atom_cost 2 = 7 ≤ 100`; budget
  monotonicity lifts it to `Provable 100`, flipping the guard to `true` — contradiction.

Classical case split: `False`.

The root cause: the axiom injects the else-certificate at a budget (`atom_cost fuel`,
fuel-dependent only) that can sit BELOW the guard budget it refutes — the else-fact of a
self-referential guard must never be provable within that guard's own search budget. The zoo
never builds anti-diagonal guards, which is why every outcome theorem still checked; but the
THEORY proves `False`, so everything downstream of the axiom is vacuous until it is repaired
(PrudentBot/JustBot outcomes cite it; Dupoc/Cupod do not).

This also converges with the T3.2 decidability analysis: the CHARGED atom model (else-certs
must pay ≥ the guard budget, then-certs pay the guard PROOF's transcript — Critch-faithful,
since PA-style proofs embed their sub-proofs) is not merely what makes `AtomProvable`
decidable — it is what a CONSISTENT false-guard principle requires.
-/

namespace PD.T32
open PD PD.BaseTheorems

/-- The anti-diagonal bot: "if provably I play D against myself, play C; else play D". -/
def G : Prog := .search 100 (.plays .self .self .D) (.const .C) (.const .D)

/-- Its guard, closed under self-substitution: `G plays D against G`. -/
def gAtom : Formula := .plays G G .D

theorem guard_subst : (Formula.plays .self .self .D).subst G G = gAtom := rfl

/-- If the guard search succeeds, `G` cooperates at every fuel — so no real play of `D` exists. -/
theorem no_D_play_of_true (hps : proofSearch 100 gAtom = true) :
    ∀ n, play n G G ≠ some .D := by
  intro n hn
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
      have : play (m+1) G G = eval m G G (.const .C) := by
        show eval (m+1) G G (.search 100 (.plays .self .self .D) (.const .C) (.const .D)) = _
        rw [eval, guard_subst, hps]
        rfl
      rw [this] at hn
      cases m with
      | zero => simp [eval] at hn
      | succ m' => simp [eval] at hn

/-- If the guard search fails, `G` defects at fuel 2. -/
theorem D_play_of_false (hps : proofSearch 100 gAtom = false) :
    play 2 G G = some .D := by
  show eval 2 G G (.search 100 (.plays .self .self .D) (.const .C) (.const .D)) = some .D
  rw [eval, guard_subst, hps]
  rfl

/-- The else-play has no certificate term (the axiom's own irreducibility result). -/
theorem no_cert : ¬ (∃ _ : PlaysProof G G G .D (atom_cost 2), True) := by
  rintro ⟨cert, -⟩
  -- (post-repair `no_pp_else` is cost-qualified; `atom_cost 2 = 7 ≤ 100` keeps this instance)
  exact PD.Exclusion.no_pp_else 100 (.plays .self .self .D) .C .D G (by decide) (by decide) cert

/-- **The former axiom implies `False`** — stated hypothesis-relative since its deletion
    (2026-07-02): the axiom's exact statement is now a hypothesis, and this theorem is the
    machine-checked record of WHY it had to go. -/
theorem engine_inconsistent
    (atom_complete_false_guard :
      ∀ p q a fuel, play fuel p q = some a →
        ¬ (∃ _ : PlaysProof p q p a (atom_cost fuel), True) →
        AtomProvable (atom_cost fuel) (.plays p q a)) : False := by
  by_cases hps : proofSearch 100 gAtom = true
  · -- guard true ⇒ Provable ⇒ sound ⇒ a real D-play exists ⇒ contradicts cooperate-branch
    have hprov : Provable 100 gAtom := (proofSearch_spec _ _).1 hps
    obtain ⟨n, hn⟩ := Provable_sound 100 gAtom hprov
    exact no_D_play_of_true hps n hn
  · -- guard false ⇒ else-play real, certificate-free ⇒ axiom injects it at atom_cost 2 = 7
    have hps' : proofSearch 100 gAtom = false := by
      cases h : proofSearch 100 gAtom
      · rfl
      · exact absurd h hps
    have hplay : play 2 G G = some .D := D_play_of_false hps'
    have hatom : AtomProvable (atom_cost 2) gAtom :=
      atom_complete_false_guard G G .D 2 hplay no_cert
    have h7 : atom_cost 2 ≤ 100 := by decide
    have hprov : Provable 100 gAtom :=
      Provable.atom (atom_monotone (atom_cost 2) 100 gAtom h7 hatom)
    exact absurd ((proofSearch_spec _ _).2 hprov) (by simp [hps'])

#print axioms engine_inconsistent

end PD.T32
