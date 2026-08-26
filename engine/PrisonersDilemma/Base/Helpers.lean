import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.ValuationSoundness
import PrisonersDilemma.Outcome

open PD

namespace PD.Theorems

theorem play_from_eval (fuel : Nat) (me opponent : Prog) (a : Action)
    (hEval : eval fuel me opponent me = some a) :
    play fuel me opponent = some a := by
  simpa [play] using hEval

/--
Generic one-step helper for `ite` programs: if `me` is an `ite` and you know
the guard value at fuel `fuel + n`, this theorem rewrites
`play (fuel + n + 1) me opponent` to the corresponding branch evaluation.
If guardAct == test, then use p as body, else use q
-/
theorem play_ite_from_guard
    (fuel n : Nat)
    (me opponent guard p q : Prog)
    (test guardAct : Action)
    (hMe : me = .ite guard test p q)
    (hGuard : eval (fuel + n) me opponent guard = some guardAct) :
    play (fuel + n + 1) me opponent =
      (if guardAct == test
        then eval (fuel + n) me opponent p
        else eval (fuel + n) me opponent q) := by
  have hGuard' :
      eval (fuel + n) (.ite guard test p q) opponent guard = some guardAct := by
    simpa [hMe] using hGuard
  rw [hMe]
  unfold play
  rw [show eval (fuel + n + 1)
          (.ite guard test p q)
          opponent
          (.ite guard test p q)
        =
          (do
            let r ← eval (fuel + n) (.ite guard test p q) opponent guard
            if r == test then
              eval (fuel + n) (.ite guard test p q) opponent p
            else
              eval (fuel + n) (.ite guard test p q) opponent q) by
        rfl]
  rw [hGuard']
  simp

/--
`eval`-level twin of `play_ite_from_guard`: given the guard's value, peel off
one layer of an `ite` body without requiring the body to equal `me`. Useful
for tracing nested `ite` chains (EBot's three-guard structure, etc.).
-/
theorem eval_ite_from_guard
    (fuel : Nat) (me opponent guard p q : Prog)
    (test guardAct : Action)
    (hGuard : eval fuel me opponent guard = some guardAct) :
    eval (fuel + 1) me opponent (.ite guard test p q) =
      (if guardAct == test
        then eval fuel me opponent p
        else eval fuel me opponent q) := by
  rw [show eval (fuel + 1) me opponent (.ite guard test p q)
        = (do let r ← eval fuel me opponent guard
              if r == test then eval fuel me opponent p
              else eval fuel me opponent q)
        by rfl]
  rw [hGuard]
  simp

/--
A `(.sim .opp (.bot z))` guard reduces to `play fuel opp (.bot z)`: the outer
`subst` sends `.opp` to `opp` and leaves `.bot z` untouched, so the simulation
is exactly opp running against `.bot z`. Hypothesis at `fuel`, conclusion at
`fuel + 1`.
-/
theorem eval_sim_opp_bot_of_play
    (fuel : Nat) (me opponent z : Prog) (a : Action)
    (h : play fuel opponent (.bot z) = some a) :
    eval (fuel + 1) me opponent (.sim .opp (.bot z)) = some a := by
  show eval fuel opponent (.bot z) opponent = some a
  exact h

/-- **Fuel monotonicity at the `outcome` level.** The `eval`-level lemmas
    (`eval_mono`/`eval_mono_le`, `Base/ValuationSoundness`) lift to whole matches:
    a determined outcome survives any larger fuel.

    This is what makes the `∃ fuel` and `∀ fuel, … (fuel + pad)` statement forms
    interchangeable, so outcome theorems can be stated in ONE canonical cofinite
    shape (see `Outcome/Spec.lean`). Before this lemma every theorem re-derived
    the lift inline. -/
theorem outcome_mono_le {p q : Prog} {r : Outcome} {N : Nat}
    (h : outcome N p q = some r) : ∀ M, N ≤ M → outcome M p q = some r := by
  intro M hM
  unfold outcome play at h ⊢
  cases hA : eval N p q p with
  | none => rw [hA] at h; simp at h
  | some a =>
    cases hB : eval N q p q with
    | none => rw [hA, hB] at h; simp at h
    | some b =>
      rw [PD.BaseTheorems.eval_mono_le hA M hM, PD.BaseTheorems.eval_mono_le hB M hM]
      rw [hA, hB] at h
      exact h

/-- **Fuel determinism.** Two determined plays of the same match agree, whatever their
    fuels: lift both to the larger fuel with `eval_mono_le`. -/
theorem play_unique {p q : Prog} {a b : Action} {n m : Nat}
    (ha : play n p q = some a) (hb : play m p q = some b) : a = b := by
  have h1 := PD.BaseTheorems.eval_mono_le ha (max n m) (Nat.le_max_left _ _)
  have h2 := PD.BaseTheorems.eval_mono_le hb (max n m) (Nat.le_max_right _ _)
  rw [h1] at h2
  exact Option.some.inj h2

/-- **From an existential fuel witness to the cofinite form at a pad.**

    `Formula.interp` reads `.plays p q a` as `∃ n, play n p q = some a`, so a play
    obtained from `Pf_sound` comes with an UNBOUNDED fuel. That witness need not be
    bounded: it suffices that the match is DETERMINED at `pad` at all (`htot`, a
    structural fact about the two programs, independent of any budget numeral inside
    them) — determinism then forces the value at `pad` to be the same `a`, and
    monotonicity carries it to every larger fuel. This is what lets the Löbian results
    be stated with a literal pad like every other cell (`Outcome/Spec.lean`). -/
theorem play_at_of_ex {p q : Prog} {a : Action} {pad : Nat}
    (hex : ∃ n, play n p q = some a) (htot : ∃ b, play pad p q = some b) :
    ∀ fuel, play (fuel + pad) p q = some a := by
  obtain ⟨n, hn⟩ := hex
  obtain ⟨b, hb⟩ := htot
  obtain rfl : b = a := play_unique hb hn
  intro fuel
  exact PD.BaseTheorems.eval_mono_le hb _ (Nat.le_add_left _ _)

/-- `play_at_of_ex` at the `outcome` level. -/
theorem outcome_at_of_ex {p q : Prog} {r : Outcome} {pad : Nat}
    (hex : ∃ n, outcome n p q = some r) (htot : ∃ r', outcome pad p q = some r') :
    ∀ fuel, outcome (fuel + pad) p q = some r := by
  obtain ⟨n, hn⟩ := hex
  obtain ⟨r', hr⟩ := htot
  have h1 := outcome_mono_le hn (max n pad) (Nat.le_max_left _ _)
  have h2 := outcome_mono_le hr (max n pad) (Nat.le_max_right _ _)
  rw [h1] at h2
  obtain rfl : r' = r := (Option.some.inj h2).symm
  intro fuel
  exact outcome_mono_le hr _ (Nat.le_add_left _ _)

/-- A one-guard searcher with constant leaves is determined at fuel 2 against ANY
    opponent, whichever way the oracle decides — the totality fact `play_at_of_ex`
    needs for `DupocBot`/`CupodBot`-shaped bots. -/
theorem play_search_const_total (k : Nat) (φ : Formula) (a b : Action) (opp : Prog)
    (fuel : Nat) :
    ∃ c, play (fuel + 2) (.search k φ (.const a) (.const b)) opp = some c := by
  unfold play
  simp only [eval]
  split <;> exact ⟨_, rfl⟩

/-- Two determined plays at the same fuel make a determined outcome — the totality
    premise of `outcome_at_of_ex`, assembled leg by leg. -/
theorem outcome_total_of_plays {p q : Prog} {pad : Nat}
    (hA : ∃ a, play pad p q = some a) (hB : ∃ b, play pad q p = some b) :
    ∃ r, outcome pad p q = some r := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨(a, b), by simp [outcome, ha, hb]⟩

/-- Totality is fuel-monotone. -/
theorem play_total_mono {p q : Prog} {N : Nat} (h : ∃ a, play N p q = some a) :
    ∀ M, N ≤ M → ∃ a, play M p q = some a := by
  obtain ⟨a, ha⟩ := h
  intro M hM
  exact ⟨a, PD.BaseTheorems.eval_mono_le ha M hM⟩

/-- `.sim .opp .self` (MirrorBot's source) is determined one fuel above the opponent's
    play against it: the mirror's turn IS the opponent's self-play in the mirror's frame. -/
theorem play_sim_opp_self_total {X : Prog} {n : Nat}
    (h : ∃ a, play n X (.sim .opp .self) = some a) :
    ∃ a, play (n + 1) (.sim .opp .self) X = some a := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  unfold play at ha ⊢
  simp only [eval, Prog.subst]
  exact ha

/-! ### Totality of the closed `ite`/`sim` bots — the pieces `outcome_at_of_ex` needs
for `TitForTatBot`/`DBot`/`EBot`/`OBot` opponents, assembled guard by guard. -/

theorem eval_const_total (fuel : Nat) (me opp : Prog) (a : Action) :
    ∃ b, eval (fuel + 1) me opp (.const a) = some b := ⟨a, rfl⟩

/-- An `ite` body is determined one fuel above its guard and both branches. -/
theorem eval_ite_total {fuel : Nat} {me opp guard p q : Prog} {test : Action}
    (hG : ∃ g, eval fuel me opp guard = some g)
    (hp : ∃ a, eval fuel me opp p = some a)
    (hq : ∃ a, eval fuel me opp q = some a) :
    ∃ a, eval (fuel + 1) me opp (.ite guard test p q) = some a := by
  obtain ⟨g, hg⟩ := hG
  obtain ⟨b, hb⟩ := hp
  obtain ⟨c, hc⟩ := hq
  rw [eval_ite_from_guard fuel me opp guard p q test g hg]
  split
  · exact ⟨b, hb⟩
  · exact ⟨c, hc⟩

/-- `eval_ite_total` for the whole player: an `ite` PROGRAM's play is determined. -/
theorem play_ite_total {fuel : Nat} {me opp guard p q : Prog} {test : Action}
    (hMe : me = .ite guard test p q)
    (hG : ∃ g, eval fuel me opp guard = some g)
    (hp : ∃ a, eval fuel me opp p = some a)
    (hq : ∃ a, eval fuel me opp q = some a) :
    ∃ a, play (fuel + 1) me opp = some a := by
  subst hMe
  exact eval_ite_total hG hp hq

/-- A `.sim .opp (.bot z)` probe is determined one fuel above the opponent's play vs `z`. -/
theorem eval_sim_opp_bot_total {fuel : Nat} {me opp z : Prog}
    (h : ∃ a, play fuel opp (.bot z) = some a) :
    ∃ a, eval (fuel + 1) me opp (.sim .opp (.bot z)) = some a := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, eval_sim_opp_bot_of_play fuel me opp z a ha⟩

/-- Package two `play` results into an `outcome`. -/
theorem outcome_of_plays
    (fuel : Nat) (p q : Prog) (a b : Action)
    (hA : play fuel p q = some a) (hB : play fuel q p = some b) :
    outcome fuel p q = some (a, b) := by
  simp [outcome, hA, hB]

end PD.Theorems
