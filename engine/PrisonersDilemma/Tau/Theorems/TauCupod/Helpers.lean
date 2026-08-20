import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Base.Loeb

/-!
# Tau/Theorems/TauCupod — the suspicious cooperator's mathematics

τ(Cupod) is τ(Dupoc)'s mirror: same self-probe geometry, inverted polarity. It
proves DEFECTION and punishes; it trusts by default. Three shapes to handle:

* **off-cycle hypotheses** — an ordinary `probeD` prove-stage, so the existing
  `searchProbeD_plays_*` shape lemmas apply verbatim;
* **the diagonal** — the quine, with `.D` in the guard: "if I can prove I defect
  against myself, defect". Unlike Dupoc's, this fixpoint is NOT closed by bounded
  Löb — Löb gives you `□φ → φ ⊢ φ` for the sentence the searcher FIRES on, and
  here firing means defecting, so the Löbian route would prove self-defection.
  What actually holds is the opposite and it is cheap: the guard is REFUTABLE
  (a cost floor), so the search fails and Cupod trusts itself;
* **the entangled cell** — `.sys`, handled in `Columns.lean` where both sides of
  the 2-cycle are in scope.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The diagonal: τ(Cupod)'s quine is LÖBIAN, and it proves SELF-DEFECTION

The mirror of Dupoc's Löb quine with the polarity inverted — and the inversion
changes what the fixpoint MEANS. Dupoc's guard fires on cooperation, so bounded Löb
delivers self-cooperation. Cupod's guard fires on DEFECTION with a trusting default,
so the very same machinery (`botSearchStep` is polarity-generic: it takes the
then/else actions as parameters) delivers **self-DEFECTION**: past the threshold
τ(Cupod) proves it defects against itself, so it does.

*A first attempt to refute the guard by the `search_f` floor was WRONG and the
kernel caught it: `no_provable_botSearcherElse_tail` excludes the ELSE-play (here
`.C`), but the guard atom is about the THEN-play `.D`, which `search_t` reaches.
The floor says nothing about it; Löb does.*

This is the tau image of base CupodBot's suspicion turning on itself — the
suspicious cooperator is exactly the bot its own test convicts. -/

/-- The Löb premise for Cupod's quine: S reads the frozen searcher's own source and
    concludes `□_k φ* → φ*` for `φ* = probeD (inst .cupod .cupod)`. Identical to
    Dupoc's construction with the branch actions swapped. -/
private theorem cupod_quine_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (probeD (inst (tauZoo k) .cupod .cupod)))
             (probeD (inst (tauZoo k) .cupod .cupod))) :=
  Pf.botSearchStep k (.plays .self .self .D) .D .C
    (.bot (inst (tauZoo k) .cupod .cupod)) (.bot (inst (tauZoo k) .cupod .cupod)) rfl
    (by
      simp only [inst_cupod_quine, Formula.subst, Prog.subst, Formula.size,
        Prog.size, numCost]
      omega)

/-- From an actual DEFECTING play of the wrapped quine against itself, the guard
    must have fired (eval inversion — a false guard forces the trusting C). -/
private theorem probeD_true_of_quine_play (k n : Nat)
    (h : play n (.bot (inst (tauZoo k) .cupod .cupod))
           (.bot (inst (tauZoo k) .cupod .cupod)) = some .D) :
    proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true := by
  cases hps : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) with
  | true => rfl
  | false =>
      exfalso
      have hps' : proofSearch k
          ((Formula.plays .self .self Action.D).subst
            (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
            (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C))))
          = false := hps
      rw [inst_cupod_quine] at h
      match n with
      | 0 => simp [play, eval] at h
      | 1 => simp [play, eval] at h
      | 2 => simp [play, eval, hps'] at h
      | n + 3 => simp [play, eval, hps'] at h

/-- **THE LÖB BIT, inverted**: past a threshold τ(Cupod)'s self-defection atom is
    provable at the probing budget itself. -/
theorem ps_probeD_inst_cupod_quine :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true := by
  have hφsz : ∀ k, (probeD (inst (tauZoo k) .cupod .cupod)).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [probeD, inst_cupod_quine, Formula.size, Prog.size, numCost]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150)
        (.impl (.box k (probeD (inst (tauZoo k) .cupod .cupod)))
               (probeD (inst (tauZoo k) .cupod .cupod))) :=
    fun k _ => cupod_quine_loeb_premise k
  obtain ⟨k₂, hk₂⟩ :=
    pblt_engine_id (fun k => probeD (inst (tauZoo k) .cupod .cupod))
      (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  exact probeD_true_of_quine_play k n hn

/-- **τ(Cupod) DEFECTS AGAINST ITSELF**: past the Löb threshold its punish-guard
    fires on its own diagonal. -/
theorem inst_cupod_quine_plays_D {k : Nat}
    (hq : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .cupod))
      (.bot (inst (tauZoo k) .cupod .cupod)) (inst (tauZoo k) .cupod .cupod)
      = some Action.D := by
  have h : proofSearch k ((Formula.plays Prog.self Prog.self Action.D).subst
      (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
      (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C))))
      = true := by simpa [probeD, inst_cupod_quine k, Formula.subst, Prog.subst] using hq
  refine ⟨2, ?_⟩
  conv_lhs => arg 4; rw [inst_cupod_quine k]
  rw [eval]
  rw [show (Formula.plays Prog.self Prog.self Action.D).subst
        (.bot (inst (tauZoo k) .cupod .cupod)) (.bot (inst (tauZoo k) .cupod .cupod))
      = (Formula.plays Prog.self Prog.self Action.D).subst
        (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
        (.bot (.search k (.plays .self .self Action.D) (.const .D) (.const .C)))
      from by rw [inst_cupod_quine k], h]
  rfl

end PD.Tau
