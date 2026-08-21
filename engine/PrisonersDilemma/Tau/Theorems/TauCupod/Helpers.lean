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

/-! ## Cupod's own plays at the two constant hypotheses

Both reduce to shapes the shared `Helpers` already certifies: at the cooperator the
punish-probe is refutable (`ps_probeD_false_of_plays_C`), at the defector it fires
(`ps_probeD_constD`). Same structure as Guardian's row — Cupod is a punisher too,
differing only in WHOM it probes (the hypothesis-vs-me, not the hypothesis-vs-the
cooperator). -/

/-- τ(Cupod) TRUSTS the unconditional cooperator: nothing to convict. -/
theorem cupod_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .coop)) (.bot (inst (tauZoo k) .cupod .coop))
      (inst (tauZoo k) .cupod .coop) = some Action.C :=
  searchProbeD_plays_C _ _ (ps_probeD_false_of_plays_C k ⟨1, rfl⟩)

/-- τ(Cupod) PUNISHES the defector: its defection is a trivial positive atom. -/
theorem cupod_defect_plays_D {k : Nat} (hk : 2 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .cupod .defect))
      (.bot (inst (tauZoo k) .cupod .defect))
      (inst (tauZoo k) .cupod .defect) = some Action.D :=
  searchProbeD_plays_D _ _ (ps_probeD_constD hk)

/-! ## THE ENTANGLED CELL — the open frontier of this milestone

`inst .cupod .dupoc` is the 2-member system: component 0 (Cupod-seeing-Dupoc) fires
on proving component 1 DEFECTS; component 1 (Dupoc-seeing-Cupod) fires on proving
component 0 COOPERATES. Each bit is a claim about the other, so neither is settled
by any column fact — this is a genuine MUTUAL fixpoint, the first in the tau layer.

**What is already in place.** The term exists and is pinned by `rfl`
(`inst_cupod_sys_dupoc`, and `inst_dupoc_sys_cupod` from the other side); the
system's `get?` and `sysClose` steps reduce definitionally; `PlaysProof.sysStep`
lets S read a component; and `Base/Loeb`'s `mutual_pblt_engine_id` consumes exactly
the shape this cycle produces — two cross-implications `□A → B`, `□B → A` — which
is why §8c predicted the pairwise engines would suffice here and the heavier
`vector2_full_pblt_engine` would not be needed.

**What is NOT yet proven** (deliberately recorded rather than papered over): the two
cross-implications themselves, i.e. the `sysStep`-mediated analogues of
`quine_loeb_premise` for a TWO-component system. They need S to read one component's
source through `sysClose` and conclude about the other — the binder's version of
`botSearchStep`, which currently has no `.sys`-aware twin. Until those land, the
`.cupod ↔ .dupoc` bits stay open and the columns below take them as HYPOTHESES,
exactly as the Dupoc quine bit was taken as a hypothesis before its Löb chain
closed.

The honest reading of the milestone: the WALL is broken (the term exists, evaluates,
and is readable by S); the MATHEMATICS of what the 2-cycle settles on is the next
piece of work. -/

end PD.Tau
