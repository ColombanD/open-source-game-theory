import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb

/-!
# Tau/Theorems/TauDupoc/Helpers — the Löb quine

TauDupoc's own mathematics: the ONE cell of the zoo that needs bounded Löb. Its
diagonal instance probes ITSELF (the compiler emits the pronoun guard), and the
fixpoint is closed by `botSearchStep` + `pblt_engine_id` — the Def-4 edition of
base `outcome_DupocBot_vs_DupocBot`'s argument. Public API: `ps_probe_inst_quine`
(the threshold bit) and `inst_quine_plays` (the diagonal entry's play).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The Löb quine — τ(Dupoc)'s diagonal -/

/-- The Löb premise for the quine fixpoint: S reads the frozen searcher's own
    source (`botSearchStep`) and concludes `□_k φ* → φ*` for
    `φ* = probe (inst .dupoc .dupoc)` — the guard sentence IS the probe atom,
    because `subst` closes the quine's `.self` to the wrapped player. -/
private theorem quine_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (probe (inst (tauZoo k) .dupoc .dupoc)))
             (probe (inst (tauZoo k) .dupoc .dupoc))) :=
  Pf.botSearchStep k (.plays .self .self .C) .C .D
    (.bot (inst (tauZoo k) .dupoc .dupoc)) (.bot (inst (tauZoo k) .dupoc .dupoc)) rfl
    (by
      simp only [inst_dupoc_quine, Formula.subst, Prog.subst, Formula.size,
        Prog.size, numCost]
      omega)

/-- From an actual cooperative play of the wrapped quine against itself, the guard
    must have fired (eval inversion — a false guard forces D). -/
private theorem probe_true_of_quine_play (k n : Nat)
    (h : play n (.bot (inst (tauZoo k) .dupoc .dupoc))
           (.bot (inst (tauZoo k) .dupoc .dupoc)) = some .C) :
    proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true := by
  cases hps : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) with
  | true => rfl
  | false =>
      exfalso
      have hps' : proofSearch k
          ((Formula.plays .self .self .C).subst
            (.bot (.search k (.plays .self .self .C) (.const .C) (.const .D)))
            (.bot (.search k (.plays .self .self .C) (.const .C) (.const .D))))
          = false := hps
      rw [inst_dupoc_quine] at h
      match n with
      | 0 => simp [play, eval] at h
      | 1 => simp [play, eval] at h
      | 2 => simp [play, eval, hps'] at h
      | n + 3 => simp [play, eval, hps'] at h

/-- **THE LÖB BIT**: past a threshold, the quine's probe atom is provable AT THE
    PROBING BUDGET ITSELF — same-`k` Löbian self-cooperation, Def-4 edition. -/
theorem ps_probe_inst_quine :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true := by
  have hφsz : ∀ k, (probe (inst (tauZoo k) .dupoc .dupoc)).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [probe, inst_dupoc_quine, Formula.size, Prog.size, numCost]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150)
        (.impl (.box k (probe (inst (tauZoo k) .dupoc .dupoc)))
               (probe (inst (tauZoo k) .dupoc .dupoc))) :=
    fun k _ => quine_loeb_premise k
  obtain ⟨k₂, hk₂⟩ :=
    pblt_engine_id (fun k => probe (inst (tauZoo k) .dupoc .dupoc))
      (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  exact probe_true_of_quine_play k n hn

/-! ## The quine entry's play -/

/-- The diagonal entry of τ(Dupoc)'s vector: past the Löb threshold the fixpoint
    fires and the entry plays C. -/
theorem inst_quine_plays {k : Nat}
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .dupoc))
         (.bot (inst (tauZoo k) .dupoc .dupoc)) (inst (tauZoo k) .dupoc .dupoc)
         = some Action.C := by
  have h : proofSearch k ((Formula.plays Prog.self Prog.self Action.C).subst
      (.bot (.search k (.plays .self .self Action.C) (.const .C) (.const .D)))
      (.bot (.search k (.plays .self .self Action.C) (.const .C) (.const .D))))
      = true := hquine
  have hq : eval 2
      (.bot (.search k (.plays .self .self Action.C) (.const .C) (.const .D)))
      (.bot (.search k (.plays .self .self Action.C) (.const .C) (.const .D)))
      (.search k (.plays .self .self Action.C) (.const .C) (.const .D))
      = some Action.C := by
    rw [eval]
    rw [h]
    rfl
  exact ⟨2, hq⟩

end PD.Tau
