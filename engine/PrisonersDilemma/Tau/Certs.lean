import PrisonersDilemma.Tau.Defs
import PrisonersDilemma.Base.Soundness
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Certs — the guard-bit lemmas

One lemma per δ-instance probe: is `probe I` provable (at which budget), refuted, or
Löbian? These are the "bits" the peel lemmas consume. All positive certificates are
`PlaysProof` transcripts (`bot`/`sim`/`ite_t`/`search_t` — the `PlaysProof` mirror of
`eval`); the one negative is a soundness refutation; the one Löbian bit is the
`.bot`-wrapped quine fixpoint, closed by `botSearchStep` + `pblt_engine_id` — the
Def-4 analogue of `outcome_DupocBot_vs_DupocBot`'s argument.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- Probe atoms are closed: `subst` cannot touch a `.bot`-frozen instance. -/
theorem probe_subst (I me o : Prog) : (probe I).subst me o = probe I := rfl

/-- Handy: the two cost constants, for `omega`. -/
private theorem hcl : c_leaf = 1 := rfl
private theorem hcn : c_node = 1 := rfl

/-! ## Positive bits (transcript certificates) -/

/-- `C(δ_·)` cooperates, provably from budget 2. -/
theorem pf_probe_coop {k : Nat} (hk : 2 ≤ k) : Pf k (probe tauCoopδ) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by have := hcl; have := hcn; omega⟩

theorem ps_probe_coop {k : Nat} (hk : 2 ≤ k) :
    proofSearch k (probe tauCoopδ) = true :=
  (proofSearch_spec _ _).2 (pf_probe_coop hk)

/-- `L(δ_C) = Tp(δ_C)` cooperates (its guard cites the Coop bit), provably from
    `c_guard k + 3`. -/
theorem pf_probe_searchOfCoop {k K : Nat} (hk : 2 ≤ k) (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (searchOfCoopδ k)) :=
  Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t (pf_probe_coop hk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probe_searchOfCoop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probe (searchOfCoopδ k)) = true :=
  (proofSearch_spec _ _).2 (pf_probe_searchOfCoop hk hkk)

/-- `Ts(δ_C)` cooperates (runs the frozen Coop instance), provably from budget 6. -/
theorem pf_probe_simOfCoop {K : Nat} (hK : 6 ≤ K) : Pf K (probe simOfCoopδ) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) rfl
      PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probe_simOfCoop {k : Nat} (hk : 6 ≤ k) :
    proofSearch k (probe simOfCoopδ) = true :=
  (proofSearch_spec _ _).2 (pf_probe_simOfCoop hk)

/-- `Ts(δ_L)` cooperates (runs `L(δ_C)`, whose guard fires), provably from
    `c_guard k + 7`. -/
theorem pf_probe_simOfSearch {k K : Nat} (hk : 2 ≤ k) (hK : c_guard k + 7 ≤ K) :
    Pf K (probe (simOfSearchδ k)) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t
      (PlaysProof.sim (PlaysProof.bot
        (PlaysProof.search_t (pf_probe_coop hk) PlaysProof.const)))
      rfl PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probe_simOfSearch {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 7 ≤ k) :
    proofSearch k (probe (simOfSearchδ k)) = true :=
  (proofSearch_spec _ _).2 (pf_probe_simOfSearch hk hkk)

/-- `Tp(δ_L)` cooperates (probes `L(δ_C)`, provable within `k` once
    `c_guard k + 3 ≤ k`), provably from `c_guard k + 3`. -/
theorem pf_probe_searchOfSearch {k K : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (searchOfSearchδ k)) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.search_t (pf_probe_searchOfCoop hk hkk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probe_searchOfSearch {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probe (searchOfSearchδ k)) = true :=
  (proofSearch_spec _ _).2 (pf_probe_searchOfSearch hk hkk hkk)

/-! ## The negative bit (soundness refutation) -/

/-- `D(δ_·)` never cooperates: the probe atom is FALSE. -/
theorem interp_probe_defect_false : ¬ (probe tauDefectδ).interp := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | n + 2 => simp [play, eval, tauDefectδ] at hn

/-- Hence the Defect probe is unprovable at EVERY budget — the bit is 0. -/
theorem ps_probe_defect (m : Nat) : proofSearch m (probe tauDefectδ) = false := by
  cases h : proofSearch m (probe tauDefectδ) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) interp_probe_defect_false

/-! ## The Löbian bit (the quine) -/

/-- The Löb premise for the `.bot`-wrapped quine fixpoint: S reads the frozen
    searcher's own source (`botSearchStep`) and concludes `□_k φ* → φ*` for
    `φ* = probe (TauDupocδ k)` — the guard sentence IS the probe atom, because
    `subst` closes the quine's `.self` to the wrapped player. Transcript: one
    transparency leaf, `O(log k)`. -/
theorem tauDupocδ_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (probe (TauDupocδ k))) (probe (TauDupocδ k))) :=
  Pf.botSearchStep k (.plays .self .self .C) .C .D
    (.bot (TauDupocδ k)) (.bot (TauDupocδ k)) rfl
    (by
      simp only [Formula.subst, Prog.subst, Formula.size, Prog.size,
        TauDupocδ, numCost]
      omega)

/-- From an actual cooperative play of the wrapped quine against itself, the guard
    must have fired (eval inversion — a false guard forces D). -/
theorem probe_true_of_quine_play (k n : Nat)
    (h : play n (.bot (TauDupocδ k)) (.bot (TauDupocδ k)) = some .C) :
    proofSearch k (probe (TauDupocδ k)) = true := by
  cases hps : proofSearch k (probe (TauDupocδ k)) with
  | true => rfl
  | false =>
      exfalso
      -- the eval unfolding δ-reduces the quine, so state the guard bit in the
      -- unfolded form (defeq to `hps`)
      have hps' : proofSearch k
          ((Formula.plays .self .self .C).subst
            (.bot (.search k (.plays .self .self .C) (.const .C) (.const .D)))
            (.bot (.search k (.plays .self .self .C) (.const .C) (.const .D))))
          = false := hps
      match n with
      | 0 => simp [play, eval] at h
      | 1 => simp [play, eval] at h
      | 2 => simp [play, eval, TauDupocδ, hps'] at h
      | n + 3 => simp [play, eval, TauDupocδ, hps'] at h

/-- **THE LÖB BIT**: past a threshold, the quine's probe atom is provable AT THE
    PROBING BUDGET ITSELF — same-`k` Löbian self-cooperation, Def-4 edition. -/
theorem ps_probe_quine :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probe (TauDupocδ k)) = true := by
  have hφsz : ∀ k, (probe (TauDupocδ k)).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [probe, Formula.size, Prog.size, TauDupocδ, numCost]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150)
        (.impl (.box k (probe (TauDupocδ k))) (probe (TauDupocδ k))) :=
    fun k _ => tauDupocδ_loeb_premise k
  obtain ⟨k₂, hk₂⟩ :=
    pblt_engine_id (fun k => probe (TauDupocδ k))
      (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  exact probe_true_of_quine_play k n hn

/-! ### The δ_D column — TauEBot's exploit stage (cascade refactor, 2026-08-12)

"Does B, seeing TauDefect, cooperate?" Only the Coop hypothesis fires; every
other instance plays D against a defector, so its probe atom is FALSE and
soundness kills the bit at every budget. -/

/-- `L(δ_D) = Tp(δ_D)` **DEFECT**: they probe `.const D`, refutable, so the
    guard fails and the else-branch runs. The bit is 0. -/
theorem interp_probe_searchOfDefect_false (k : Nat) :
    ¬ (probe (searchOfDefectδ k)).interp := by
  rintro ⟨n, hn⟩
  -- the guard bit in the form `eval`'s unfolding exposes (defeq to `ps_probe_defect`)
  have hps : proofSearch k
      ((probe tauDefectδ).subst
        (.bot (.search k (probe tauDefectδ) (.const .C) (.const .D)))
        (.bot (.search k (probe tauDefectδ) (.const .C) (.const .D))))
      = false := ps_probe_defect k
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, searchOfDefectδ, probeSearchδ, hps] at hn
  | n + 3 => simp [play, eval, searchOfDefectδ, probeSearchδ, hps] at hn

theorem ps_probe_searchOfDefect (k m : Nat) :
    proofSearch m (probe (searchOfDefectδ k)) = false := by
  cases h : proofSearch m (probe (searchOfDefectδ k)) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_probe_searchOfDefect_false k)

/-- `Ts(δ_D)` **DEFECTS**: it runs `.const D` and copies the defection.

    The `.ite` guard is a `.sim` of the frozen `.const D`, so at any fuel ≥ 2
    the guard yields `D ≠ C` and the else-branch `.const .D` runs. The deep
    case needs the inner `.bot`/`.const` unfolding supplied explicitly, since
    `simp` stops at the `bind`. -/
theorem interp_probe_simOfDefect_false : ¬ (probe simOfDefectδ).interp := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, simOfDefectδ, tftSimδ, tauDefectδ] at hn
  | 3 => simp [play, eval, simOfDefectδ, tftSimδ, tauDefectδ] at hn
  | n + 4 =>
      -- `.const` evaluates at ANY positive fuel; the residual here is `n`, so
      -- case on it rather than guessing an offset.
      cases n with
      | zero =>
          simp only [play, eval, simOfDefectδ, tftSimδ, tauDefectδ, Prog.subst] at hn
          simp at hn
      | succ m =>
          have hinner : eval (m + 1) (.bot (.const Action.D))
              (.bot (.const Action.D)) (.const Action.D) = some Action.D := rfl
          simp only [play, eval, simOfDefectδ, tftSimδ, tauDefectδ, Prog.subst,
            hinner] at hn
          exact absurd hn (by decide)

theorem ps_probe_simOfDefect (m : Nat) : proofSearch m (probe simOfDefectδ) = false := by
  cases h : proofSearch m (probe simOfDefectδ) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) interp_probe_simOfDefect_false

/-- `E(δ_D)` **DEFECTS**: both cascade probes are about `.const D` — false — so
    the cascade falls through both else-branches to the final `.const D`. -/
theorem interp_probe_eOfDefect_false (k : Nat) :
    ¬ (probe (eOfDefectδ k)).interp := by
  rintro ⟨n, hn⟩
  have hps : proofSearch k
      ((probe tauDefectδ).subst
        (.bot (.search k (probe tauDefectδ) (.const .D)
          (.search k (probe tauDefectδ) (.const .C) (.const .D))))
        (.bot (.search k (probe tauDefectδ) (.const .D)
          (.search k (probe tauDefectδ) (.const .C) (.const .D)))))
      = false := ps_probe_defect k
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, eOfDefectδ, eδ, hps] at hn
  | n + 3 =>
      -- the cascade consumes three fuel units (bot + two searches); the residual
      -- `.const D` evaluates at any fuel to `none` or `some D`, never `some C`
      simp only [play, eval, eOfDefectδ, eδ, hps] at hn
      cases n with
      | zero => simp [eval] at hn
      | succ m => simp [eval] at hn

theorem ps_probe_eOfDefect (k m : Nat) :
    proofSearch m (probe (eOfDefectδ k)) = false := by
  cases h : proofSearch m (probe (eOfDefectδ k)) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_probe_eOfDefect_false k)

/-! ### The δ_C column's EBot bit -/

/-- `E(δ_C)` **DEFECTS via a FIRING exploit-probe**: `C(δ_D) = tauCoopδ` provably
    cooperates with a defector, so the first cascade guard fires and the
    then-branch `.const D` runs — the mechanism-faithful reading of base
    `EBot vs CooperateBot = (D, C)`. The bit is 0 at every budget. -/
theorem interp_probe_eOfCoop_false {k : Nat} (hk : 2 ≤ k) :
    ¬ (probe (eOfCoopδ k)).interp := by
  rintro ⟨n, hn⟩
  have hps : proofSearch k
      ((probe tauCoopδ).subst
        (.bot (.search k (probe tauCoopδ) (.const .D)
          (.search k (probe tauCoopδ) (.const .C) (.const .D))))
        (.bot (.search k (probe tauCoopδ) (.const .D)
          (.search k (probe tauCoopδ) (.const .C) (.const .D)))))
      = true := ps_probe_coop hk
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, eOfCoopδ, eδ, hps] at hn
  | n + 3 => simp [play, eval, eOfCoopδ, eδ, hps] at hn

theorem ps_probe_eOfCoop_false {k : Nat} (hk : 2 ≤ k) (m : Nat) :
    proofSearch m (probe (eOfCoopδ k)) = false := by
  cases h : proofSearch m (probe (eOfCoopδ k)) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_probe_eOfCoop_false hk)

/-! ### The δ_L column's EBot bit — THE FLOOR (the Gödelian pair)

`E(δ_L)` is the tau image of base `outcome_DupocBot_vs_EBot = (D, C)`: the
instance REALLY COOPERATES (`interp_probe_eOfSearch` — its exploit-probe of
Dupoc fails, its reciprocity-probe fires), yet its cooperation is UNPROVABLE at
any budget ≤ k (`ps_probe_eOfSearch_false`) — every certificate must cross the
failed exploit-search and pay the `search_f` floor `> k`
(`no_provable_botSearcherElse_tail`). A true bit that reads 0: exactly what the
2026-08-11 stipulation (a provable cooperator) papered over. -/

/-- The atom is TRUE: `E(δ_L)` plays C (through the failed exploit-probe). -/
theorem interp_probe_eOfSearch {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) :
    (probe (eOfSearchδ k)).interp := by
  have hps1 : proofSearch k
      ((probe (searchOfDefectδ k)).subst
        (.bot (.search k (probe (searchOfDefectδ k)) (.const .D)
          (.search k (probe (searchOfCoopδ k)) (.const .C) (.const .D))))
        (.bot (.search k (probe (searchOfDefectδ k)) (.const .D)
          (.search k (probe (searchOfCoopδ k)) (.const .C) (.const .D)))))
      = false := ps_probe_searchOfDefect k k
  have hps2 : proofSearch k
      ((probe (searchOfCoopδ k)).subst
        (.bot (.search k (probe (searchOfDefectδ k)) (.const .D)
          (.search k (probe (searchOfCoopδ k)) (.const .C) (.const .D))))
        (.bot (.search k (probe (searchOfDefectδ k)) (.const .D)
          (.search k (probe (searchOfCoopδ k)) (.const .C) (.const .D)))))
      = true := ps_probe_searchOfCoop hk hkk
  exact ⟨4, by simp [play, eval, eOfSearchδ, eδ, hps1, hps2]⟩

/-- The bit is 0: no proof of ≤ k characters concludes `E(δ_L)`'s cooperation —
    it sits behind the failed exploit-search, so any certificate pays the
    `search_f` floor. TauDupoc's budget-`k` probe honestly fails. -/
theorem ps_probe_eOfSearch_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (eOfSearchδ k)) = false := by
  cases h : proofSearch K (probe (eOfSearchδ k)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k (probe (searchOfDefectδ k))
        .D .C (.search k (probe (searchOfCoopδ k)) (.const .C) (.const .D))
        (by decide) (Nat.le_refl k)
        (.bot (eOfSearchδ k))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

end PD.Tau
