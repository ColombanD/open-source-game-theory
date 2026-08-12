import PrisonersDilemma.Tau.Defs
import PrisonersDilemma.Base.Soundness
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.Asymptotics

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

/-! ### TauEBot's bits

`TauEBotδ` is definitionally the same shape as `TauDupocδ` (both are the
self-probing quine `.search k (.plays .self .self C) C D`), so its Löb bit is
literally the same theorem — stated separately because the two are DIFFERENT
tau bots whose guard lists probe different columns, and a reader chasing
TauEBot should find its bit under its own name. -/

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

/-- TauEBot's quine bit — the same Löb argument as `ps_probe_quine`, restated
    for `TauEBotδ` (definitionally the same term; the bots differ in which
    column their guard lists probe, not in this instance). -/
theorem ps_probe_eQuine :
    ∃ k₂, ∀ k, k₂ < k → proofSearch k (probe (TauEBotδ k)) = true :=
  ps_probe_quine

/-- `Tp(δ_E)` / `L(δ_E)` **DEFECT**: their probe is about `.const D`, which is
    refutable, so the guard fails and the else-branch runs. The bit is 0. -/
theorem interp_probe_searchOfE_false (k : Nat) :
    ¬ (probe (searchOfEδ k)).interp := by
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
  | 2 => simp [play, eval, searchOfEδ, probeSearchδ, hps] at hn
  | n + 3 => simp [play, eval, searchOfEδ, probeSearchδ, hps] at hn

theorem ps_probe_searchOfE (k m : Nat) :
    proofSearch m (probe (searchOfEδ k)) = false := by
  cases h : proofSearch m (probe (searchOfEδ k)) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_probe_searchOfE_false k)

/-- `Ts(δ_E)` **DEFECTS**: it runs `.const D` and copies the defection.

    The `.ite` guard is a `.sim` of the frozen `.const D`, so at any fuel ≥ 2
    the guard yields `D ≠ C` and the else-branch `.const .D` runs. The deep
    case needs the inner `.bot`/`.const` unfolding supplied explicitly, since
    `simp` stops at the `bind`. -/
theorem interp_probe_simOfE_false : ¬ (probe simOfEδ).interp := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, simOfEδ, tftSimδ, tauDefectδ] at hn
  | 3 => simp [play, eval, simOfEδ, tftSimδ, tauDefectδ] at hn
  | n + 4 =>
      -- `.const` evaluates at ANY positive fuel; the residual here is `n`, so
      -- case on it rather than guessing an offset.
      cases n with
      | zero =>
          simp only [play, eval, simOfEδ, tftSimδ, tauDefectδ, Prog.subst] at hn
          simp at hn
      | succ m =>
          have hinner : eval (m + 1) (.bot (.const Action.D))
              (.bot (.const Action.D)) (.const Action.D) = some Action.D := rfl
          simp only [play, eval, simOfEδ, tftSimδ, tauDefectδ, Prog.subst,
            hinner] at hn
          exact absurd hn (by decide)

theorem ps_probe_simOfE (m : Nat) : proofSearch m (probe simOfEδ) = false := by
  cases h : proofSearch m (probe simOfEδ) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) interp_probe_simOfE_false

/-! ### The enlarged-zoo cross bits (2026-08-12)

The six-slot guard lists add two hypotheses: the δ_L column now holds an EBot
hypothesis, and the δ_C column does too. Both are decided by base cells:
`EBot vs DupocBot = (C, D)` fires, `EBot vs CooperateBot = (D, C)` does not. -/

/-- `E(δ_L)` **COOPERATES**: it probes `.const C`, which is certifiable. -/
theorem pf_probe_eOfSearch {k K : Nat} (hk : 2 ≤ k) (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (eOfSearchδ k)) :=
  pf_probe_searchOfCoop hk hK

theorem ps_probe_eOfSearch {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probe (eOfSearchδ k)) = true :=
  ps_probe_searchOfCoop hk hkk

/-- `E(δ_C)` **DEFECTS**: it probes `.const D`, refutable, so its guard fails.
    (`eOfCoopδ` is `searchOfEδ` up to the budget argument — same term.) -/
theorem ps_probe_eOfCoop_false (k m : Nat) :
    proofSearch m (probe (eOfCoopδ k)) = false :=
  ps_probe_searchOfE k m

end PD.Tau
