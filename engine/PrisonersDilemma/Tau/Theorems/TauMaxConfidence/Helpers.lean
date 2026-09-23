import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Loeb

/-!
# Tau/Theorems/TauMaxConfidence/Helpers — the `maxconfidence × dupoc` system

MaxConfidenceBot's test is Dupoc's, so its instances are Dupoc's by `rfl`
(`Zoo.lean`'s bridges) — EXCEPT where the two Dupoc-spec self-probers meet: the
compiler emits the symmetric 2-member system `cfdSys` (component `i` probes component
`1-i` with Dupoc's guard), the same term in both orientations. It is the simplest
mutual-Löb shape in the zoo — both cross-readings are `sys_cross_C_at`, no `.impl`
asymmetry (compare `dupoc_cimcic_mutual`) — and it closes on MUTUAL COOPERATION:
MaxConfidenceBot at point mass on Dupoc cooperates, and Dupoc at point mass on
MaxConfidenceBot cooperates, both past a budget threshold. The probe-level bit
(`ps_probe_inst_maxconfidence_dupoc`) is what the δ_L column and τ(Just)'s row consume.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem cfdSys_get0 (k : Nat) :
    (cfdSys k).get? 0
      = some (.search k (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C)
          (.const .C) (.const .D)) := rfl

theorem cfdSys_get1 (k : Nat) :
    (cfdSys k).get? 1
      = some (.search k (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) Action.C)
          (.const .C) (.const .D)) := rfl

/-- **The mutual engine** on the symmetric system: component 0's self-cooperation
    atom is provable past a threshold. (By symmetry so is component 1's, but the
    row only ever consults component 0 — both orientations are the same term.) -/
theorem maxconfidence_dupoc_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, Pf m (.plays (.bot (.sys (cfdSys k) 0)) (.bot (.sys (cfdSys k) 0)) Action.C) := by
  refine mutual_pblt_engine_id
    (fun k => .plays (.bot (.sys (cfdSys k) 0)) (.bot (.sys (cfdSys k) 0)) Action.C)
    (fun k => .plays (.bot (.sys (cfdSys k) 1)) (.bot (.sys (cfdSys k) 1)) Action.C)
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, cfdSys, numCost]
    omega
  · intro k
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, cfdSys, numCost]
    omega
  · -- □A₀ → A₁ : component 1 reads component 0's box and cooperates
    intro k _
    refine Pf_mono (sys_cross_C_at (cfdSys k) 1 0 k _ (.bot (.sys (cfdSys k) 1))
      (cfdSys_get1 k) le_rfl) ?_
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, cfdSys, numCost]
    omega
  · -- □A₁ → A₀ : component 0 reads component 1's box and cooperates
    intro k _
    refine Pf_mono (sys_cross_C_at (cfdSys k) 0 1 k _ (.bot (.sys (cfdSys k) 0))
      (cfdSys_get0 k) le_rfl) ?_
    have hlog := Nat.log2_le_self k
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [Formula.size, Prog.size, ProgList.psize, cfdSys, numCost]
    omega

/-- **MaxConfidenceBot at point mass on Dupoc COOPERATES** (Löb-gated). -/
theorem maxconfidence_dupoc_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .maxconfidence .dupoc))
        (.bot (inst (tauZoo k) .maxconfidence .dupoc)) (inst (tauZoo k) .maxconfidence .dupoc)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := maxconfidence_dupoc_mutual
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hLb k hk
  have hint : (probe (.sys (cfdSys k) 0)).interp := Pf_sound m _ hm
  rw [inst_maxconfidence_dupoc_eq k]
  exact entry_C_of_interp hint

/-- **Dupoc at point mass on MaxConfidenceBot COOPERATES** — the same term. -/
theorem dupoc_maxconfidence_plays_C :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .maxconfidence))
        (.bot (inst (tauZoo k) .dupoc .maxconfidence)) (inst (tauZoo k) .dupoc .maxconfidence)
        = some Action.C := by
  obtain ⟨kL, hLb⟩ := maxconfidence_dupoc_mutual
  refine ⟨kL, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hLb k hk
  have hint : (probe (.sys (cfdSys k) 0)).interp := Pf_sound m _ hm
  rw [inst_dupoc_maxconfidence_eq k]
  exact entry_C_of_interp hint

/-- The cheap budget-`k` certificate for component 0's cooperation from component
    1's provable cooperation: its guard fires (`search_t` cites via `c_guard`). -/
theorem pf_A0_of_A1_cd {k : Nat} (hkk : c_guard k + 5 ≤ k)
    (h1 : Pf k (.plays (.bot (.sys (cfdSys k) 1)) (.bot (.sys (cfdSys k) 1)) Action.C)) :
    Pf k (.plays (.bot (.sys (cfdSys k) 0)) (.bot (.sys (cfdSys k) 0)) Action.C) := by
  have hpre : Pf k (((Formula.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) Action.C).sysClose
      (cfdSys k)).subst (.bot (.sys (cfdSys k) 0)) (.bot (.sys (cfdSys k) 0))) := by
    rw [sysClose_subst_botSelfIdx]; exact h1
  have hs := PlaysProof.search_t (q := .const .D) hpre
    (PlaysProof.const (me := .bot (.sys (cfdSys k) 0)) (opponent := .bot (.sys (cfdSys k) 0))
      (a := Action.C))
  exact Pf.atom ⟨PlaysProof.bot (PlaysProof.sysStep (cfdSys_get0 k) hs),
    by have := hcl; have := hcn; omega⟩

/-- **THE LÖB BIT of the pair**: past a threshold the probe of `inst .maxconfidence .dupoc`
    fires AT THE PROBING BUDGET. Consumed by the δ_L column's `.maxconfidence` slot and by
    τ(Just)'s row. -/
theorem ps_probe_inst_maxconfidence_dupoc :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (probe (inst (tauZoo k) .maxconfidence .dupoc)) = true := by
  obtain ⟨kL, hLp⟩ := maxconfidence_dupoc_plays_C
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  refine ⟨max kL kA, fun k hk => ?_⟩
  have hplay := hLp k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hkk : c_guard k + 5 ≤ k := by simp only [c_guard, numCost]; omega
  rw [inst_maxconfidence_dupoc_eq k] at hplay
  have hfired := sysSearcher_fired_of_plays (by decide) _ _ (cfdSys_get0 k) hplay
  rw [sysClose_subst_botSelfIdx] at hfired
  rw [probe, inst_maxconfidence_dupoc_eq k]
  exact (proofSearch_spec _ _).2 (pf_A0_of_A1_cd hkk ((proofSearch_spec _ _).1 hfired))

/-- τ(Just) at MaxConfidenceBot: its third-party probe is aimed at the system, and fires
    exactly when the system's Löb bit does. -/
theorem ps_probe_just_maxconfidence {k : Nat} (hkk : c_guard k + 3 ≤ k)
    (hconf : proofSearch k (probe (inst (tauZoo k) .maxconfidence .dupoc)) = true) :
    proofSearch k (probe (inst (tauZoo k) .just .maxconfidence)) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot (PlaysProof.search_t ((proofSearch_spec _ _).1 hconf)
        PlaysProof.const),
      by
        have h1 : c_leaf = 1 := rfl
        have h2 : c_node = 1 := rfl
        have h3 : c_guard (tauZoo k).budget = c_guard k := rfl
        omega⟩)

end PD.Tau
