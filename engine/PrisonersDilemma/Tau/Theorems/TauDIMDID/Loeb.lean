import PrisonersDilemma.Tau.Theorems.TauDIMDID.Helpers

/-!
# Tau/Theorems/TauDIMDID/Loeb — the `dimdid × dimcid` pair, aligned on defection (2026-10-19)
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## dimdid × dimcid — ALIGNED ON DEFECTION, closed by mutual bounded Löb

Both members are `.impl`-guard searchers firing `D`; each guard's consequent is the other member's
THEN-play, so the boxed guards feed each other. Unlike `dimcid × cupod` (where Cupod's probe guard IS
the DIMCID member's self-play atom, so the one-sentence engine on that atom suffices), neither guard
here is an atom: the two SUBJECTS of the Löb cycle are the two CLOSED GUARDS themselves —
`Af` = the head member's, `Bf` = the partner's — and each leg is "the other member fires `D` at the
cross frame, weakened by `implK` into my implication guard". The cycle certifies the head member's
guard at a budget `≤ k/4`, so `Pf_mono` re-certifies it at the search budget `k` and `search_t`
fires: that is why the engine below is the public `mutual_pblt_engine_id` with its budget EXPOSED
(`4·m ≤ k`, the twin of `pblt_engine_id_bounded`) — a `∃ m` play witness is not enough when the
fixpoint is a guard rather than a play. -/

/-! ### The two member readings at an arbitrary opponent frame

`sys_cross_impl_dim` (`Tau/Theorems/Helpers.lean`) fixes the opponent to the member itself; the
cross legs need the member's play AGAINST THE PARTNER. Members are `.opp`-free, so
`botSysSearchStep` reads them at any frame with the same closed guard. -/

/-- DIMCID's member reading at an arbitrary opponent frame: □(its closed guard) → it plays `D`
    against `opp`. -/
theorem sys_cross_impl_dim_at (defs : ProgList) (i j : Nat) (k K : Nat) (opp : Prog)
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
             (.plays (.bot (.selfIdx j)) .self Action.D)) (.const .D) (.const .C)))
    (hK : (Formula.impl
        (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D)))
        (.plays (.bot (.sys defs i)) opp Action.D)).size ≤ K) :
    Pf K (.impl
      (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                     (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D)))
      (.plays (.bot (.sys defs i)) opp Action.D)) := by
  have h := Pf.botSysSearchStep defs i k
    (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
           (.plays (.bot (.selfIdx j)) .self Action.D)) .D .C
    (.bot (.sys defs i)) opp rfl hget
    (by simpa [sysClose_subst_cimSelfIdxD] using hK)
  rw [sysClose_subst_cimSelfIdxD] at h
  exact h

/-- DIMDID's member reading at an arbitrary opponent frame: □(its closed guard) → it plays `D`
    against `opp` (the twin of `sys_cross_impl_dim_at`, antecedent at `D`). -/
theorem sys_cross_impl_dd_at (defs : ProgList) (i j : Nat) (k K : Nat) (opp : Prog)
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.D)
             (.plays (.bot (.selfIdx j)) .self Action.D)) (.const .D) (.const .C)))
    (hK : (Formula.impl
        (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.D)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D)))
        (.plays (.bot (.sys defs i)) opp Action.D)).size ≤ K) :
    Pf K (.impl
      (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.D)
                     (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D)))
      (.plays (.bot (.sys defs i)) opp Action.D)) := by
  have h := Pf.botSysSearchStep defs i k
    (.impl (.plays .self (.bot (.selfIdx j)) Action.D)
           (.plays (.bot (.selfIdx j)) .self Action.D)) .D .C
    (.bot (.sys defs i)) opp rfl hget
    (by simpa [sysClose_subst_ddSelfIdx] using hK)
  rw [sysClose_subst_ddSelfIdx] at h
  exact h

/-! ### The mutual engine with its budget exposed -/

/-- `mutual_pblt_engine_id` (`Base/Loeb.lean`) with the fixpoint's budget REPORTED: the engine
    picks `m = 32768·V` under its own headroom `131072·V ≤ k`, so `4·m ≤ k` costs nothing — it
    just stops throwing the bound away (the mutual twin of `pblt_engine_id_bounded`). Needed here
    because the fixpoint is a GUARD that must be re-certified at the search budget `k`. Proof body
    identical to the public engine's. -/
theorem mutual_pblt_engine_id_bounded (Af Bf : Nat → Formula) (p₁ p₂ : Nat → Nat) (k₁ : Nat)
    (hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000)
    (hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000)
    (hp1 : ∀ k, p₁ k ≤ 100 * Nat.log2 k + 1000)
    (hp2 : ∀ k, p₂ k ≤ 100 * Nat.log2 k + 1000)
    (hL1 : ∀ k, k > k₁ → Pf (p₁ k) (.impl (.box k (Af k)) (Bf k)))
    (hL2 : ∀ k, k > k₁ → Pf (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 4 * m ≤ k ∧ Pf m (Af k) := by
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (131072 * 401) (131072 * 4016)
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hVk : 131072 * V ≤ k := by
    have h := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hVle : V ≤ 401 * Nat.log2 k + 4016 := by omega
    calc 131072 * V ≤ 131072 * (401 * Nat.log2 k + 4016) := Nat.mul_le_mul_left _ hVle
      _ = 131072 * 401 * Nat.log2 k + 131072 * 4016 := by ring
      _ ≤ k := h
  have hkk₁ : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  obtain ⟨fb, hfb⟩ : ∃ fb, 64 * V + fb = k := Nat.le.dest (by omega)
  have hLfb : Nat.log2 fb ≤ Nat.log2 k := log2_mono (by omega)
  have hLm : Nat.log2 (fb + 8*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLc : Nat.log2 (fb + 32*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn : Nat.log2 (16*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₁ : Nat.log2 (512*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLg : Nat.log2 (8192*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₃ : Nat.log2 (16384*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₅ : Nat.log2 (65536*V) ≤ Nat.log2 k := log2_mono (by omega)
  have s10 : Pf (160*V) (.impl (.box fb (Af k)) (Af k)) := by
    refine mutual_loeb (Af k) (Bf k) k k fb (16*V) (fb + 8*V) (fb + 32*V) (p₁ k) (p₂ k)
      (8*V) (16*V) (32*V) (16*V) (64*V) (16*V) (96*V) (8*V) (128*V) (160*V)
      (hL1 k hkk₁) (hL2 k hkk₁)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  refine ⟨32768*V, by omega, bloeb_engine (Af k) (160*V) fb
    (8192*V) (512*V) (16384*V) (16384*V) (65536*V)
    (256*V) (256*V) (1024*V) (512*V) (2048*V) (512*V) (512*V)
    (3072*V) (4096*V) (256*V) (5120*V) (6144*V) (7168*V) (16384*V) (32768*V)
    s10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [numCost, Formula.size]); omega

/-- The cheap budget-`k` re-certification of the DIMDID member's defection from its FIRED guard
    (`search_t` cites via `c_guard`) — the twin of `pf_dimcidSys_D_of_guard`. -/
theorem pf_ddSys_D_of_guard {defs : ProgList} {i j k : Nat}
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.D)
             (.plays (.bot (.selfIdx j)) .self Action.D)) (.const .D) (.const .C)))
    (hkk : c_guard k + 5
      + (Formula.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D).size ≤ k)
    (hAf : Pf k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.D)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D))) :
    Pf k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D) := by
  have hpre : Pf k (((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.D)
      (.plays (.bot (.selfIdx j)) .self Action.D)).sysClose defs).subst
      (.bot (.sys defs i)) (.bot (.sys defs i))) := by
    rw [sysClose_subst_ddSelfIdx]; exact hAf
  have h1 := PlaysProof.search_t (q := .const .C) hpre
    (PlaysProof.const (me := .bot (.sys defs i)) (opponent := .bot (.sys defs i))
      (a := Action.D))
  have hbody : PlaysProof (.bot (.sys defs i)) (.bot (.sys defs i)) (.sys defs i) Action.D
      (c_leaf + c_guard k + c_node + c_node) :=
    PlaysProof.sysStep hget (by simp only [Prog.sysClose]; exact h1)
  exact Pf.atom ⟨PlaysProof.bot hbody, by have := hcl; have := hcn; omega⟩

private theorem log_facts' (k : Nat) :
    Nat.log2 k ≤ k ∧ Nat.log2 0 = 0 ∧ Nat.log2 1 = 0 :=
  ⟨Nat.log2_le_self k, by decide, by decide⟩

/-! ### DIMDID at the head -/

/-- `inst .dimdid .dimcid`: DIMDID at the head. -/
def ddDiSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.D)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem inst_dimdid_dimcid_eq (k : Nat) : inst (tauZoo k) .dimdid .dimcid = .sys (ddDiSys k) 0 := rfl
theorem ddDiSys_get0 (k : Nat) :
    (ddDiSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.D)
                               (.plays (.bot (.selfIdx 1)) .self Action.D))
          (.const .D) (.const .C)) := rfl
theorem ddDiSys_get1 (k : Nat) :
    (ddDiSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.C)
                               (.plays (.bot (.selfIdx 0)) .self Action.D))
          (.const .D) (.const .C)) := rfl

/-- **The mutual engine, DIMDID-at-the-head**: `Af` = the DIMDID member's (0) closed guard,
    `Bf` = the DIMCID member's (1). Leg 1: □Af fires member 0 at the cross frame (`D` against
    member 1), weakened by `implK` into member 1's guard; leg 2: □Bf fires member 1 at the cross
    frame, weakened into member 0's guard. The guard is certified at a budget `≤ k/4`. -/
theorem ddDi_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, 4 * m ≤ k ∧
        Pf m (.impl (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D)
                    (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.D)) := by
  refine mutual_pblt_engine_id_bounded
    (fun k => .impl (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D)
                    (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.D))
    (fun k => .impl (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.C)
                    (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, ddDiSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, ddDiSys, numCost]; omega
  · -- leg 1: □(member 0's guard) → member 1's guard
    intro k _
    have h1 := sys_cross_impl_dd_at (ddDiSys k) 0 1 k _ (.bot (.sys (ddDiSys k) 1))
      (ddDiSys_get0 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D)
      (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.C)
      (k := (Formula.impl (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D)
        (.impl (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.C)
               (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    obtain ⟨h, h0, h1'⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, ddDiSys, numCost]; omega
  · -- leg 2: □(member 1's guard) → member 0's guard
    intro k _
    have h1 := sys_cross_impl_dim_at (ddDiSys k) 1 0 k _ (.bot (.sys (ddDiSys k) 0))
      (ddDiSys_get1 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.D)
      (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D)
      (k := (Formula.impl (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.D)
        (.impl (.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 1)) Action.D)
               (.plays (.bot (.sys (ddDiSys k) 1)) (.bot (.sys (ddDiSys k) 0)) Action.D))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    obtain ⟨h, h0, h1'⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, ddDiSys, numCost]; omega

/-- **τ(DIMDID) at DIMCID DEFECTS** (Löb-gated): the head member's guard is Löb-certified at a
    budget `≤ k/4`, re-certified at `k`, and `search_t` fires `D`. -/
theorem dimdid_dimcid_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dimdid .dimcid))
        (.bot (inst (tauZoo k) .dimdid .dimcid)) (inst (tauZoo k) .dimdid .dimcid)
        = some Action.D := by
  obtain ⟨kL, hLb⟩ := ddDi_mutual
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 5 100
  refine ⟨max kL kA, fun k hk => ?_⟩
  obtain ⟨m, hm4, hm⟩ := hLb k (by omega)
  have hkA' : 5 * Nat.log2 k + 100 ≤ k := hkA k (by omega)
  have hkk : c_guard k + 5
      + (Formula.plays (.bot (.sys (ddDiSys k) 0)) (.bot (.sys (ddDiSys k) 0))
          Action.D).size ≤ k := by
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [c_guard, numCost, Formula.size, Prog.size, ProgList.psize, ddDiSys]
    omega
  have hG := Pf_mono hm (show m ≤ k by omega)
  have hAf := pf_ddSys_D_of_guard (ddDiSys_get0 k) hkk hG
  rw [inst_dimdid_dimcid_eq k]
  exact entry_of_interp (Pf_sound k _ hAf)

/-! ### DIMCID at the head -/

/-- `inst .dimcid .dimdid`: DIMCID at the head. -/
def diDdSys (k : Nat) : ProgList :=
  .cons (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                          (.plays (.bot (.selfIdx 1)) .self Action.D))
    (.const .D) (.const .C))
  (.cons (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.D)
                           (.plays (.bot (.selfIdx 0)) .self Action.D))
    (.const .D) (.const .C)) .nil)

theorem inst_dimcid_dimdid_eq (k : Nat) : inst (tauZoo k) .dimcid .dimdid = .sys (diDdSys k) 0 := rfl
theorem diDdSys_get0 (k : Nat) :
    (diDdSys k).get? 0
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 1)) Action.C)
                               (.plays (.bot (.selfIdx 1)) .self Action.D))
          (.const .D) (.const .C)) := rfl
theorem diDdSys_get1 (k : Nat) :
    (diDdSys k).get? 1
      = some (.search k (.impl (.plays .self (.bot (.selfIdx 0)) Action.D)
                               (.plays (.bot (.selfIdx 0)) .self Action.D))
          (.const .D) (.const .C)) := rfl

/-- **The mutual engine, DIMCID-at-the-head**: `Af` = the DIMCID member's (0) closed guard,
    `Bf` = the DIMDID member's (1); the same two legs with the roles swapped. -/
theorem diDd_mutual :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ m, 4 * m ≤ k ∧
        Pf m (.impl (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.C)
                    (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D)) := by
  refine mutual_pblt_engine_id_bounded
    (fun k => .impl (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.C)
                    (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D))
    (fun k => .impl (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D)
                    (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.D))
    (fun k => 100 * Nat.log2 k + 1000) (fun k => 100 * Nat.log2 k + 1000) 0
    ?_ ?_ (fun k => le_rfl) (fun k => le_rfl) ?_ ?_
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, diDdSys, numCost]; omega
  · intro k; obtain ⟨h, h0, h1⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, diDdSys, numCost]; omega
  · -- leg 1: □(member 0's guard) → member 1's guard
    intro k _
    have h1 := sys_cross_impl_dim_at (diDdSys k) 0 1 k _ (.bot (.sys (diDdSys k) 1))
      (diDdSys_get0 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.D)
      (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D)
      (k := (Formula.impl (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.D)
        (.impl (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D)
               (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.D))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    obtain ⟨h, h0, h1'⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, diDdSys, numCost]; omega
  · -- leg 2: □(member 1's guard) → member 0's guard
    intro k _
    have h1 := sys_cross_impl_dd_at (diDdSys k) 1 0 k _ (.bot (.sys (diDdSys k) 0))
      (diDdSys_get1 k) le_rfl
    have h2 := Pf.implK
      (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D)
      (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.C)
      (k := (Formula.impl (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D)
        (.impl (.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 1)) Action.C)
               (.plays (.bot (.sys (diDdSys k) 1)) (.bot (.sys (diDdSys k) 0)) Action.D))).size)
      le_rfl
    have h3 := Pf.implTrans _ _ _ _ _ h1 h2 (Nat.le_refl _)
    refine Pf_mono h3 ?_
    obtain ⟨h, h0, h1'⟩ := log_facts' k
    simp only [Formula.size, Prog.size, ProgList.psize, diDdSys, numCost]; omega

/-- **τ(DIMCID) at DIMDID DEFECTS** (Löb-gated) — the same closure with DIMCID at the head
    (`pf_dimcidSys_D_of_guard` re-certifies its fired guard). -/
theorem dimcid_dimdid_plays_D :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ N, eval N (.bot (inst (tauZoo k) .dimcid .dimdid))
        (.bot (inst (tauZoo k) .dimcid .dimdid)) (inst (tauZoo k) .dimcid .dimdid)
        = some Action.D := by
  obtain ⟨kL, hLb⟩ := diDd_mutual
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 5 100
  refine ⟨max kL kA, fun k hk => ?_⟩
  obtain ⟨m, hm4, hm⟩ := hLb k (by omega)
  have hkA' : 5 * Nat.log2 k + 100 ≤ k := hkA k (by omega)
  have hkk : c_guard k + 5
      + (Formula.plays (.bot (.sys (diDdSys k) 0)) (.bot (.sys (diDdSys k) 0))
          Action.D).size ≤ k := by
    have h0 : Nat.log2 0 = 0 := by decide
    have h1 : Nat.log2 1 = 0 := by decide
    simp only [c_guard, numCost, Formula.size, Prog.size, ProgList.psize, diDdSys]
    omega
  have hG := Pf_mono hm (show m ≤ k by omega)
  have hAf := pf_dimcidSys_D_of_guard (diDdSys_get0 k) hkk hG
  rw [inst_dimcid_dimdid_eq k]
  exact entry_of_interp (Pf_sound k _ hAf)

end PD.Tau
