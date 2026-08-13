import PrisonersDilemma.Tau.SysDefs
import PrisonersDilemma.BaseTheorems

/-!
# Tau/SysCerts — the Def-5 σ-zoo certificate layer (milestone 1)

The parametric-weight analogues of `Tau/Certs`: shallow bits for the constant
members, the QUINE's Löb premise (via `botSysTsearchDefer` — the O(log k)
reading of member 2's source), `ps_probe_sysQuine` (bounded Löb through
`pblt_engine`, honest size bounds — a `.sys` probe carries the WHOLE system, so
the budget envelope's constant term depends on the weight parameters and the
threshold `k₂` depends on the weights; unlike Def 4 there is no weight-uniform
threshold, and that is the honest price of the binder), and the top player's
α-phase theorem.

REGIME (fixed by the Löb cost analysis + the eval inversion):
`dC + dT < θ₂ ≤ dC + dL` — the member-2 threshold is within the C+L mass
(cooperation commits at the deferred Löb guard) but above the C+T mass (the
threshold is unreachable WITHOUT the Löb bit, which is what makes the
play→bit inversion sound even though the behavioral T-bit is unknown).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Size bounds (the honest cost of the binder) -/

/-- `iteTree`'s size, bounded θ-uniformly by a fold over the guard sizes (the
    θ = 0 short-circuit is a single `.const`; each level duplicates the residual
    tree across the two branches). -/
theorem iteTree_size_le : ∀ (l : List (Nat × Prog)) (θ : Nat),
    (iteTree l θ).size ≤ l.foldr (fun p acc => p.2.size + 2 * acc + 1) 1
  | [], θ => by cases θ <;> simp [iteTree, Prog.size]
  | (w, g) :: rest, θ => by
      have hpos : ∀ l' : List (Nat × Prog),
          1 ≤ l'.foldr (fun p acc => p.2.size + 2 * acc + 1) 1 := by
        intro l'; induction l' with
        | nil => simp
        | cons hd tl ih => simp only [List.foldr]; omega
      cases θ with
      | zero =>
          simp only [iteTree, Prog.size, List.foldr]
          have := hpos rest
          omega
      | succ t =>
          simp only [iteTree, Prog.size, List.foldr]
          have h1 := iteTree_size_le rest (t + 1 - w)
          have h2 := iteTree_size_le rest (t + 1)
          omega

/-- The constant term of the σ-zoo's size envelope: the weight and threshold
    numerals (which the SYSTEM source carries — honest sizes) plus a generous
    structural constant. -/
def sysB (θ₂ θ₄ dC dD dL dT cC cD cL cT : Nat) : Nat :=
  4 * (numCost θ₂ + numCost θ₄ + numCost dC + numCost dD + numCost dL + numCost dT
     + numCost cC + numCost cD + numCost cL + numCost cT) + 4000

/-- A probe of any σ-zoo member fits the envelope `8·log₂ k + sysB`: the two
    copies of the system contribute `4·numCost k` (the two `.tsearch` budget
    literals, twice) plus the weight numerals plus θ-uniform `iteTree` bulk. -/
theorem probe_sysZoo_size_le (k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT i : Nat)
    (hi : i ≤ 6) :
    (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) i)).size
      ≤ 8 * Nat.log2 k + sysB θ₂ θ₄ dC dD dL dT cC cD cL cT := by
  -- literal numCosts (kernel-computed; `simp [Nat.log2]` would expose the raw rec)
  have hn0 : numCost 0 = 1 := by decide
  have hn1 : numCost 1 = 1 := by decide
  have hn2 : numCost 2 = 2 := by decide
  have hn3 : numCost 3 = 2 := by decide
  have hni : numCost i ≤ 4 := by
    have : ∀ j : Nat, j ≤ 6 → numCost j ≤ 4 := by decide
    exact this i hi
  -- the two behavioral members: θ-uniform iteTree bulk, weight-independent
  have h3 : (iteTree (sysTFTWatch dC dD dL dT) θ₃).size ≤ 200 := by
    refine le_trans (iteTree_size_le _ _) ?_
    have hb : ((sysTFTWatch dC dD dL dT).foldr
        (fun p acc => p.2.size + 2 * acc + 1) 1)
        = ((Prog.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))).size
          + 2 * ((Prog.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))).size
          + 2 * ((Prog.sim (.bot (.selfIdx 4)) (.bot (.selfIdx 4))).size
          + 2 * ((Prog.sim (.bot (.selfIdx 5)) (.bot (.selfIdx 5))).size
          + 2 * 1 + 1) + 1) + 1) + 1) := rfl
    rw [hb]
    have : ∀ j : Nat, j ≤ 6 →
        (Prog.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))).size ≤ 11 := by decide
    have g0 := this 0 (by omega); have g1 := this 1 (by omega)
    have g4 := this 4 (by omega); have g5 := this 5 (by omega)
    omega
  have h5 : (iteTree (sysTFTWatch cC cD cL cT) θ₅).size ≤ 200 := by
    refine le_trans (iteTree_size_le _ _) ?_
    have hb : ((sysTFTWatch cC cD cL cT).foldr
        (fun p acc => p.2.size + 2 * acc + 1) 1)
        = ((Prog.sim (.bot (.selfIdx 0)) (.bot (.selfIdx 0))).size
          + 2 * ((Prog.sim (.bot (.selfIdx 1)) (.bot (.selfIdx 1))).size
          + 2 * ((Prog.sim (.bot (.selfIdx 4)) (.bot (.selfIdx 4))).size
          + 2 * ((Prog.sim (.bot (.selfIdx 5)) (.bot (.selfIdx 5))).size
          + 2 * 1 + 1) + 1) + 1) + 1) := rfl
    rw [hb]
    have : ∀ j : Nat, j ≤ 6 →
        (Prog.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))).size ≤ 11 := by decide
    have g0 := this 0 (by omega); have g1 := this 1 (by omega)
    have g4 := this 4 (by omega); have g5 := this 5 (by omega)
    omega
  simp only [probe, Formula.size, Prog.size, sigmaZoo, ProgList.psize,
    sysDupocSig, GuardList.gsize, sysB] at *
  simp only [numCost] at *
  omega

/-! ## Shallow bits -/

/-- The C-member's probe is provable at any budget ≥ 3 (run it: `sysStep`
    through the `.bot` freeze, then the constant). Generic in the system. -/
theorem pf_probe_sysCoop (defs : ProgList) (h0 : defs.get? 0 = some (.const .C))
    (k : Nat) (hk : 3 ≤ k) : Pf k (probe (.sys defs 0)) :=
  .atom ⟨.bot (.sysStep h0 .const), by simp only [c_leaf, c_node]; omega⟩

/-- The D-member's probe is FALSE: the member plays D at every adequate fuel. -/
theorem interp_probe_sysDefect_false (defs : ProgList)
    (h1 : defs.get? 1 = some (.const .D)) :
    ¬ (probe (.sys defs 1)).interp := by
  rintro ⟨n, hn⟩
  have hD : eval (n + 1 + 1 + 1) (.bot (.sys defs 1)) (.bot (.sys defs 1))
      (.bot (.sys defs 1)) = some .D := by
    have s1 : eval (n + 1) (.bot (.sys defs 1)) (.bot (.sys defs 1))
        (.const .D) = some .D := by rw [eval]
    have s2 : eval (n + 1 + 1) (.bot (.sys defs 1)) (.bot (.sys defs 1))
        (.sys defs 1) = some .D := by
      rw [eval_sys_some (n + 1) h1]; exact s1
    rw [eval]; exact s2
  have hC := eval_mono_le hn (n + 1 + 1 + 1) (by omega)
  rw [hD] at hC
  exact absurd hC (by simp)

/-- The D-bit is `false` at every budget (soundness of the oracle). -/
theorem ps_probe_sysDefect_false (defs : ProgList)
    (h1 : defs.get? 1 = some (.const .D)) (k : Nat) :
    proofSearch k (probe (.sys defs 1)) = false := by
  cases h : proofSearch k (probe (.sys defs 1)) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) (interp_probe_sysDefect_false defs h1)

/-! ## The quine's Löb premise (O(log k), via `botSysTsearchDefer`) -/

/-- **THE LÖB PREMISE, parametric weights**: in the regime `dC < θ₂ ≤ dC + dL`,
    S reads member 2's source — the C-guard cited, the self-slot deferred as the
    `□`-antecedent, the peel committed at residual 0 before D/Ts — yielding
    `□_k φ₁ → φ₁` at `c_guard k + |conclusion|` transcript. -/
theorem sysQuine_loeb_premise (k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)
    (hθ₁ : dC < θ₂) (hθ₂ : θ₂ ≤ dC + dL) (hk : 3 ≤ k) (K : Nat)
    (hK : c_guard k +
      (Formula.impl
        (.box k (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2)))
        (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))).size ≤ K) :
    Pf K (.impl
      (.box k (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2)))
      (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))) := by
  exact Pf.botSysTsearchDefer k
    (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2 dC dL
    (probe (.selfIdx 0)) (probe (.selfIdx 2))
    (.cons dD (probe (.selfIdx 1)) (.cons dT (probe (.selfIdx 3)) .nil)) θ₂ .C .D
    (.bot (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))
    (.bot (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))
    rfl rfl
    (pf_probe_sysCoop _ rfl k hk)
    hθ₁ hθ₂ hK

/-! ## The quine bit (bounded Löb) -/

/-- Play→bit inversion for the quine: a real cooperative self-play of member 2
    forces the Löb bit, PROVIDED the threshold is unreachable without it
    (`dC + dT < θ₂` — the D-bit is refutably false, and even a firing T-bit
    leaves the residual positive). -/
theorem probe_true_of_sysQuine_play (k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)
    (hreg : dC + dT < θ₂) (hk : 3 ≤ k) (n : Nat)
    (hn : play n
      (.bot (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))
      (.bot (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2)) = some .C) :
    proofSearch k
      (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2)) = true := by
  set Z := sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT with hZ
  cases hL : proofSearch k (probe (.sys Z 2)) with
  | true => rfl
  | false =>
      exfalso
      have hbC : proofSearch k (probe (.sys Z 0)) = true :=
        (proofSearch_spec _ _).2 (pf_probe_sysCoop Z rfl k hk)
      have hbD : proofSearch k (probe (.sys Z 1)) = false :=
        ps_probe_sysDefect_false Z rfl k
      -- compute the play at generous fuel: the else-branch D
      have hC := eval_mono_le hn (n + 8) (by omega)
      have hstep : eval (n + 8) (.bot (.sys Z 2)) (.bot (.sys Z 2))
          (.bot (.sys Z 2)) = some .D := by
        rw [show eval (n + 8) (.bot (.sys Z 2)) (.bot (.sys Z 2)) (.bot (.sys Z 2))
              = eval (n + 7) (.bot (.sys Z 2)) (.bot (.sys Z 2)) (.sys Z 2) by rw [eval]]
        rw [eval_sys_some (n + 6)
          (rfl : Z.get? 2 = some (.tsearch k (sysDupocSig dC dD dL dT) θ₂
            (.const .C) (.const .D)))]
        show eval (n + 6) (.bot (.sys Z 2)) (.bot (.sys Z 2))
          (.tsearch k (.cons dC (probe (.sys Z 0))
            (.cons dL (probe (.sys Z 2))
              (.cons dD (probe (.sys Z 1))
                (.cons dT (probe (.sys Z 3)) .nil)))) θ₂ (.const .C) (.const .D))
          = some .D
        rw [eval_tsearch_cons_t (n + 5) (by omega) hbC]
        rw [eval_tsearch_cons_f (n + 4) (by omega) hL]
        rw [eval_tsearch_cons_f (n + 3) (by omega) hbD]
        cases hbT : proofSearch k (probe (.sys Z 3)) with
        | true =>
            rw [eval_tsearch_cons_t (n + 2) (by omega) hbT]
            rw [eval_tsearch_nil (n + 1) (by omega)]
            rw [eval]
        | false =>
            rw [eval_tsearch_cons_f (n + 2) (by omega) hbT]
            rw [eval_tsearch_nil (n + 1) (by omega)]
            rw [eval]
      rw [hstep] at hC
      exact absurd hC (by simp)

/-- **THE QUINE BIT** — Def-5 Löbian self-reference closes: past a
    weight-dependent threshold, member 2's own probe is provable AT THE PROBING
    BUDGET. Bounded Löb (`pblt_engine`) on the premise family from
    `sysQuine_loeb_premise`; the play witness inverts to the bit through the
    regime `dC + dT < θ₂ ≤ dC + dL`. -/
theorem ps_probe_sysQuine (θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)
    (hreg₁ : dC + dT < θ₂) (hreg₂ : θ₂ ≤ dC + dL) :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k
        (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2)) = true := by
  have hθ₁ : dC < θ₂ := by omega
  obtain ⟨B, hB⟩ : ∃ B, B = sysB θ₂ θ₄ dC dD dL dT cC cD cL cT := ⟨_, rfl⟩
  -- the premise transcript: c_guard k + |□_k φ₁ → φ₁| ≤ 18·log2 k + (2B + 20)
  obtain ⟨k₂, hk₂⟩ := pblt_engine
    (fun k => probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))
    id
    (fun k => c_guard k +
      (Formula.impl
        (.box k (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2)))
        (probe (.sys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) 2))).size)
    (max 3 (Classical.choose (linear_log2_add_le (8192 * 30) (8192 * (4 * B + 100)))))
    (fun k hk => sysQuine_loeb_premise k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT
      hθ₁ hreg₂ (by omega) _ le_rfl)
    (by
      intro k hk
      have hsz := probe_sysZoo_size_le k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT 2
        (by omega)
      have hlin := Classical.choose_spec
        (linear_log2_add_le (8192 * 30) (8192 * (4 * B + 100))) k
        (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
      simp only [id_eq]
      simp only [c_guard, numCost, Formula.size] at *
      omega)
  refine ⟨max k₂ 3, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  exact probe_true_of_sysQuine_play k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT hreg₁
    (by omega) n hn

/-! ## The top player's α-phase theorem -/

/-- **TauDupocSys α-phase theorem** (Def-5 milestone 1): past a weight-dependent
    budget threshold, the top player — probing the σ-zoo's members at free
    weights `w⃗` and threshold `θ` — cooperates against EVERY opponent when
    `θ ≤ wC + wL` (the C-bit and the Löbian quine bit alone carry the vote) and
    defects when `wC + wL + wT < θ` (unreachable even with the behavioral bit).
    The band between is the honest OPEN region (the T-bit is Gödelian). -/
theorem tauDupocSys_phase (θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)
    (hreg₁ : dC + dT < θ₂) (hreg₂ : θ₂ ≤ dC + dL) :
    ∃ k₂, ∀ k, k₂ < k → ∀ (wC wD wL wT θ : Nat) (opponent : Prog),
      (θ ≤ wC + wL → ∃ N, play N
        (TauDupocSys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) k wC wD wL wT θ)
        opponent = some .C)
      ∧ (wC + wL + wT < θ → ∃ N, play N
        (TauDupocSys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) k wC wD wL wT θ)
        opponent = some .D) := by
  obtain ⟨k₂, hquine⟩ := ps_probe_sysQuine θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT
    hreg₁ hreg₂
  refine ⟨max k₂ 3, fun k hk wC wD wL wT θ opponent => ?_⟩
  set Z := sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT with hZ
  have hbC : proofSearch k (probe (.sys Z 0)) = true :=
    (proofSearch_spec _ _).2 (pf_probe_sysCoop Z rfl k
      (le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk)))
  have hbL : proofSearch k (probe (.sys Z 2)) = true :=
    hquine k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hbD : proofSearch k (probe (.sys Z 1)) = false :=
    ps_probe_sysDefect_false Z rfl k
  constructor
  · -- cooperative leg: C and L carry the vote
    intro hθ
    refine ⟨6, ?_⟩
    show eval 6 _ opponent (.tsearch k (.cons wC (probe (.sys Z 0))
      (.cons wL (probe (.sys Z 2))
        (.cons wD (probe (.sys Z 1))
          (.cons wT (probe (.sys Z 3)) .nil)))) θ (.const .C) (.const .D))
      = some .C
    by_cases h0 : θ = 0
    · subst h0
      rw [show (6 : Nat) = 5 + 1 from rfl, eval_tsearch_zero 5, eval]
    · rw [show (6 : Nat) = 5 + 1 from rfl, eval_tsearch_cons_t 5 h0 hbC]
      by_cases h1 : θ - wC = 0
      · rw [show (5 : Nat) = 4 + 1 from rfl, h1, eval_tsearch_zero 4, eval]
      · rw [show (5 : Nat) = 4 + 1 from rfl, eval_tsearch_cons_t 4 h1 hbL]
        rw [show (4 : Nat) = 3 + 1 from rfl,
          show θ - wC - wL = 0 from by omega, eval_tsearch_zero 3, eval]
  · -- defect leg: the threshold is unreachable even with the behavioral bit
    intro hθ
    refine ⟨7, ?_⟩
    show eval 7 _ opponent (.tsearch k (.cons wC (probe (.sys Z 0))
      (.cons wL (probe (.sys Z 2))
        (.cons wD (probe (.sys Z 1))
          (.cons wT (probe (.sys Z 3)) .nil)))) θ (.const .C) (.const .D))
      = some .D
    rw [show (7 : Nat) = 6 + 1 from rfl, eval_tsearch_cons_t 6 (by omega) hbC]
    rw [show (6 : Nat) = 5 + 1 from rfl, eval_tsearch_cons_t 5 (by omega) hbL]
    rw [show (5 : Nat) = 4 + 1 from rfl, eval_tsearch_cons_f 4 (by omega) hbD]
    cases hbT : proofSearch k (probe (.sys Z 3)) with
    | true =>
        rw [show (4 : Nat) = 3 + 1 from rfl, eval_tsearch_cons_t 3 (by omega) hbT]
        rw [show (3 : Nat) = 2 + 1 from rfl, eval_tsearch_nil 2 (by omega)]
        rw [eval]
    | false =>
        rw [show (4 : Nat) = 3 + 1 from rfl, eval_tsearch_cons_f 3 (by omega) hbT]
        rw [show (3 : Nat) = 2 + 1 from rfl, eval_tsearch_nil 2 (by omega)]
        rw [eval]

end PD.Tau
