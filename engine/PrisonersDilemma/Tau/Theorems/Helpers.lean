import PrisonersDilemma.Tau.Zoo

/-!
# Tau/Theorems/Helpers — shared shape lemmas and the regime masses

The base-layout split of the tau mathematics (2026-08-18): `Tau/` holds only
definitions (machinery + the zoo); everything proved lives here under
`Tau/Theorems/`, one directory per bot, mirroring `Theorems/<Bot>/` for the base
zoo. THIS file is the shared floor: certificate lemmas for the compile IDIOMS
(probes of constants, prove-stages, run-stages, cascades — zoo-independent shapes),
the `massOf` reducers, and the two α-boundary masses. Bot-specific mathematics
lives in each bot's own `Helpers.lean` (Dupoc: the Löb quine; EBot: the Gödelian
floor pair); the cross-bot column theorems in `Columns.lean`; each bot's RESULT —
its phase theorem — in its `Phase.lean`; and the outcome matrix in `Matrix.lean`
(ONE file: tau plays are opponent-independent, so a per-pair file would have no
pair-local content — every cell is two phase theorems glued).
-/

open PD PD.BaseTheorems

namespace PD.Tau

@[simp] theorem massOf_ifC (w : Nat) :
    (if (Action.C == Action.C) = true then w else 0) = w := if_pos rfl

@[simp] theorem massOf_ifD (w : Nat) :
    (if (Action.D == Action.C) = true then w else 0) = 0 :=
  if_neg (by decide)

/-- Handy: the two cost constants, for `omega`. -/
theorem hcl : c_leaf = 1 := rfl
theorem hcn : c_node = 1 := rfl

/-! ## Shape lemmas — constants -/

/-- A frozen constant cooperator provably cooperates, from budget 2. -/
theorem pf_probe_constC {K : Nat} (hK : 2 ≤ K) :
    Pf K (probe (.const .C)) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by have := hcl; have := hcn; omega⟩

theorem ps_probe_constC {k : Nat} (hk : 2 ≤ k) :
    proofSearch k (probe (.const .C)) = true :=
  (proofSearch_spec _ _).2 (pf_probe_constC hk)

/-- A frozen constant defector never cooperates: the probe atom is FALSE… -/
theorem interp_probe_constD_false : ¬ (probe (.const .D)).interp := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | n + 2 => simp [play, eval] at hn

/-- …so its bit is 0 at EVERY budget (soundness). -/
theorem ps_probe_constD (m : Nat) :
    proofSearch m (probe (.const .D)) = false := by
  cases h : proofSearch m (probe (.const .D)) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) interp_probe_constD_false

/-! ## Shape lemmas — one prove-stage on a constant -/

/-- A prove-stage probing the constant cooperator fires: provable from
    `c_guard k + 3`. -/
theorem pf_searchProbe_constC {k K : Nat} (hk : 2 ≤ k)
    (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (.search k (probe (.const .C)) (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t (pf_probe_constC hk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_searchProbe_constC {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probe (.search k (probe (.const .C)) (.const .C) (.const .D)))
      = true :=
  (proofSearch_spec _ _).2 (pf_searchProbe_constC hk hkk)

/-- A prove-stage probing the constant defector FAILS and defects: its own probe
    atom is false… -/
theorem interp_searchProbe_constD_false (k : Nat) :
    ¬ (probe (.search k (probe (.const .D)) (.const .C) (.const .D))).interp := by
  rintro ⟨n, hn⟩
  have hps : proofSearch k
      ((probe (.const .D)).subst
        (.bot (.search k (probe (.const .D)) (.const .C) (.const .D)))
        (.bot (.search k (probe (.const .D)) (.const .C) (.const .D))))
      = false := ps_probe_constD k
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, hps] at hn
  | n + 3 => simp [play, eval, hps] at hn

theorem ps_searchProbe_constD (k m : Nat) :
    proofSearch m (probe (.search k (probe (.const .D)) (.const .C) (.const .D)))
      = false := by
  cases h : proofSearch m
      (probe (.search k (probe (.const .D)) (.const .C) (.const .D))) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_searchProbe_constD_false k)

/-! ## Shape lemmas — one run-stage on a constant -/

/-- A run-stage watching the constant cooperator copies the C: provable from 6. -/
theorem pf_simCopy_constC {K : Nat} (hK : 6 ≤ K) :
    Pf K (probe (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) rfl
      PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_simCopy_constC {k : Nat} (h6 : 6 ≤ k) :
    proofSearch k (probe (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .C) (.const .D))) = true :=
  (proofSearch_spec _ _).2 (pf_simCopy_constC h6)

/-- A run-stage watching the constant defector copies the D — bit 0 everywhere. -/
theorem interp_simCopy_constD_false :
    ¬ (probe (.ite (.sim (.bot (.const .D)) (.bot (.const .D))) Action.C
        (.const .C) (.const .D))).interp := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval] at hn
  | 3 => simp [play, eval] at hn
  | n + 4 =>
      cases n with
      | zero =>
          simp only [play, eval, Prog.subst] at hn
          simp at hn
      | succ m =>
          have hinner : eval (m + 1) (.bot (.const Action.D))
              (.bot (.const Action.D)) (.const Action.D) = some Action.D := rfl
          simp only [play, eval, Prog.subst, hinner] at hn
          exact absurd hn (by decide)

theorem ps_simCopy_constD (m : Nat) :
    proofSearch m (probe (.ite (.sim (.bot (.const .D)) (.bot (.const .D))) Action.C
      (.const .C) (.const .D))) = false := by
  cases h : proofSearch m
      (probe (.ite (.sim (.bot (.const .D)) (.bot (.const .D))) Action.C
        (.const .C) (.const .D))) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) interp_simCopy_constD_false

/-! ## Shape lemmas — the cascade on constants (τ(EBot)'s coop/defect/self cells) -/

/-- The cascade probed at the CONSTANT COOPERATOR defects via a FIRING exploit
    check — bit 0 (base `EBot vs CooperateBot = (D, C)`, mechanism-faithful). -/
theorem interp_cascade_constC_false {k : Nat} (hk : 2 ≤ k) :
    ¬ (probe (.search k (probe (.const .C)) (.const .D)
        (.search k (probe (.const .C)) (.const .C) (.const .D)))).interp := by
  rintro ⟨n, hn⟩
  have hps : proofSearch k
      ((probe (.const .C)).subst
        (.bot (.search k (probe (.const .C)) (.const .D)
          (.search k (probe (.const .C)) (.const .C) (.const .D))))
        (.bot (.search k (probe (.const .C)) (.const .D)
          (.search k (probe (.const .C)) (.const .C) (.const .D)))))
      = true := ps_probe_constC hk
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, hps] at hn
  | n + 3 => simp [play, eval, hps] at hn

theorem ps_cascade_constC_false {k : Nat} (hk : 2 ≤ k) (m : Nat) :
    proofSearch m (probe (.search k (probe (.const .C)) (.const .D)
      (.search k (probe (.const .C)) (.const .C) (.const .D)))) = false := by
  cases h : proofSearch m
      (probe (.search k (probe (.const .C)) (.const .D)
        (.search k (probe (.const .C)) (.const .C) (.const .D)))) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) (interp_cascade_constC_false hk)

/-- The cascade probed at the CONSTANT DEFECTOR falls through both stages — bit 0. -/
theorem interp_cascade_constD_false (k : Nat) :
    ¬ (probe (.search k (probe (.const .D)) (.const .D)
        (.search k (probe (.const .D)) (.const .C) (.const .D)))).interp := by
  rintro ⟨n, hn⟩
  have hps : proofSearch k
      ((probe (.const .D)).subst
        (.bot (.search k (probe (.const .D)) (.const .D)
          (.search k (probe (.const .D)) (.const .C) (.const .D))))
        (.bot (.search k (probe (.const .D)) (.const .D)
          (.search k (probe (.const .D)) (.const .C) (.const .D)))))
      = false := ps_probe_constD k
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | 2 => simp [play, eval, hps] at hn
  | n + 3 =>
      simp only [play, eval, hps] at hn
      cases n with
      | zero => simp [eval] at hn
      | succ m => simp [eval] at hn

theorem ps_cascade_constD_false (k m : Nat) :
    proofSearch m (probe (.search k (probe (.const .D)) (.const .D)
      (.search k (probe (.const .D)) (.const .C) (.const .D)))) = false := by
  cases h : proofSearch m
      (probe (.search k (probe (.const .D)) (.const .D)
        (.search k (probe (.const .D)) (.const .C) (.const .D)))) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) (interp_cascade_constD_false k)

/-! ## Shape lemmas — the δ_L column's two provable conditionals

Both probe `inst .dupoc .coop` — "Dupoc seeing the cooperator" — which is itself a
prove-stage on the constant cooperator; its bit is true, so the TFTs' instances
seeing Dupoc cooperate, provably. -/

theorem pf_simCopy_searchProbeC {k K : Nat} (hk : 2 ≤ k)
    (hK : c_guard k + 7 ≤ K) :
    Pf K (probe (.ite (.sim
      (.bot (.search k (probe (.const .C)) (.const .C) (.const .D)))
      (.bot (.search k (probe (.const .C)) (.const .C) (.const .D)))) Action.C
      (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t
      (PlaysProof.sim (PlaysProof.bot
        (PlaysProof.search_t (pf_probe_constC hk) PlaysProof.const)))
      rfl PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem pf_searchProbe_searchProbeC {k K : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (.search k
      (probe (.search k (probe (.const .C)) (.const .C) (.const .D)))
      (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.search_t (pf_searchProbe_constC hk hkk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

abbrev simMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + (w .obot + w .guardian)))))
abbrev pfMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + w .obot))))
abbrev dupMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + w .just)))
abbrev eMass (w : Tmpl → Nat) : Nat :=
  w .tftSim + (w .tftPf + (w .dupoc + (w .just + w .obot)))
abbrev guardMass (w : Tmpl → Nat) : Nat := simMass w
abbrev obotMass (w : Tmpl → Nat) : Nat := w .coop

/-! ## Shape lemmas — the `test = .D` idioms (9-zoo extension, 2026-08-18) -/

/-- The constant defector PROVABLY defects. -/
theorem pf_probeD_constD {K : Nat} (hK : 2 ≤ K) :
    Pf K (probeD (.const .D)) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by have := hcl; have := hcn; omega⟩

theorem ps_probeD_constD {k : Nat} (hk : 2 ≤ k) :
    proofSearch k (probeD (.const .D)) = true :=
  (proofSearch_spec _ _).2 (pf_probeD_constD hk)

/-- The cascade probed at the constant cooperator PROVABLY defects — its exploit
    check FIRES, and the firing transcript is cheap (`search_t` cites the probe of
    the constant). This is the bit GuardianBot reads to punish EBot. -/
theorem pf_probeD_cascadeConstC {k K : Nat} (hk : 2 ≤ k) (hK : c_guard k + 3 ≤ K) :
    Pf K (probeD (.search k (probe (.const .C)) (.const .D)
      (.search k (probe (.const .C)) (.const .C) (.const .D)))) :=
  Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t (pf_probe_constC hk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probeD_cascadeConstC {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probeD (.search k (probe (.const .C)) (.const .D)
      (.search k (probe (.const .C)) (.const .C) (.const .D)))) = true :=
  (proofSearch_spec _ _).2 (pf_probeD_cascadeConstC hk hkk)

/-- OBot's instance at the cooperator PROVABLY cooperates: both defection-watching
    stages see the constant cooperator cooperate and fall through to the trusting
    default; the transcript is two `ite_f`s over constant sims. -/
theorem pf_probe_obotConstC {K : Nat} (hK : 10 ≤ K) :
    Pf K (probe (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.D (.const .D)
      (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.D (.const .D)
        (.const .C)))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_f (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) (by decide)
      (PlaysProof.ite_f (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) (by decide)
        PlaysProof.const)),
    by have := hcl; have := hcn; omega⟩

theorem ps_probe_obotConstC {k : Nat} (h10 : 10 ≤ k) :
    proofSearch k (probe (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.D
      (.const .D) (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.D
        (.const .D) (.const .C)))) = true :=
  (proofSearch_spec _ _).2 (pf_probe_obotConstC h10)

end PD.Tau
