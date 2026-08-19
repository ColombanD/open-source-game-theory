import PrisonersDilemma.Tau.Zoo

/-!
# Tau/Theorems/Helpers — shared shape lemmas and the regime masses

The base-layout split of the tau mathematics (2026-08-18): `Tau/` holds only
definitions (machinery + the zoo); everything proved lives here under
`Tau/Theorems/`, one directory per bot, mirroring `Theorems/<Bot>/` for the base
zoo. THIS file is the shared floor: the generic play-lemmas for the compile
IDIOMS (what a prove-stage/run-stage/cascade PLAYS, given its probe bits), the
generic false-bit lemmas (a probe is refuted by any witness of the opposite play —
`eval_det`), the constant-instance bit certificates, the probe ↔ entry bridge and
outcome glue, the `massOf` reducers, and the regime masses. Bot-specific mathematics
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

theorem outcome_of_ex_plays {A B : Prog} {a b : Action}
    (hA : ∃ N, play N A B = some a) (hB : ∃ N, play N B A = some b) :
    ∃ N, outcome N A B = some (a, b) := by
  obtain ⟨N₁, h₁⟩ := hA
  obtain ⟨N₂, h₂⟩ := hB
  refine ⟨max N₁ N₂, ?_⟩
  have h₁' : play (max N₁ N₂) A B = some a := eval_mono_le h₁ _ (Nat.le_max_left _ _)
  have h₂' : play (max N₁ N₂) B A = some b := eval_mono_le h₂ _ (Nat.le_max_right _ _)
  simp [outcome, h₁', h₂']

/-! ## The probe ↔ entry bridge

A `.tvote` entry runs `.bot`-framed, which is LITERALLY the probe atom's frame. So
every bit lemma the tau layer already proves about `probe I` is a fact about the
entry `I`, one `.bot` unfolding apart. This is what lets the whole `Certs` layer be
reused verbatim under the refined definition. -/

/-- A true probe atom gives a cooperating entry. -/
theorem entry_C_of_interp {I : Prog} (h : (probe I).interp) :
    ∃ N, eval N (.bot I) (.bot I) I = some Action.C := by
  simp only [probe, Formula.interp] at h
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [play, eval] at hn
  | succ m => exact ⟨m, by rw [play, eval] at hn; exact hn⟩

/-! ## Shape play-lemmas

What each COMPILE IDIOM plays, given its probe bits. Stated over the explicit `Prog`
shapes the Spec compiler emits (a prove-stage, the two-stage cascade, a run-stage) —
no zoo vocabulary, so they apply to any zoo's compiled entries by defeq. Probes are
closed (`probe_subst`), so a shape's play never depends on the frame it is consulted
from — the term-level reason a tau player's action depends on its signal alone. -/

/-- A single prove-stage (`.search` on a probe, constant branches) cooperates exactly
    when its probe fires… -/
theorem searchProbe_plays_C {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probe I) = true) :
    ∃ N, eval N me opp (.search k (probe I) (.const .C) (.const .D)) = some Action.C := by
  refine ⟨2, ?_⟩
  rw [eval, probe_subst, h]
  rfl

/-- …and defects when it does not. -/
theorem searchProbe_plays_D {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probe I) = false) :
    ∃ N, eval N me opp (.search k (probe I) (.const .C) (.const .D)) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, probe_subst, h, if_neg (by simp)]
  rfl

/-- The two-stage exploiter cascade DEFECTS when its exploit-probe fires… -/
theorem cascade_plays_D_of_exploit {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = true) :
    ∃ N, eval N me opp (.search k (probe I_D) (.const .D)
      (.search k (probe I_C) (.const .C) (.const .D))) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, probe_subst, h1]
  rfl

/-- …COOPERATES when the exploit fails but reciprocity fires… -/
theorem cascade_plays_C {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = false)
    (h2 : proofSearch k (probe I_C) = true) :
    ∃ N, eval N me opp (.search k (probe I_D) (.const .D)
      (.search k (probe I_C) (.const .C) (.const .D))) = some Action.C := by
  refine ⟨3, ?_⟩
  rw [eval, probe_subst, h1, if_neg (by simp), eval, probe_subst, h2]
  rfl

/-- …and DEFECTS when neither fires. -/
theorem cascade_plays_D_of_both_false {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = false)
    (h2 : proofSearch k (probe I_C) = false) :
    ∃ N, eval N me opp (.search k (probe I_D) (.const .D)
      (.search k (probe I_C) (.const .C) (.const .D))) = some Action.D := by
  refine ⟨3, ?_⟩
  rw [eval, probe_subst, h1, if_neg (by simp), eval, probe_subst, h2,
      if_neg (by simp)]
  rfl

/-- A run-stage (`.ite` over a frozen self-sim) COPIES what its probed instance
    plays — the behavioral read: true plays, floor-blind. -/
theorem simCopy_plays {I : Prog} {a : Action} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some a) :
    ∃ N, eval N me opp (.ite (.sim (.bot I) (.bot I)) Action.C (.const .C) (.const .D))
      = some a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 3, ?_⟩
  rw [eval]
  have hg : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some a := by
    rw [eval]
    simp only [Prog.subst]
    rw [eval]
    exact eval_mono_le hN _ (by omega)
  rw [hg]
  cases a with
  | C => simp only [bind, Option.bind]; rw [if_pos (by decide)]; rfl
  | D => simp only [bind, Option.bind]; rw [if_neg (by decide)]; rfl

/-! ## The generic false-bit lemmas

`eval` is a function (`eval_det`, in `Base/ValuationSoundness`), so a program has ONE
play — which makes "the probe atom is false" derivable from ANY witness of the
opposite play, killing the per-shape match-on-fuel proofs for every negative bit. -/

/-- A D-playing instance's COOPERATION probe is false… -/
theorem interp_probe_false_of_plays_D {I : Prog}
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.D) :
    ¬ (probe I).interp := by
  rintro ⟨n, hn⟩
  obtain ⟨N, hN⟩ := h
  have hplay : eval (n+1) (.bot I) (.bot I) (.bot I) = some Action.C := by
    cases n with
    | zero => simp [play, eval] at hn
    | succ m => exact eval_mono_le hn _ (by omega)
  have hN' : eval (N+1) (.bot I) (.bot I) (.bot I) = some Action.D := by
    rw [eval]; exact hN
  exact absurd (eval_det hplay hN') (by decide)

/-- …and unprovable at every budget (soundness). -/
theorem ps_probe_false_of_plays_D {I : Prog} (m : Nat)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.D) :
    proofSearch m (probe I) = false := by
  cases hps : proofSearch m (probe I) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ hps) (interp_probe_false_of_plays_D h)

/-- A C-playing instance's DEFECTION probe is false… -/
theorem interp_probeD_false_of_plays_C {I : Prog}
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.C) :
    ¬ (probeD I).interp := by
  rintro ⟨n, hn⟩
  obtain ⟨N, hN⟩ := h
  have hplay : eval (n+1) (.bot I) (.bot I) (.bot I) = some Action.D := by
    cases n with
    | zero => simp [play, eval] at hn
    | succ m => exact eval_mono_le hn _ (by omega)
  have hN' : eval (N+1) (.bot I) (.bot I) (.bot I) = some Action.C := by
    rw [eval]; exact hN
  exact absurd (eval_det hplay hN') (by decide)

/-- …and unprovable at every budget (soundness). -/
theorem ps_probeD_false_of_plays_C {I : Prog} (m : Nat)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.C) :
    proofSearch m (probeD I) = false := by
  cases hps : proofSearch m (probeD I) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ hps) (interp_probeD_false_of_plays_C h)

/-! ## Shape play-lemmas for the `test = .D` idioms -/

/-- GuardianBot's idiom fires: a prove-stage on a DEFECTION atom plays its
    punishment when the atom is provable… -/
theorem searchProbeD_plays_D {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probeD I) = true) :
    ∃ N, eval N me opp (.search k (probeD I) (.const .D) (.const .C)) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, probeD_subst, h]
  rfl

/-- …and trusts (plays C) when it is not. -/
theorem searchProbeD_plays_C {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probeD I) = false) :
    ∃ N, eval N me opp (.search k (probeD I) (.const .D) (.const .C)) = some Action.C := by
  refine ⟨2, ?_⟩
  rw [eval, probeD_subst, h, if_neg (by simp)]
  rfl

/-- OBot's idiom fires: a run-stage testing DEFECTION plays its fire action when the
    watched instance defects… -/
theorem simTestD_fires {I : Prog} {cont : Prog} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.D) :
    ∃ N, eval N me opp (.ite (.sim (.bot I) (.bot I)) Action.D (.const .D) cont)
      = some Action.D := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 3, ?_⟩
  rw [eval]
  have hg : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some Action.D := by
    rw [eval]
    simp only [Prog.subst]
    rw [eval]
    exact eval_mono_le hN _ (by omega)
  rw [hg]
  simp only [bind, Option.bind]
  rw [if_pos (by decide)]
  rfl

/-- …and falls through to the continuation when it cooperates. -/
theorem simTestD_falls {I : Prog} {cont : Prog} {a : Action} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.C)
    (hcont : ∃ N, eval N me opp cont = some a) :
    ∃ N, eval N me opp (.ite (.sim (.bot I) (.bot I)) Action.D (.const .D) cont)
      = some a := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨M, hM⟩ := hcont
  refine ⟨max (N + 2) M + 1, ?_⟩
  rw [eval]
  have hg : eval (max (N + 2) M) me opp (.sim (.bot I) (.bot I)) = some Action.C := by
    have : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some Action.C := by
      rw [eval]
      simp only [Prog.subst]
      rw [eval]
      exact eval_mono_le hN _ (by omega)
    exact eval_mono_le this _ (Nat.le_max_left _ _)
  rw [hg]
  simp only [bind, Option.bind]
  rw [if_neg (by decide)]
  exact eval_mono_le hM _ (Nat.le_max_right _ _)

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
