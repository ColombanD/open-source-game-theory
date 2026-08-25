import PrisonersDilemma.Tau.Zoo
import PrisonersDilemma.Base.Exclusion

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

/-- EBot's idiom fires: a run-stage testing COOPERATION plays its fire action when
    the watched instance cooperates (generic in the fire action — EBot's stage 1
    fires D, its stage 2 fires C)… -/
theorem simWatchC_fires {I : Prog} {f : Action} {cont : Prog} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.C) :
    ∃ N, eval N me opp (.ite (.sim (.bot I) (.bot I)) Action.C (.const f) cont)
      = some f := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 3, ?_⟩
  rw [eval]
  have hg : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some Action.C := by
    rw [eval]
    simp only [Prog.subst]
    rw [eval]
    exact eval_mono_le hN _ (by omega)
  rw [hg]
  simp only [bind, Option.bind]
  rw [if_pos (by decide)]
  rfl

/-- …and falls through to the continuation when it defects. -/
theorem simWatchC_falls {I : Prog} {f : Action} {cont : Prog} {a : Action}
    (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some Action.D)
    (hcont : ∃ N, eval N me opp cont = some a) :
    ∃ N, eval N me opp (.ite (.sim (.bot I) (.bot I)) Action.C (.const f) cont)
      = some a := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨M, hM⟩ := hcont
  refine ⟨max (N + 2) M + 1, ?_⟩
  rw [eval]
  have hg : eval (max (N + 2) M) me opp (.sim (.bot I) (.bot I)) = some Action.D := by
    have : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some Action.D := by
      rw [eval]
      simp only [Prog.subst]
      rw [eval]
      exact eval_mono_le hN _ (by omega)
    exact eval_mono_le this _ (Nat.le_max_left _ _)
  rw [hg]
  simp only [bind, Option.bind]
  rw [if_neg (by decide)]
  exact eval_mono_le hM _ (Nat.le_max_right _ _)

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

/-! ## `probeD` bits for the two idioms the δ_Cu column meets (2026-08-21) -/

/-- A prove-stage whose probe FAILS defects — through `search_f`, so the DEFECTION
    atom is itself floor-priced: unprovable at every budget ≤ k. The honest reading
    is "it defects, and you cannot cite that either". Uses the `botSearcherElse`
    kernel with the ELSE action as the target. -/
theorem ps_probeD_searchProbe_false {k K : Nat} (hK : K ≤ k) (I : Prog) :
    proofSearch K (probeD (.search k (probe I) (.const .C) (.const .D))) = false := by
  cases h : proofSearch K (probeD (.search k (probe I) (.const .C) (.const .D))) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k (probe I) .C .D (.const .D)
        (by decide) (Nat.le_refl k)
        (.bot (.search k (probe I) (.const .C) (.const .D)))
        K _ ((proofSearch_spec _ _).1 h) hK (by simp only [probeD, TailTo_plays])

/-- OBot's idiom, `probeD` side: the cascade PROVABLY defects when the first watch
    FALLS THROUGH (its instance cooperates) and the second FIRES (its instance
    defects) — `ite_f` over the first sim, then `ite_t` over the second.

    Transcript: `sim(bot hP) = m+2`, `sim(bot hQ) = n+2`, `ite_t = n+4`,
    `ite_f = m+n+7`, outer `bot = m+n+8`. -/
theorem pf_probeD_obotSecondFires {K m n : Nat} {P Q : Prog}
    (hP : PlaysProof (.bot P) (.bot P) P Action.C m)
    (hQ : PlaysProof (.bot Q) (.bot Q) Q Action.D n)
    (hK : m + n + 8 ≤ K) :
    Pf K (probeD (.ite (.sim (.bot P) (.bot P)) Action.D (.const .D)
      (.ite (.sim (.bot Q) (.bot Q)) Action.D (.const .D) (.const .C)))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_f (PlaysProof.sim (PlaysProof.bot hP)) (by decide)
      (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot hQ)) rfl PlaysProof.const)),
    by have := hcl; have := hcn; omega⟩

/-- The constant cooperator provably does NOT defect — the refutation that Cupod's
    trust-transcript cites (`search_f` needs a `.neg` of its guard). -/
theorem pf_neg_probeD_constC {K : Nat} (hK : 10 ≤ K) :
    Pf K (.neg (probeD (.const .C))) := by
  have hl : Nat.log2 1 = 0 := by decide
  refine Pf.atomNeg (.bot (.const .C)) (.bot (.const .C)) Action.C Action.D (atom_cost 1)
    ⟨PlaysProof.bot PlaysProof.const, ?_⟩ (by decide) ?_
  · simp only [atom_cost, c_leaf, c_node, c_guard, numCost, hl]; omega
  · simp only [Formula.size, Prog.size, atom_cost, c_leaf, c_node, c_guard, numCost, hl]
    omega

abbrev simMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + (w .obot +
    (w .guardian + (w .cupodTroll + (w .cupod + (w .cimcic +
      (w .dimcid + w .mirror))))))))))
abbrev pfMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + (w .obot + (w .cimcic + w .mirror))))))
abbrev dupMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + (w .cimcic + w .mirror)))))
/-- τ(EBot)'s mass. Since the THIRD stage was restored (2026-08-24, the `.mirror`
    template) it INCLUDES `w .ebot`: the mirror watch fires on E's own instance,
    so E cooperates with itself — the tau image of base
    `outcome_EBot_vs_EBot = (C, C)`, which the truncated two-stage lift got
    wrong. -/
abbrev eMass (w : Tmpl → Nat) : Nat :=
  w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + (w .just + (w .obot +
    (w .guardian + (w .cupod + (w .cimcic + (w .dimcid + (w .prudent + w .mirror)))))))))) 
/-- τ(Guardian)'s mass — `simMass` PLUS the prudent slot (2026-08-25): Guardian
    trusts τ(Prudent) (it cannot convict it of bullying the cooperator — its
    exploitation there is a floor-priced else-play), while TFTSim SEES Prudent
    defect on it. The two masses coincided until Prudent joined the roster. -/
abbrev guardMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + (w .obot +
    (w .guardian + (w .cupodTroll + (w .cupod + (w .cimcic +
      (w .dimcid + (w .prudent + w .mirror)))))))))))
abbrev obotMass (w : Tmpl → Nat) : Nat := w .coop + w .cupodTroll
/-- τ(Cupod)'s mass: everything but the provable bullies — the defector, ITSELF
    (the Löbian self-defection), and — since the 2026-08-24 `proveEq` restatement
    — τ(CupodTroll), which now recognises Cupod and defects on it. -/
abbrev cupodMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + (w .just +
    (w .obot + (w .guardian + (w .dbot + (w .cimcic + w .prudent)))))))))
/-- τ(DBot)'s mass: everything but the exploitable constant cooperator AND ITSELF
    (the punisher fires on its own trust — see `Theorems/TauDBot/Phase.lean`). -/
abbrev dbotMass (w : Tmpl → Nat) : Nat :=
  w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + (w .just +
    (w .obot + (w .guardian + (w .cupod + (w .cimcic +
      (w .dimcid + (w .prudent + w .mirror)))))))))))
/-- τ(CIMCIC)'s mass: the hypotheses whose consequent it can certify — the
    cooperator, both TFTs, the mutual-Löb Dupoc, Just (through the same Löb bit)
    and ITSELF (the `implRefl` diagonal). -/
abbrev cimcicMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .tftSim + (w .tftPf + (w .dupoc + (w .just + (w .cimcic + w .mirror)))))

/-! ## The `.sys` toolkit — entangled cells, generic in the system (2026-08-21)

The wrapped emission (`.bot (.selfIdx j)`, uniform with how off-cycle guards freeze
`.bot P`) makes every entangled guard a `probe`/`probeD` of the wrapped partner
component. Three generic lemmas then settle a whole class of cells:

* `sysClose_subst_botSelfIdx` — the closed-substituted guard form;
* `sysSearcher_plays_else` / `_then` — what a component actually plays;
* `ps_botSys_mismatch_false` — **the floor decides**: a probe aimed at a component
  whose then-action mismatches the target is FALSE at every budget up to the
  component's own (`no_provable_botSysSearcherElse_tail`). A 2-cycle whose actions
  do not align therefore has BOTH bits provably false — no bistability survives
  the `search_f` floor. -/

/-- `sysClose` sends a wrapped self-reference to the wrapped system, and `subst`
    cannot touch the `.bot` freeze. -/
theorem sysClose_subst_botSelfIdx (defs : ProgList) (j : Nat) (a : Action)
    (me o : Prog) :
    ((Formula.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a).sysClose defs).subst me o
      = .plays (.bot (.sys defs j)) (.bot (.sys defs j)) a := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]

/-- A system component that is a searcher with constant branches plays its ELSE
    action whenever its closed guard search fails… -/
theorem sysSearcher_plays_else {defs : ProgList} {i kb : Nat} {g : Formula}
    {aT aE : Action} (me opp : Prog)
    (hget : defs.get? i = some (.search kb g (.const aT) (.const aE)))
    (hps : proofSearch kb ((g.sysClose defs).subst me opp) = false) :
    ∃ N, eval N me opp (.sys defs i) = some aE := by
  refine ⟨3, ?_⟩
  rw [eval_sys_some 2 hget]
  simp only [Prog.sysClose]
  rw [eval, hps, if_neg (by simp)]
  rfl

/-- …and its THEN action whenever it fires. -/
theorem sysSearcher_plays_then {defs : ProgList} {i kb : Nat} {g : Formula}
    {aT aE : Action} (me opp : Prog)
    (hget : defs.get? i = some (.search kb g (.const aT) (.const aE)))
    (hps : proofSearch kb ((g.sysClose defs).subst me opp) = true) :
    ∃ N, eval N me opp (.sys defs i) = some aT := by
  refine ⟨3, ?_⟩
  rw [eval_sys_some 2 hget]
  simp only [Prog.sysClose]
  rw [eval, hps]
  rfl

/-- **The floor decides**: a plays-atom aimed at a `.bot`-wrapped component whose
    then-action mismatches the target action is FALSE at every budget ≤ k. -/
theorem ps_botSys_mismatch_false {k K : Nat} (hK : K ≤ k) (defs : ProgList)
    (i kb : Nat) (g : Formula) (aT aTgt : Action) (pE : Prog)
    (hne : aT ≠ aTgt) (hkb : k ≤ kb)
    (hget : defs.get? i = some (.search kb g (.const aT) pE)) (O : Prog) :
    proofSearch K (.plays (.bot (.sys defs i)) O aTgt) = false := by
  cases h : proofSearch K (.plays (.bot (.sys defs i)) O aTgt) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSysSearcherElse_tail k defs i kb g aT aTgt pE hne hkb hget O
        K _ ((proofSearch_spec _ _).1 h) hK rfl

/-- The closed-substituted form of the entangled CIMCIC guard. -/
theorem sysClose_subst_cimSelfIdx (defs : ProgList) (j : Nat) (me o : Prog) :
    ((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.C)
                   (.plays (.bot (.selfIdx j)) .self Action.C)).sysClose defs).subst me o
      = .impl (.plays me (.bot (.sys defs j)) Action.C)
              (.plays (.bot (.sys defs j)) me Action.C) := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]

/-- A searcher component's reading, at an arbitrary opponent frame and EITHER
    polarity: □(component `i` plays `aT` against itself) → component `j` plays `aT`
    against `opp`. Generic in the then/else actions — Dupoc's `(C, D)` and Cupod's
    `(D, C)` searchers are the same lemma. -/
theorem sys_cross_at (defs : ProgList) (j i : Nat) (k K : Nat) (opp : Prog) (aT aE : Action)
    (hget : defs.get? j = some (.search k
      (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) aT) (.const aT) (.const aE)))
    (hK : (Formula.impl
        (.box k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) aT))
        (.plays (.bot (.sys defs j)) opp aT)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) aT))
                (.plays (.bot (.sys defs j)) opp aT)) := by
  have h := Pf.botSysSearchStep defs j k
    (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) aT) aT aE
    (.bot (.sys defs j)) opp rfl hget
    (by simpa [sysClose_subst_botSelfIdx] using hK)
  rw [sysClose_subst_botSelfIdx] at h
  exact h

/-- Dupoc's side, at an arbitrary opponent frame: □(i cooperates) → j plays C
    against `opp`. (`sys_cross_at` at `(C, D)`.) -/
theorem sys_cross_C_at (defs : ProgList) (j i : Nat) (k K : Nat) (opp : Prog)
    (hget : defs.get? j = some (.search k
      (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) Action.C) (.const .C) (.const .D)))
    (hK : (Formula.impl
        (.box k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C))
        (.plays (.bot (.sys defs j)) opp Action.C)).size ≤ K) :
    Pf K (.impl (.box k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C))
                (.plays (.bot (.sys defs j)) opp Action.C)) :=
  sys_cross_at defs j i k K opp .C .D hget hK

/-- CIMCIC's side: □(its guard) → it cooperates (generic in the system). -/
theorem sys_cross_impl_cim (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
             (.plays (.bot (.selfIdx j)) .self Action.C)) (.const .C) (.const .D)))
    (hK : (Formula.impl
        (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.C)))
        (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)).size ≤ K) :
    Pf K (.impl
      (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                     (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.C)))
      (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.C)) := by
  have h := Pf.botSysSearchStep defs i k
    (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
           (.plays (.bot (.selfIdx j)) .self Action.C)) .C .D
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_cimSelfIdx] using hK)
  rw [sysClose_subst_cimSelfIdx] at h
  exact h

/-- The closed-substituted form of DIMCID's entangled guard (the asymmetric twin
    of `sysClose_subst_cimSelfIdx`). -/
theorem sysClose_subst_cimSelfIdxD (defs : ProgList) (j : Nat) (me o : Prog) :
    ((Formula.impl (.plays .self (.bot (.selfIdx j)) Action.C)
                   (.plays (.bot (.selfIdx j)) .self Action.D)).sysClose defs).subst me o
      = .impl (.plays me (.bot (.sys defs j)) Action.C)
              (.plays (.bot (.sys defs j)) me Action.D) := by
  simp [Formula.sysClose, Prog.sysClose, Formula.subst, Prog.subst]


/-- DIMCID's member reading, generic in the system: □(its closed guard) → it
    self-defects. -/
theorem sys_cross_impl_dim (defs : ProgList) (i j : Nat) (k K : Nat)
    (hget : defs.get? i = some (.search k
      (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
             (.plays (.bot (.selfIdx j)) .self Action.D)) (.const .D) (.const .C)))
    (hK : (Formula.impl
        (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                       (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D)))
        (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D)).size ≤ K) :
    Pf K (.impl
      (.box k (.impl (.plays (.bot (.sys defs i)) (.bot (.sys defs j)) Action.C)
                     (.plays (.bot (.sys defs j)) (.bot (.sys defs i)) Action.D)))
      (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) Action.D)) := by
  have h := Pf.botSysSearchStep defs i k
    (.impl (.plays .self (.bot (.selfIdx j)) Action.C)
           (.plays (.bot (.selfIdx j)) .self Action.D)) .D .C
    (.bot (.sys defs i)) (.bot (.sys defs i)) rfl hget
    (by simpa [sysClose_subst_cimSelfIdxD] using hK)
  rw [sysClose_subst_cimSelfIdxD] at h
  exact h

/-- A FORWARDER component's reading (`Pf.botSysSimStep`), at an arbitrary opponent
    frame and any action: component `j` plays `a` against itself → component `i`,
    a bare copy of `j`, plays `a` against `opp`. -/
theorem sys_mirror_fwd (defs : ProgList) (i j : Nat) (a : Action) (K : Nat) (opp : Prog)
    (hget : defs.get? i = some (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))))
    (hK : (Formula.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                        (.plays (.bot (.sys defs i)) opp a)).size ≤ K) :
    Pf K (.impl (.plays (.bot (.sys defs j)) (.bot (.sys defs j)) a)
                (.plays (.bot (.sys defs i)) opp a)) :=
  Pf.botSysSimStep defs i j a (.bot (.sys defs i)) opp rfl hget hK

/-! ## Forwarders — the bare `.sim` reads (τ(Mirror), 2026-08-24) -/

/-- A bare `.sim` over a frozen instance FORWARDS what that instance plays, in
    any frame — the behavioural read of a forwarder, both polarities at once. -/
theorem simFwd_plays {I : Prog} {a : Action} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some a) :
    ∃ N, eval N me opp (.sim (.bot I) (.bot I)) = some a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 2, ?_⟩
  rw [eval]
  simp only [Prog.subst]
  rw [eval]
  exact eval_mono_le hN _ (by omega)

/-- …and its transcript: the watched instance's own, plus a `bot` and a `sim`. -/
theorem playsProof_simFwd {I me opp : Prog} {a : Action} {m : Nat}
    (hw : PlaysProof (.bot I) (.bot I) I a m) :
    PlaysProof me opp (.sim (.bot I) (.bot I)) a (m + c_node + c_node) := by
  refine PlaysProof.sim ?_
  simp only [Prog.subst]
  exact PlaysProof.bot hw

/-- A true self-play atom gives a play witness, at either action
    (`entry_C_of_interp` generalised). -/
theorem entry_of_interp {I : Prog} {a : Action}
    (h : (Formula.plays (.bot I) (.bot I) a).interp) :
    ∃ N, eval N (.bot I) (.bot I) I = some a := by
  simp only [Formula.interp] at h
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [play, eval] at hn
  | succ m => exact ⟨m, by rw [play, eval] at hn; exact hn⟩

/-- A FORWARDER component PLAYS what its partner component self-plays. -/
theorem sysFwd_plays {defs : ProgList} {i j : Nat} {a : Action} (me opp : Prog)
    (hget : defs.get? i = some (.sim (.bot (.selfIdx j)) (.bot (.selfIdx j))))
    (h : ∃ N, eval N (.bot (.sys defs j)) (.bot (.sys defs j)) (.sys defs j) = some a) :
    ∃ N, eval N me opp (.sys defs i) = some a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 3, ?_⟩
  rw [eval_sys_some (N + 2) hget]
  simp only [Prog.sysClose]
  rw [eval]
  simp only [Prog.subst]
  rw [eval]
  exact eval_mono_le hN _ (by omega)

/-! ## Searcher heads — eval inversion and the fired-guard play (hoisted 2026-08-24) -/

/-- Eval inversion: a system component that plays its THEN action must have FIRED. -/
theorem sysSearcher_fired_of_plays {defs : ProgList} {i kb : Nat} {g : Formula}
    {aT aE : Action} (hne : aT ≠ aE) (me opp : Prog)
    (hget : defs.get? i = some (.search kb g (.const aT) (.const aE)))
    (h : ∃ N, eval N me opp (.sys defs i) = some aT) :
    proofSearch kb ((g.sysClose defs).subst me opp) = true := by
  cases hps : proofSearch kb ((g.sysClose defs).subst me opp) with
  | true => rfl
  | false =>
      exfalso
      obtain ⟨N, hN⟩ := h
      obtain ⟨M, hM⟩ := sysSearcher_plays_else me opp hget hps
      have h1 := eval_mono_le hN (max N M) (Nat.le_max_left _ _)
      have h2 := eval_mono_le hM (max N M) (Nat.le_max_right _ _)
      rw [h1] at h2
      exact hne (Option.some.inj h2)

/-- A searcher component at the head FIRES once its guard is provable at `k`:
    `search_t` cites the guard at `c_guard k` (a pointer, not the transcript), and
    the play is the then-constant. Generic in the polarity. -/
theorem sysSearcher_head_plays {defs : ProgList} {k i : Nat} {aT aE : Action}
    (hget : defs.get? 0 = some (.search k
      (.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) aT) (.const aT) (.const aE)))
    (hcg : c_leaf + c_guard k + c_node + c_node + c_node ≤ k)
    (hAf : Pf k (.plays (.bot (.sys defs i)) (.bot (.sys defs i)) aT)) :
    ∃ N, eval N (.bot (.sys defs 0)) (.bot (.sys defs 0)) (.sys defs 0) = some aT := by
  have hpre : Pf k (((Formula.plays (.bot (.selfIdx i)) (.bot (.selfIdx i)) aT).sysClose defs).subst
      (.bot (.sys defs 0)) (.bot (.sys defs 0))) := by
    rw [sysClose_subst_botSelfIdx]; exact hAf
  have h1 := PlaysProof.search_t (q := .const aE) hpre
    (PlaysProof.const (me := .bot (.sys defs 0)) (opponent := .bot (.sys defs 0)) (a := aT))
  have hbody : PlaysProof (.bot (.sys defs 0)) (.bot (.sys defs 0)) (.sys defs 0) aT
      (c_leaf + c_guard k + c_node + c_node) :=
    PlaysProof.sysStep hget (by simp only [Prog.sysClose]; exact h1)
  exact entry_of_interp (Pf_sound (c_leaf + c_guard k + c_node + c_node + c_node) _
    (Pf.atom ⟨PlaysProof.bot hbody, by omega⟩))

/-- The `c_guard` headroom every head-fires cell needs, past a threshold. -/
theorem cg_headroom : ∃ kC, ∀ k, kC ≤ k → c_leaf + c_guard k + c_node + c_node + c_node ≤ k := by
  obtain ⟨kC, hkC⟩ := linear_log2_add_le 200 4000
  refine ⟨kC, fun k hk => ?_⟩
  have := hkC k hk; have := hcl; have := hcn
  simp only [c_guard, numCost]; omega

/-! ## Shape lemmas — the `test = .D` idioms (9-zoo extension, 2026-08-18) -/

/-- The constant defector PROVABLY defects. -/
theorem pf_probeD_constD {K : Nat} (hK : 2 ≤ K) :
    Pf K (probeD (.const .D)) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by have := hcl; have := hcn; omega⟩

theorem ps_probeD_constD {k : Nat} (hk : 2 ≤ k) :
    proofSearch k (probeD (.const .D)) = true :=
  (proofSearch_spec _ _).2 (pf_probeD_constD hk)

/-- EBot's run cascade at the constant cooperator PROVABLY defects — its
    exploit-WATCH sees the cooperator cooperate and fires, and the firing
    transcript is a cheap positive `ite_t` over a constant sim. This is the bit
    GuardianBot reads to punish EBot. -/
theorem pf_probeD_runCascadeConstC {K : Nat} (hK : 6 ≤ K) (cont : Prog) :
    Pf K (probeD (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .D) cont)) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) rfl
      PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probeD_runCascadeConstC {k : Nat} (h6 : 6 ≤ k) (cont : Prog) :
    proofSearch k (probeD (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .D) cont)) = true :=
  (proofSearch_spec _ _).2 (pf_probeD_runCascadeConstC h6 cont)

/-- DBot's instance at the constant DEFECTOR provably cooperates: its watch sees
    the defector defect (an `ite_f` over a constant sim) and falls through to the
    trusting default. -/
theorem pf_probe_dbotConstD {K : Nat} (hK : 6 ≤ K) :
    Pf K (probe (.ite (.sim (.bot (.const .D)) (.bot (.const .D))) Action.C
      (.const .D) (.const .C))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_f (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) (by decide)
      PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probe_dbotConstD {k : Nat} (h6 : 6 ≤ k) :
    proofSearch k (probe (.ite (.sim (.bot (.const .D)) (.bot (.const .D))) Action.C
      (.const .D) (.const .C))) = true :=
  (proofSearch_spec _ _).2 (pf_probe_dbotConstD h6)

/-- DBot's instance at the constant COOPERATOR provably DEFECTS: its watch fires
    (an `ite_t` over a constant sim). The bit GuardianBot reads to punish DBot. -/
theorem pf_probeD_dbotConstC {K : Nat} (hK : 6 ≤ K) :
    Pf K (probeD (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .D) (.const .C))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) rfl
      PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

theorem ps_probeD_dbotConstC {k : Nat} (h6 : 6 ≤ k) :
    proofSearch k (probeD (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .D) (.const .C))) = true :=
  (proofSearch_spec _ _).2 (pf_probeD_dbotConstC h6)

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
