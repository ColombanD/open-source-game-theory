import PrisonersDilemma.Tau.Zoo
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Certs — the bit mathematics, stated over the COMPILED instances

Since the 2026-08-18 cleanup this is the ONLY certificate layer: the hand-written
δ-closure and its named lemmas are gone, and every statement here speaks the DSL
vocabulary `inst (zoo6 k) T X`. Organization:

* **shape lemmas** (private): the recurring certificate patterns, stated over the
  explicit `Prog` shapes the compiler emits — a probe of a constant, of a
  prove-stage, of a run-stage, of the cascade. Zoo-independent.
* **the three consulted COLUMNS** (public API): `ps_probe_inst_coop` / `_defect` /
  `_dupoc` — one quantified theorem per question the zoo's specs ask, each arm a
  shape lemma bridged by defeq (the `Zoo.lean` peel equations pin the shapes).
* **the Löb quine** (`ps_probe_inst_quine`) and **the Gödelian floor pair**
  (`interp_probe_inst_ebot_dupoc` + `ps_probe_inst_ebot_dupoc_false`) — the two
  cells where the real mathematics lives.
* **the behavioral δ_C column** (`inst_coop_plays`) and the quine entry's play.

Scope (unchanged): only CONSULTED columns. A full 6×6 bit table would need floor
and certificate lemmas for cells no spec probes; write a column's lemmas when a
spec first consults it.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- Handy: the two cost constants, for `omega`. -/
private theorem hcl : c_leaf = 1 := rfl
private theorem hcn : c_node = 1 := rfl

/-! ## Shape lemmas — constants -/

/-- A frozen constant cooperator provably cooperates, from budget 2. -/
private theorem pf_probe_constC {K : Nat} (hK : 2 ≤ K) :
    Pf K (probe (.const .C)) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by have := hcl; have := hcn; omega⟩

private theorem ps_probe_constC {k : Nat} (hk : 2 ≤ k) :
    proofSearch k (probe (.const .C)) = true :=
  (proofSearch_spec _ _).2 (pf_probe_constC hk)

/-- A frozen constant defector never cooperates: the probe atom is FALSE… -/
private theorem interp_probe_constD_false : ¬ (probe (.const .D)).interp := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => simp [play, eval] at hn
  | 1 => simp [play, eval] at hn
  | n + 2 => simp [play, eval] at hn

/-- …so its bit is 0 at EVERY budget (soundness). -/
private theorem ps_probe_constD (m : Nat) :
    proofSearch m (probe (.const .D)) = false := by
  cases h : proofSearch m (probe (.const .D)) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) interp_probe_constD_false

/-! ## Shape lemmas — one prove-stage on a constant -/

/-- A prove-stage probing the constant cooperator fires: provable from
    `c_guard k + 3`. -/
private theorem pf_searchProbe_constC {k K : Nat} (hk : 2 ≤ k)
    (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (.search k (probe (.const .C)) (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot (PlaysProof.search_t (pf_probe_constC hk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

private theorem ps_searchProbe_constC {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) :
    proofSearch k (probe (.search k (probe (.const .C)) (.const .C) (.const .D)))
      = true :=
  (proofSearch_spec _ _).2 (pf_searchProbe_constC hk hkk)

/-- A prove-stage probing the constant defector FAILS and defects: its own probe
    atom is false… -/
private theorem interp_searchProbe_constD_false (k : Nat) :
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

private theorem ps_searchProbe_constD (k m : Nat) :
    proofSearch m (probe (.search k (probe (.const .D)) (.const .C) (.const .D)))
      = false := by
  cases h : proofSearch m
      (probe (.search k (probe (.const .D)) (.const .C) (.const .D))) with
  | false => rfl
  | true =>
      exact absurd (proofSearch_sound _ _ h) (interp_searchProbe_constD_false k)

/-! ## Shape lemmas — one run-stage on a constant -/

/-- A run-stage watching the constant cooperator copies the C: provable from 6. -/
private theorem pf_simCopy_constC {K : Nat} (hK : 6 ≤ K) :
    Pf K (probe (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) rfl
      PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

private theorem ps_simCopy_constC {k : Nat} (h6 : 6 ≤ k) :
    proofSearch k (probe (.ite (.sim (.bot (.const .C)) (.bot (.const .C))) Action.C
      (.const .C) (.const .D))) = true :=
  (proofSearch_spec _ _).2 (pf_simCopy_constC h6)

/-- A run-stage watching the constant defector copies the D — bit 0 everywhere. -/
private theorem interp_simCopy_constD_false :
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

private theorem ps_simCopy_constD (m : Nat) :
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
private theorem interp_cascade_constC_false {k : Nat} (hk : 2 ≤ k) :
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

private theorem ps_cascade_constC_false {k : Nat} (hk : 2 ≤ k) (m : Nat) :
    proofSearch m (probe (.search k (probe (.const .C)) (.const .D)
      (.search k (probe (.const .C)) (.const .C) (.const .D)))) = false := by
  cases h : proofSearch m
      (probe (.search k (probe (.const .C)) (.const .D)
        (.search k (probe (.const .C)) (.const .C) (.const .D)))) with
  | false => rfl
  | true => exact absurd (proofSearch_sound _ _ h) (interp_cascade_constC_false hk)

/-- The cascade probed at the CONSTANT DEFECTOR falls through both stages — bit 0. -/
private theorem interp_cascade_constD_false (k : Nat) :
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

private theorem ps_cascade_constD_false (k m : Nat) :
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

private theorem pf_simCopy_searchProbeC {k K : Nat} (hk : 2 ≤ k)
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

private theorem pf_searchProbe_searchProbeC {k K : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (hK : c_guard k + 3 ≤ K) :
    Pf K (probe (.search k
      (probe (.search k (probe (.const .C)) (.const .C) (.const .D)))
      (.const .C) (.const .D))) :=
  Pf.atom ⟨PlaysProof.bot
    (PlaysProof.search_t (pf_searchProbe_constC hk hkk) PlaysProof.const),
    by have := hcl; have := hcn; omega⟩

/-! ## The Löb quine — τ(Dupoc)'s diagonal -/

/-- The Löb premise for the quine fixpoint: S reads the frozen searcher's own
    source (`botSearchStep`) and concludes `□_k φ* → φ*` for
    `φ* = probe (inst .dupoc .dupoc)` — the guard sentence IS the probe atom,
    because `subst` closes the quine's `.self` to the wrapped player. -/
private theorem quine_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (probe (inst (zoo6 k) .dupoc .dupoc)))
             (probe (inst (zoo6 k) .dupoc .dupoc))) :=
  Pf.botSearchStep k (.plays .self .self .C) .C .D
    (.bot (inst (zoo6 k) .dupoc .dupoc)) (.bot (inst (zoo6 k) .dupoc .dupoc)) rfl
    (by
      simp only [inst_dupoc_quine, Formula.subst, Prog.subst, Formula.size,
        Prog.size, numCost]
      omega)

/-- From an actual cooperative play of the wrapped quine against itself, the guard
    must have fired (eval inversion — a false guard forces D). -/
private theorem probe_true_of_quine_play (k n : Nat)
    (h : play n (.bot (inst (zoo6 k) .dupoc .dupoc))
           (.bot (inst (zoo6 k) .dupoc .dupoc)) = some .C) :
    proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true := by
  cases hps : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) with
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
      proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true := by
  have hφsz : ∀ k, (probe (inst (zoo6 k) .dupoc .dupoc)).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [probe, inst_dupoc_quine, Formula.size, Prog.size, numCost]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150)
        (.impl (.box k (probe (inst (zoo6 k) .dupoc .dupoc)))
               (probe (inst (zoo6 k) .dupoc .dupoc))) :=
    fun k _ => quine_loeb_premise k
  obtain ⟨k₂, hk₂⟩ :=
    pblt_engine_id (fun k => probe (inst (zoo6 k) .dupoc .dupoc))
      (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  obtain ⟨n, hn⟩ := Pf_sound m _ hm
  exact probe_true_of_quine_play k n hn

/-! ## The Gödelian floor pair — the δ_L column's EBot cell

`inst .ebot .dupoc` is the tau image of base `outcome_DupocBot_vs_EBot = (D, C)`:
the instance REALLY COOPERATES (its exploit-probe of Dupoc fails, its
reciprocity-probe fires), yet its cooperation is UNPROVABLE at any budget ≤ k —
every certificate must cross the failed exploit-search and pay the `search_f`
floor (`no_provable_botSearcherElse_tail`). A true bit that reads 0. -/

/-- TRUE: `inst .ebot .dupoc` plays C (through the failed exploit-probe). -/
theorem interp_probe_inst_ebot_dupoc {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) :
    (probe (inst (zoo6 k) .ebot .dupoc)).interp := by
  have h1 : proofSearch k (probe (inst (zoo6 k) .dupoc .defect)) = false :=
    ps_searchProbe_constD k k
  have h2 : proofSearch k (probe (inst (zoo6 k) .dupoc .coop)) = true :=
    ps_searchProbe_constC hk hkk
  refine ⟨4, ?_⟩
  -- after `refine`, the goal is the PLAY of the `.bot`-framed instance; peel one
  -- compiler level, then the two guard bits close the run
  rw [inst_ebot_peel k .dupoc]
  simp [play, eval, probe_subst, h1, h2]

/-- UNPROVABLE: the bit is 0 at every budget up to k — TauDupoc's probe honestly
    fails. -/
theorem ps_probe_inst_ebot_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (zoo6 k) .ebot .dupoc)) = false := by
  cases h : proofSearch K (probe (inst (zoo6 k) .ebot .dupoc)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k
        (probe (inst (zoo6 k) .dupoc .defect)) .D .C
        (.search k (probe (inst (zoo6 k) .dupoc .coop)) (.const .C) (.const .D))
        (by decide) (Nat.le_refl k)
        (.bot (inst (zoo6 k) .ebot .dupoc))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

/-! ## The three consulted columns (the public bit API) -/

/-- δ_C column bits. Zero rows: Defect (refutable) and EBot (it EXPLOITS a
    cooperator). -/
def coopColBit : Tmpl → Bool
  | .defect => false
  | .ebot   => false
  | _       => true

theorem ps_probe_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .coop)) = coopColBit T
  | .coop   => ps_probe_constC hk
  | .defect => ps_probe_constD k
  | .tftSim => ps_simCopy_constC h6
  | .tftPf  => ps_searchProbe_constC hk hkk
  | .dupoc  => ps_searchProbe_constC hk hkk
  | .ebot   => ps_cascade_constC_false hk k

/-- δ_D column bits. Only the unconditional cooperator is exploitable. -/
def defectColBit : Tmpl → Bool
  | .coop => true
  | _     => false

theorem ps_probe_inst_defect {k : Nat} (hk : 2 ≤ k) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .defect)) = defectColBit T
  | .coop   => ps_probe_constC hk
  | .defect => ps_probe_constD k
  | .tftSim => ps_simCopy_constD k
  | .tftPf  => ps_searchProbe_constD k k
  | .dupoc  => ps_searchProbe_constD k k
  | .ebot   => ps_cascade_constD_false k k

/-- δ_L column bits. Zero rows: Defect, and EBot — THE FLOOR. The diagonal is the
    Löb quine, supplied as a hypothesis (it holds past a THRESHOLD, not at a fixed
    budget bound — `ps_probe_inst_quine`). -/
def dupocColBit : Tmpl → Bool
  | .defect => false
  | .ebot   => false
  | _       => true

theorem ps_probe_inst_dupoc {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true) :
    ∀ T, proofSearch k (probe (inst (zoo6 k) T .dupoc)) = dupocColBit T
  | .coop   => ps_probe_constC hk
  | .defect => ps_probe_constD k
  | .tftSim => (proofSearch_spec _ _).2 (pf_simCopy_searchProbeC hk hk7)
  | .tftPf  => (proofSearch_spec _ _).2 (pf_searchProbe_searchProbeC hk hkk hkk)
  | .dupoc  => hquine
  | .ebot   => ps_probe_inst_ebot_dupoc_false (le_refl k)

/-! ## The behavioral δ_C column — true plays, for `run`-mode consumers -/

/-- What T's instance seeing the cooperator TRULY plays (floor-blind). -/
def coopColPlay : Tmpl → Action
  | .defect => .D
  | .ebot   => .D
  | _       => .C

theorem inst_coop_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (zoo6 k) T .coop)) (.bot (inst (zoo6 k) T .coop))
              (inst (zoo6 k) T .coop) = some (coopColPlay T)
  | .coop   => ⟨1, rfl⟩
  | .defect => ⟨1, rfl⟩
  | .tftSim => entry_C_of_interp (Pf_sound _ _ (pf_simCopy_constC h6))
  | .tftPf  => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .dupoc  => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .ebot   => by
      have hb : proofSearch k (probe (.const .C)) = true := ps_probe_constC hk
      have hplay : eval 3
          (.bot (.search k (probe (.const .C)) (.const .D)
            (.search k (probe (.const .C)) (.const .C) (.const .D))))
          (.bot (.search k (probe (.const .C)) (.const .D)
            (.search k (probe (.const .C)) (.const .C) (.const .D))))
          (.search k (probe (.const .C)) (.const .D)
            (.search k (probe (.const .C)) (.const .C) (.const .D)))
          = some Action.D := by
        rw [eval, probe_subst, hb]; rfl
      exact ⟨3, hplay⟩

/-! ## The quine entry's play -/

/-- The diagonal entry of τ(Dupoc)'s vector: past the Löb threshold the fixpoint
    fires and the entry plays C. -/
theorem inst_quine_plays {k : Nat}
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true) :
    ∃ N, eval N (.bot (inst (zoo6 k) .dupoc .dupoc))
         (.bot (inst (zoo6 k) .dupoc .dupoc)) (inst (zoo6 k) .dupoc .dupoc)
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
