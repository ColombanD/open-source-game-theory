import PrisonersDilemma.Research.Spikes.transcript.T49TreeSubstrate
import PrisonersDilemma.Bots.DupocBot

/-! # T50 — THE FALSIFICATION EXPERIMENT (2026-07-08, ledger §6 top)

A REAL instance-Löb fact as a ProvT tree: DupocBot self-cooperation, whose guard
instance IS the cooperation fact (`tgt = ψg.subst me me = .plays me me C`). Built by
mirroring `BaseTheorems.bloeb_engine` constructor-for-constructor, Löb premise =
the searchBranch census. Three verdicts decide the pivot:
  (a) `certifyExcised` — expect FALSE (v1 excisor: apps only; instance middles remain);
  (b) `atomizeGo` — expect TRUE (the machine is the Löb-unroller);
  (c) gate-check of the produced ATOM — decides whether cites must be normalized
      recursively (predicted: yes — the cite carries the once-unrolled tree). -/


namespace PD.T50
open PD PD.T49

/-- `bloeb_engine`, mirrored into the Type layer verbatim. -/
def bloebT (φ : Formula) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ K : Nat)
    (hLoeb : ProvT pm (.impl (.box fb φ) φ))
    (H1 : pm + (Formula.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)).size ≤ c₁)
    (H2 : pm + (Formula.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)).size ≤ c₂)
    (H3 : c₁ ≤ n₁)
    (H4 : n₁ + (Formula.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))).size ≤ c₃)
    (H5 : n₁ + g + (Formula.impl (.box g (.diag g φ)) φ).size ≤ n₃)
    (H6 : (Formula.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
            (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))).size ≤ c₄)
    (H7 : c₄ + c₃ + (Formula.impl (.box g (.diag g φ))
            (.box n₃ (.impl (.box g (.diag g φ)) φ))).size ≤ c₅)
    (H8 : n₃ + n₄ + φ.size ≤ n₅)
    (H9 : (Formula.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₆)
    (H10 : g + (Formula.box g (.diag g φ)).size ≤ n₄)
    (H11 : (Formula.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))).size ≤ c₇)
    (H12 : c₅ + c₆ + (Formula.impl (.box g (.diag g φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₈)
    (H13 : c₈ + c₇ + (Formula.impl (.box g (.diag g φ)) (.box n₅ φ)).size ≤ c₉)
    (H14 : n₅ ≤ fb)
    (H15 : (Formula.impl (.box n₅ φ) (.box fb φ)).size ≤ c₁₀)
    (H16 : c₉ + c₁₀ + (Formula.impl (.box g (.diag g φ)) (.box fb φ)).size ≤ c₁₁)
    (H17 : c₁₁ + pm + (Formula.impl (.box g (.diag g φ)) φ).size ≤ c₁₂)
    (H18 : c₂ + c₁₂ + (Formula.diag g φ).size ≤ c₁₃)
    (H19 : c₁₃ ≤ g)
    (H20 : g + (Formula.box g (.diag g φ)).size ≤ c₁₄)
    (H21 : c₁₂ + c₁₄ + φ.size ≤ K) :
    ProvT K φ :=
  let legF : ProvT c₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)) :=
    .diagF pm fb g c₁ φ hLoeb H1
  let legB : ProvT c₂ (.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)) :=
    .diagB pm fb g c₂ φ hLoeb H2
  let hnec : ProvT c₃ (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))) :=
    .boxIntro n₁ c₃ _ (legF.mono H3) H4
  let hK1 : ProvT c₄ (.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
      (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))) :=
    .axKf n₁ g n₃ c₄ (.diag g φ) (.impl (.box g (.diag g φ)) φ) H5 H6
  let h2 : ProvT c₅ (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ))) :=
    .app c₅ c₄ c₃ _ _ hK1 hnec H7
  let hK2 : ProvT c₆ (.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    .axKf n₃ n₄ n₅ c₆ (.box g (.diag g φ)) φ H8 H9
  let hfour : ProvT c₇ (.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))) :=
    .box4 g n₄ c₇ (.diag g φ) H10 H11
  let h4 : ProvT c₈ (.impl (.box g (.diag g φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    .implTrans _ _ _ c₅ c₆ h2 hK2 H12
  let h6 : ProvT c₉ (.impl (.box g (.diag g φ)) (.box n₅ φ)) :=
    .impS2 _ _ _ c₈ c₇ c₉ h4 hfour H13
  let hmono : ProvT c₁₀ (.impl (.box n₅ φ) (.box fb φ)) :=
    .boxMono n₅ fb c₁₀ φ H14 H15
  let h6' : ProvT c₁₁ (.impl (.box g (.diag g φ)) (.box fb φ)) :=
    .implTrans _ _ _ c₉ c₁₀ h6 hmono H16
  let hE : ProvT c₁₂ (.impl (.box g (.diag g φ)) φ) :=
    .implTrans _ _ _ c₁₁ pm h6' hLoeb H17
  let hF : ProvT c₁₃ (.diag g φ) := .app c₁₃ c₂ c₁₂ _ _ legB hE H18
  let hG : ProvT c₁₄ (.box g (.diag g φ)) := .boxIntro g c₁₄ _ (hF.mono H19) H20
  .app K c₁₂ c₁₄ _ _ hE hG H21

/-! ## The Dupoc instance. -/

def kD : Nat := 2097152
def meD : Prog := Bots.DupocBot kD
def tgtD : Formula := .plays meD meD Action.C

def dLeg : Derivation (.impl (.box kD tgtD) tgtD) :=
  .searchBranch kD (.plays .opp .self Action.C) Action.C Action.D meD meD rfl

#eval dLeg.size          -- pm
#eval tgtD.size          -- |φ|
#eval Nat.log2 kD

def W : Nat := 224   -- dLeg.size + tgtD.size + log2 kD + 8 = 138+57+21+8

def hLoebT : ProvT 138 (.impl (.box kD tgtD) tgtD) := .struct dLeg (Nat.le_refl _)

/-- THE TREE: DupocBot self-cooperation, the real instance-Löb fact. -/
def treeD : ProvT (4096 * W) tgtD :=
  bloebT tgtD 138 kD (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    hLoebT
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- (a′) the pivot's claim, directly: the RAW tree fails the modest gate
#eval s!"(a′) raw tree passes gate: {treeD.gateOKb (T44.cutOKb kD)}"
-- (a) v1 excision cannot repair it (apps only; middles/diag remain)
#eval s!"(a) certifyExcised: {(certifyExcised 4 500 kD treeD).isSome}"
-- (b) but the machine IS the Löb-unroller: the fact atomizes
#eval s!"(b) atomizes: {(atomizeGo 2000 treeD).isSome}"
-- (c) the produced atom's gate status (predicted false: the cite carries the
--     once-unrolled tree; cite-normalization is the missing pipeline step)
#eval s!"(c) atom passes gate: {
  match atomizeGo 2000 treeD with
  | some ⟨_, cert⟩ => (ProvT.atom cert).gateOKb (T44.cutOKb kD)
  | none => false}"

/-! ## THE REPAIR — the instance gate (pool-instances of modest formulas).

`argOK` relaxed: plays/sim/eq argument positions may also be POOL MEMBERS. -/

def argOKP (P : List Prog) (p : Prog) : Bool :=
  p == .self || p == .opp || T43.closedP p || P.contains p

mutual
  def instModestP (P : List Prog) : Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => instModestP P p
    | .sim p q => argOKP P p && argOKP P q && instModestP P p && instModestP P q
    | .ite b _ p q => instModestP P b && instModestP P p && instModestP P q
    | .search _ φ p q => T43.modestF φ && instModestP P p && instModestP P q

  def instModestF (P : List Prog) : Formula → Bool
    | .plays p q _ => argOKP P p && argOKP P q && instModestP P p && instModestP P q
    | .impl φ ψ => instModestF P φ && instModestF P ψ
    | .neg φ => instModestF P φ
    | .box _ φ => instModestF P φ
    | .eq p q => argOKP P p && instModestP P p && instModestP P q
    | .diag _ φ => instModestF P φ
end

def instOKb (P : List Prog) (N : Nat) (B : Formula) : Bool :=
  decide (T42.maxLitF B ≤ N) && instModestF P B

-- (d) THE REPAIRED VERDICT: does the RAW bloeb tree pass the instance gate?
#eval s!"(d) raw tree passes INSTANCE gate: {treeD.gateOKb (instOKb [meD] kD)}"

/-! ## 2. The instance-gate bricks (plan of record, item i).

Structural fact the bricks encode: the RULES only ever substitute RAW stored guards
(instances are never re-substituted), so the only subst-closure needed is
raw-modest × pool players → instance-modest. `P` is intended as T43's `players`
closure (finite; `step_sim` gives frame-closure). -/

/-- The Prop instance gate. -/
def instGate (P : List Prog) (N : Nat) : Formula → Prop :=
  fun B => T42.maxLitF B ≤ N ∧ instModestF P B = true

theorem instOKb_iff {P : List Prog} {N : Nat} {B : Formula} :
    instOKb P N B = true ↔ instGate P N B := by
  simp [instOKb, instGate, Bool.and_eq_true]

/-- `argOK` positions are `argOKP` positions. -/
theorem argOK_argOKP {P : List Prog} {p : Prog} (h : T43.argOK p = true) :
    argOKP P p = true := by
  simp only [T43.argOK, Bool.or_eq_true] at h
  simp only [argOKP, Bool.or_eq_true]
  tauto

mutual
  /-- Modesty is monotone into instance-modesty. -/
  theorem modestP_instModestP (P : List Prog) :
      ∀ (p : Prog), T43.modestP p = true → instModestP P p = true
    | .const _, _ => rfl
    | .self, _ => rfl
    | .opp, _ => rfl
    | .bot p, h => modestP_instModestP P p h
    | .sim p q, h => by
        simp only [T43.modestP, Bool.and_eq_true] at h
        simp only [instModestP, Bool.and_eq_true]
        exact ⟨⟨⟨argOK_argOKP h.1.1.1, argOK_argOKP h.1.1.2⟩,
          modestP_instModestP P p h.1.2⟩, modestP_instModestP P q h.2⟩
    | .ite b _ p q, h => by
        simp only [T43.modestP, Bool.and_eq_true] at h
        simp only [instModestP, Bool.and_eq_true]
        exact ⟨⟨modestP_instModestP P b h.1.1, modestP_instModestP P p h.1.2⟩,
          modestP_instModestP P q h.2⟩
    | .search _ φ p q, h => by
        simp only [T43.modestP, Bool.and_eq_true] at h
        simp only [instModestP, Bool.and_eq_true]
        exact ⟨⟨h.1.1, modestP_instModestP P p h.1.2⟩,
          modestP_instModestP P q h.2⟩

  theorem modestF_instModestF (P : List Prog) :
      ∀ (φ : Formula), T43.modestF φ = true → instModestF P φ = true
    | .plays p q _, h => by
        simp only [T43.modestF, Bool.and_eq_true] at h
        simp only [instModestF, Bool.and_eq_true]
        exact ⟨⟨⟨argOK_argOKP h.1.1.1, argOK_argOKP h.1.1.2⟩,
          modestP_instModestP P p h.1.2⟩, modestP_instModestP P q h.2⟩
    | .impl φ ψ, h => by
        simp only [T43.modestF, Bool.and_eq_true] at h
        simp only [instModestF, Bool.and_eq_true]
        exact ⟨modestF_instModestF P φ h.1, modestF_instModestF P ψ h.2⟩
    | .neg φ, h => modestF_instModestF P φ h
    | .box _ φ, h => modestF_instModestF P φ h
    | .eq p q, h => by
        simp only [T43.modestF, Bool.and_eq_true] at h
        simp only [instModestF, Bool.and_eq_true]
        exact ⟨⟨argOK_argOKP h.1.1, modestP_instModestP P p h.1.2⟩,
          modestP_instModestP P q h.2⟩
    | .diag _ φ, h => modestF_instModestF P φ h
end

/-- **The arg-resolution brick**: an `argOK` argument substituted by `argOKP`,
    instance-modest players is instance-modest — no program recursion needed
    (argOK args resolve atomically: to a player or frozen). -/
theorem arg_subst_inst (P : List Prog) (u v : Prog)
    (hu : argOKP P u = true) (hv : argOKP P v = true)
    (hum : instModestP P u = true) (hvm : instModestP P v = true)
    {p : Prog} (ha : T43.argOK p = true) (hm : T43.modestP p = true) :
    argOKP P (p.subst u v) = true ∧ instModestP P (p.subst u v) = true := by
  rcases T43.argOK_subst ha u v with h' | h' | ⟨h', _⟩
  · rw [h']; exact ⟨hu, hum⟩
  · rw [h']; exact ⟨hv, hvm⟩
  · rw [h']; exact ⟨argOK_argOKP ha, modestP_instModestP P p hm⟩

/-- **THE INSTANCE-SUBST BRICK (formula half)**: a raw-modest formula substituted by
    instance-modest players is instance-modest. Recursion is on the FORMULA only —
    raw-modest formulas hold programs exclusively at argOK-atomic positions. -/
theorem modestF_subst_inst (P : List Prog) (u v : Prog)
    (hu : argOKP P u = true) (hv : argOKP P v = true)
    (hum : instModestP P u = true) (hvm : instModestP P v = true) :
    ∀ (φ : Formula), T43.modestF φ = true → instModestF P (φ.subst u v) = true
  | .plays p q _, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, instModestF, Bool.and_eq_true]
      have hp := arg_subst_inst P u v hu hv hum hvm h.1.1.1 h.1.2
      have hq := arg_subst_inst P u v hu hv hum hvm h.1.1.2 h.2
      exact ⟨⟨⟨hp.1, hq.1⟩, hp.2⟩, hq.2⟩
  | .impl φ ψ, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, instModestF, Bool.and_eq_true]
      exact ⟨modestF_subst_inst P u v hu hv hum hvm φ h.1,
        modestF_subst_inst P u v hu hv hum hvm ψ h.2⟩
  | .neg φ, h => modestF_subst_inst P u v hu hv hum hvm φ h
  | .box _ φ, h => modestF_subst_inst P u v hu hv hum hvm φ h
  | .eq p q, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, instModestF, Bool.and_eq_true]
      have hp := arg_subst_inst P u v hu hv hum hvm h.1.1 h.1.2
      exact ⟨⟨hp.1, hp.2⟩, modestP_instModestP P q h.2⟩
  | .diag _ φ, h => modestF_instModestF P _ h

/-! ## 3. The census tie at the instance gate.

The pool hypothesis is exactly what the sim cases need: member instance-modesty and
closure of member arg-substitution by admissible frames (for the canonical
`P := T43.players r₁ r₂` both are theorems — `certU_modest`, `step_sim`). -/

structure PoolOK (P : List Prog) : Prop where
  modest : ∀ p, p ∈ P → instModestP P p = true
  argStep : ∀ p me opnt, P.contains p = true →
    argOKP P me = true → instModestP P me = true →
    argOKP P opnt = true → instModestP P opnt = true →
    argOKP P (p.subst me opnt) = true ∧ instModestP P (p.subst me opnt) = true

/-- Uniform arg resolution under frames: the four `argOKP` cases in one lemma. -/
theorem argOKP_subst_inst {P : List Prog} (hP : PoolOK P) {p me opnt : Prog}
    (hp : argOKP P p = true) (hpm : instModestP P p = true)
    (hme : argOKP P me = true) (hmem : instModestP P me = true)
    (hop : argOKP P opnt = true) (hopm : instModestP P opnt = true) :
    argOKP P (p.subst me opnt) = true ∧ instModestP P (p.subst me opnt) = true := by
  simp only [argOKP, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with ((rfl | rfl) | hcl) | hmem'
  · exact ⟨hme, hmem⟩
  · exact ⟨hop, hopm⟩
  · rw [T43.substP_id me opnt p hcl]
    exact ⟨by simp only [argOKP, hcl, Bool.or_true, Bool.true_or], hpm⟩
  · exact hP.argStep p me opnt hmem' hme hmem hop hopm

/-- **The census tie, instance-gated**: every census antecedent is instance-modest
    whenever its consequent is — over any `PoolOK` pool. -/
theorem DAnt_instModest {P : List Prog} (hP : PoolOK P) :
    ∀ {B C : Formula}, PD.T48.DAnt B C →
    instModestF P C = true → instModestF P B = true := by
  intro B C h
  induction h with
  | searchBr hme =>
      subst hme
      intro hC
      simp only [instModestF, Bool.and_eq_true] at hC
      have hm := hC.1.2
      simp only [instModestP, Bool.and_eq_true] at hm
      simp only [instModestF]
      exact modestF_subst_inst P _ _ hC.1.1.1 hC.1.1.2 hC.1.2 hC.2 _ hm.1.1
  | botSearchSt hme =>
      subst hme
      intro hC
      simp only [instModestF, Bool.and_eq_true] at hC
      have hm := hC.1.2
      simp only [instModestP, Bool.and_eq_true] at hm
      simp only [instModestF]
      exact modestF_subst_inst P _ _ hC.1.1.1 hC.1.1.2 hC.1.2 hC.2 _ hm.1.1
  | simSt hme =>
      subst hme
      intro hC
      simp only [instModestF, Bool.and_eq_true] at hC
      have hm := hC.1.2
      simp only [instModestP, Bool.and_eq_true] at hm
      have hp := argOKP_subst_inst hP hm.1.1.1 hm.1.2
        hC.1.1.1 hC.1.2 hC.1.1.2 hC.2
      have hq := argOKP_subst_inst hP hm.1.1.2 hm.2
        hC.1.1.1 hC.1.2 hC.1.1.2 hC.2
      simp only [instModestF, Bool.and_eq_true]
      exact ⟨⟨⟨hp.1, hq.1⟩, hp.2⟩, hq.2⟩
  | botSimSt hme =>
      subst hme
      intro hC
      simp only [instModestF, Bool.and_eq_true] at hC
      have hm := hC.1.2
      simp only [instModestP, Bool.and_eq_true] at hm
      have hp := argOKP_subst_inst hP hm.1.1.1 hm.1.2
        hC.1.1.1 hC.1.2 hC.1.1.2 hC.2
      have hq := argOKP_subst_inst hP hm.1.1.2 hm.2
        hC.1.1.1 hC.1.2 hC.1.1.2 hC.2
      simp only [instModestF, Bool.and_eq_true]
      exact ⟨⟨⟨hp.1, hq.1⟩, hp.2⟩, hq.2⟩
  | iteBr₁ hme =>
      subst hme
      intro hC
      simp only [instModestF, Bool.and_eq_true] at hC
      have hm := hC.2.1.2
      simp only [instModestP, Bool.and_eq_true] at hm
      simp only [instModestF, Bool.and_eq_true]
      exact ⟨⟨⟨hC.2.1.1.2, hm.1.1.1.1.2⟩, hC.2.2⟩, hm.1.1.2⟩
  | iteBr₂ hme =>
      subst hme
      intro hC
      simp only [instModestF, Bool.and_eq_true] at hC
      have hm := hC.1.2
      simp only [instModestP, Bool.and_eq_true] at hm
      simp only [instModestF]
      exact modestF_subst_inst P _ _ hC.1.1.1 hC.1.1.2 hC.1.2 hC.2 _ hm.1.2.1.1
  | trans h1 h2 ih1 ih2 => intro hC; exact ih1 (ih2 hC)

/-- The combined instance-gate transfer for Derivation cuts (literal half is
    gate-agnostic: T48's `DAnt_lit`). -/
theorem DAnt_instGate {P : List Prog} {N : Nat} (hP : PoolOK P) {B C : Formula}
    (h : PD.T48.DAnt B C) (hC : instGate P N C) : instGate P N B :=
  ⟨le_trans (PD.T48.DAnt_lit h) hC.1, DAnt_instModest hP h hC.2⟩

/-- The instance gate distributes over implication. -/
theorem instGate_impl_iff {P : List Prog} {N : Nat} {φ ψ : Formula} :
    instGate P N (.impl φ ψ) ↔ instGate P N φ ∧ instGate P N ψ := by
  simp only [instGate, T42.maxLitF, instModestF, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, h2⟩, ⟨by omega, h3⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h2, h4⟩

/-- **The struct arm at the instance gate**: a Derivation with an instance-gated
    conclusion passes at every `derivGateOK` site. -/
theorem derivGateOK_of_conclusion_inst {P : List Prog} {N : Nat} (hP : PoolOK P) :
    ∀ {ξ : Formula} (d : Derivation ξ), instGate P N ξ →
    derivGateOK (instGate P N) d
  | _, .modusPonens φ ψ d1 d2, hξ => by
      have hcut : instGate P N φ :=
        DAnt_instGate hP (PD.T48.derivation_impl_ant d1) hξ
      exact ⟨hcut,
        derivGateOK_of_conclusion_inst hP d1 (instGate_impl_iff.mpr ⟨hcut, hξ⟩),
        derivGateOK_of_conclusion_inst hP d2 hcut⟩
  | _, .hypSyll φ ψ χ d1 d2, hξ => by
      have hχ : instGate P N χ := (instGate_impl_iff.mp hξ).2
      have hφ : instGate P N φ := (instGate_impl_iff.mp hξ).1
      have hmid : instGate P N ψ :=
        DAnt_instGate hP (PD.T48.derivation_impl_ant d2) hχ
      exact ⟨hmid,
        derivGateOK_of_conclusion_inst hP d1 (instGate_impl_iff.mpr ⟨hφ, hmid⟩),
        derivGateOK_of_conclusion_inst hP d2 (instGate_impl_iff.mpr ⟨hmid, hχ⟩)⟩
  | _, .searchBranch _ _ _ _ _ _ _, _ => trivial
  | _, .botSearchStep _ _ _ _ _ _ _, _ => trivial
  | _, .simStep _ _ _ _ _ _, _ => trivial
  | _, .botSimStep _ _ _ _ _ _, _ => trivial
  | _, .iteBranchSearch_t _ _ _ _ _ _ _ _ _ _, _ => trivial
  | _, .eqRefl _, _ => trivial
  | _, .eqNeg _ _ _, _ => trivial

/-- axK's premise gate is fully conclusion-tied — instance-gate port. -/
theorem instGate_axK_tied {P : List Prog} {N a b c : Nat} {φ α : Formula}
    (h : instGate P N (.impl (.box b φ) (.box c α)))
    (hg1 : a + b + α.size ≤ c) :
    instGate P N (.box a (.impl φ α)) := by
  obtain ⟨hlit, hmod⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [T42.maxLitF] at hlit ⊢
    omega
  · simp only [instModestF, Bool.and_eq_true] at hmod ⊢
    exact hmod

/-- diagF/diagB's gate is conclusion-tied modulo the premise subscript —
    instance-gate port. -/
theorem instGate_diag_tied {P : List Prog} {N fb g : Nat} {tgt : Formula}
    (h : instGate P N (.impl (.box g (.diag g tgt)) tgt))
    (hfb : fb ≤ N) :
    instGate P N (.impl (.box fb tgt) tgt) := by
  obtain ⟨hlit, hmod⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [T42.maxLitF] at hlit ⊢
    omega
  · simp only [instModestF, Bool.and_eq_true] at hmod ⊢
    exact ⟨hmod.2, hmod.2⟩
