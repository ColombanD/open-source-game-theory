import PrisonersDilemma.Research.Spikes.transcript.T49TreeSubstrate
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Decidability.T46LogicSpace

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
  p == .self || p == .opp || (T43.closedP p && T43.modestP p) || P.contains p

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
theorem argOK_argOKP {P : List Prog} {p : Prog} (h : T43.argOK p = true)
    (hm : T43.modestP p = true) : argOKP P p = true := by
  simp only [T43.argOK, Bool.or_eq_true] at h
  simp only [argOKP, Bool.or_eq_true, Bool.and_eq_true]
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr ⟨h, hm⟩)

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
        exact ⟨⟨⟨argOK_argOKP h.1.1.1 h.1.2, argOK_argOKP h.1.1.2 h.2⟩,
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
        exact ⟨⟨⟨argOK_argOKP h.1.1.1 h.1.2, argOK_argOKP h.1.1.2 h.2⟩,
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
        exact ⟨⟨argOK_argOKP h.1.1 h.1.2, modestP_instModestP P p h.1.2⟩,
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
  · rw [h']; exact ⟨argOK_argOKP ha hm, modestP_instModestP P p hm⟩

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

/-! ## 3. Live instance-gate bricks (the PoolOK-conditioned tie was pruned
2026-07-09 — superseded by the pool-free §3b; see git history). -/

theorem instGate_impl_iff {P : List Prog} {N : Nat} {φ ψ : Formula} :
    instGate P N (.impl φ ψ) ↔ instGate P N φ ∧ instGate P N ψ := by
  simp only [instGate, T42.maxLitF, instModestF, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, h2⟩, ⟨by omega, h3⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h2, h4⟩

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

/-! ## 3b. Raw argument frames — the PoolOK-free census tie (ledger: v3 blocker fix).

`rawArgsF`: the formula's program arguments are RAW-modest (`argOK` NOT required —
compound raw frames allowed). Under this side condition the census tie needs no pool
facts at all: raw frames' sim-args are argOK-ATOMIC, so substitution resolves by the
three-case lemma and rawness self-propagates. -/

def rawArgsF : Formula → Bool
  | .plays p q _ => T43.modestP p && T43.modestP q
  | .impl φ ψ => rawArgsF φ && rawArgsF ψ
  | .neg φ => rawArgsF φ
  | .box _ φ => rawArgsF φ
  | .eq p q => T43.modestP p && T43.modestP q
  | .diag _ φ => rawArgsF φ

/-- Raw-modesty of formulas is weaker than modesty. -/
theorem modestF_rawArgsF : ∀ (φ : Formula), T43.modestF φ = true → rawArgsF φ = true
  | .plays p q _, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [rawArgsF, Bool.and_eq_true]
      exact ⟨h.1.2, h.2⟩
  | .impl φ ψ, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [rawArgsF, Bool.and_eq_true]
      exact ⟨modestF_rawArgsF φ h.1, modestF_rawArgsF ψ h.2⟩
  | .neg φ, h => modestF_rawArgsF φ h
  | .box _ φ, h => modestF_rawArgsF φ h
  | .eq p q, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [rawArgsF, Bool.and_eq_true]
      exact ⟨h.1.2, h.2⟩
  | .diag _ φ, h => modestF_rawArgsF φ h

/-- Raw-modest formulas substituted by raw frames have raw args (argOK-atomic
    resolution: to a frame or a frozen raw subprogram). -/
theorem rawArgsF_subst (me o : Prog) (hme : T43.modestP me = true)
    (ho : T43.modestP o = true) :
    ∀ (φ : Formula), T43.modestF φ = true → rawArgsF (φ.subst me o) = true
  | .plays p q _, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, rawArgsF, Bool.and_eq_true]
      constructor
      · rcases T43.argOK_subst h.1.1.1 me o with h' | h' | ⟨h', _⟩
        · rw [h']; exact hme
        · rw [h']; exact ho
        · rw [h']; exact h.1.2
      · rcases T43.argOK_subst h.1.1.2 me o with h' | h' | ⟨h', _⟩
        · rw [h']; exact hme
        · rw [h']; exact ho
        · rw [h']; exact h.2
  | .impl φ ψ, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, rawArgsF, Bool.and_eq_true]
      exact ⟨rawArgsF_subst me o hme ho φ h.1, rawArgsF_subst me o hme ho ψ h.2⟩
  | .neg φ, h => rawArgsF_subst me o hme ho φ h
  | .box _ φ, h => rawArgsF_subst me o hme ho φ h
  | .eq p q, h => by
      simp only [T43.modestF, Bool.and_eq_true] at h
      simp only [Formula.subst, rawArgsF, Bool.and_eq_true]
      constructor
      · rcases T43.argOK_subst h.1.1 me o with h' | h' | ⟨h', _⟩
        · rw [h']; exact hme
        · rw [h']; exact ho
        · rw [h']; exact h.1.2
      · exact h.2
  | .diag _ φ, h => modestF_rawArgsF _ h

/-- The modest+raw halves of the pool-free tie (lit is gate-agnostic, added by
    the wrapper below). -/
theorem DAnt_rawModest {P : List Prog} :
    ∀ {B C : Formula}, PD.T48.DAnt B C →
    instModestF P C = true → rawArgsF C = true →
    instModestF P B = true ∧ rawArgsF B = true := by
  intro B C h
  induction h with
  | searchBr hme =>
      subst hme
      intro hmod hraw
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hm := hraw.1
      simp only [T43.modestP, Bool.and_eq_true] at hm
      refine ⟨?_, ?_⟩
      · simp only [instModestF]
        exact modestF_subst_inst P _ _ hmod.1.1.1 hmod.1.1.2
          (modestP_instModestP P _ hraw.1) (modestP_instModestP P _ hraw.2)
          _ hm.1.1
      · simp only [rawArgsF]
        exact rawArgsF_subst _ _ hraw.1 hraw.2 _ hm.1.1
  | botSearchSt hme =>
      subst hme
      intro hmod hraw
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hm := hraw.1
      simp only [T43.modestP, Bool.and_eq_true] at hm
      refine ⟨?_, ?_⟩
      · simp only [instModestF]
        exact modestF_subst_inst P _ _ hmod.1.1.1 hmod.1.1.2
          (modestP_instModestP P _ hraw.1) (modestP_instModestP P _ hraw.2)
          _ hm.1.1
      · simp only [rawArgsF]
        exact rawArgsF_subst _ _ hraw.1 hraw.2 _ hm.1.1
  | simSt hme =>
      subst hme
      intro hmod hraw
      rename_i p' q' opnt' a'
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hm := hraw.1
      simp only [T43.modestP, Bool.and_eq_true] at hm
      have hres : ∀ (r : Prog), T43.argOK r = true → T43.modestP r = true →
          (argOKP P (r.subst (.sim p' q') opnt') = true ∧
            instModestP P (r.subst (.sim p' q') opnt') = true) ∧
          T43.modestP (r.subst (.sim p' q') opnt') = true := by
        intro r ha hp
        rcases T43.argOK_subst ha _ _ with h' | h' | ⟨h', hcl⟩
        · rw [h']
          exact ⟨⟨hmod.1.1.1, modestP_instModestP P _ hraw.1⟩, hraw.1⟩
        · rw [h']
          exact ⟨⟨hmod.1.1.2, modestP_instModestP P _ hraw.2⟩, hraw.2⟩
        · rw [h']
          exact ⟨⟨by simp only [argOKP, hcl, hp, Bool.and_self, Bool.or_true, Bool.true_or],
            modestP_instModestP P _ hp⟩, hp⟩
      have hp := hres _ hm.1.1.1 hm.1.2
      have hq := hres _ hm.1.1.2 hm.2
      refine ⟨?_, ?_⟩
      · simp only [instModestF, Bool.and_eq_true]
        exact ⟨⟨⟨hp.1.1, hq.1.1⟩, hp.1.2⟩, hq.1.2⟩
      · simp only [rawArgsF, Bool.and_eq_true]
        exact ⟨hp.2, hq.2⟩
  | botSimSt hme =>
      subst hme
      intro hmod hraw
      rename_i p' q' opnt' a'
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hm := hraw.1
      simp only [T43.modestP, Bool.and_eq_true] at hm
      have hres : ∀ (r : Prog), T43.argOK r = true → T43.modestP r = true →
          (argOKP P (r.subst (.bot (.sim p' q')) opnt') = true ∧
            instModestP P (r.subst (.bot (.sim p' q')) opnt') = true) ∧
          T43.modestP (r.subst (.bot (.sim p' q')) opnt') = true := by
        intro r ha hp
        rcases T43.argOK_subst ha _ _ with h' | h' | ⟨h', hcl⟩
        · rw [h']
          exact ⟨⟨hmod.1.1.1, modestP_instModestP P _ hraw.1⟩, hraw.1⟩
        · rw [h']
          exact ⟨⟨hmod.1.1.2, modestP_instModestP P _ hraw.2⟩, hraw.2⟩
        · rw [h']
          exact ⟨⟨by simp only [argOKP, hcl, hp, Bool.and_self, Bool.or_true, Bool.true_or],
            modestP_instModestP P _ hp⟩, hp⟩
      have hp := hres _ hm.1.1.1 hm.1.2
      have hq := hres _ hm.1.1.2 hm.2
      refine ⟨?_, ?_⟩
      · simp only [instModestF, Bool.and_eq_true]
        exact ⟨⟨⟨hp.1.1, hq.1.1⟩, hp.1.2⟩, hq.1.2⟩
      · simp only [rawArgsF, Bool.and_eq_true]
        exact ⟨hp.2, hq.2⟩
  | iteBr₁ hme =>
      subst hme
      intro hmod hraw
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hm := hraw.2.1
      simp only [T43.modestP, Bool.and_eq_true] at hm
      have hmi := hmod.2.1.2
      simp only [instModestP, Bool.and_eq_true] at hmi
      refine ⟨?_, ?_⟩
      · simp only [instModestF, Bool.and_eq_true]
        exact ⟨⟨⟨hmod.2.1.1.2, hmi.1.1.1.1.2⟩, hmod.2.2⟩, hmi.1.1.2⟩
      · simp only [rawArgsF, Bool.and_eq_true]
        exact ⟨hraw.2.2, hm.1.1.2⟩
  | iteBr₂ hme =>
      subst hme
      intro hmod hraw
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hm := hraw.1
      simp only [T43.modestP, Bool.and_eq_true] at hm
      refine ⟨?_, ?_⟩
      · simp only [instModestF]
        exact modestF_subst_inst P _ _ hmod.1.1.1 hmod.1.1.2
          (modestP_instModestP P _ hraw.1) (modestP_instModestP P _ hraw.2)
          _ hm.1.2.1.1
      · simp only [rawArgsF]
        exact rawArgsF_subst _ _ hraw.1 hraw.2 _ hm.1.2.1.1
  | trans h1 h2 ih1 ih2 =>
      intro hmod hraw
      have := ih2 hmod hraw
      exact ih1 this.1 this.2

/-- **The census tie, pool-free**: under raw args, every census antecedent is
    instance-gated AND raw-arged whenever its consequent is. -/
theorem DAnt_rawGate {P : List Prog} {N : Nat} {B C : Formula}
    (h : PD.T48.DAnt B C) (hC : instGate P N C) (hraw : rawArgsF C = true) :
    instGate P N B ∧ rawArgsF B = true :=
  have hm := DAnt_rawModest h hC.2 hraw
  ⟨⟨le_trans (PD.T48.DAnt_lit h) hC.1, hm.1⟩, hm.2⟩

/-- **The struct arm, pool-free**: instance-gated + raw-arged conclusions pass at
    every `derivGateOK` site. -/
theorem derivGateOK_of_conclusion_raw {P : List Prog} {N : Nat} :
    ∀ {ξ : Formula} (d : Derivation ξ), instGate P N ξ → rawArgsF ξ = true →
    derivGateOK (instGate P N) d
  | _, .modusPonens φ ψ d1 d2, hξ, hraw => by
      have hcut := DAnt_rawGate (PD.T48.derivation_impl_ant d1) hξ hraw
      exact ⟨hcut.1,
        derivGateOK_of_conclusion_raw d1 (instGate_impl_iff.mpr ⟨hcut.1, hξ⟩)
          (by simp only [rawArgsF, Bool.and_eq_true]; exact ⟨hcut.2, hraw⟩),
        derivGateOK_of_conclusion_raw d2 hcut.1 hcut.2⟩
  | _, .hypSyll φ ψ χ d1 d2, hξ, hraw => by
      have hφ := (instGate_impl_iff.mp hξ).1
      have hχ := (instGate_impl_iff.mp hξ).2
      simp only [rawArgsF, Bool.and_eq_true] at hraw
      have hmid := DAnt_rawGate (PD.T48.derivation_impl_ant d2) hχ hraw.2
      exact ⟨hmid.1,
        derivGateOK_of_conclusion_raw d1 (instGate_impl_iff.mpr ⟨hφ, hmid.1⟩)
          (by simp only [rawArgsF, Bool.and_eq_true]; exact ⟨hraw.1, hmid.2⟩),
        derivGateOK_of_conclusion_raw d2 (instGate_impl_iff.mpr ⟨hmid.1, hχ⟩)
          (by simp only [rawArgsF, Bool.and_eq_true]; exact ⟨hmid.2, hraw.2⟩)⟩
  | _, .searchBranch _ _ _ _ _ _ _, _, _ => trivial
  | _, .botSearchStep _ _ _ _ _ _ _, _, _ => trivial
  | _, .simStep _ _ _ _ _ _, _, _ => trivial
  | _, .botSimStep _ _ _ _ _ _, _, _ => trivial
  | _, .iteBranchSearch_t _ _ _ _ _ _ _ _ _ _, _, _ => trivial
  | _, .eqRefl _, _, _ => trivial
  | _, .eqNeg _ _ _, _, _ => trivial

/-- Raw frames of a plays walk (read off the type indices). -/
def _root_.PD.T49.PlaysT.rawFrames {me o b : Prog} {a : Action} {n : Nat}
    (_ : PlaysT me o b a n) : Prop :=
  T43.modestP me = true ∧ T43.modestP o = true

mutual
  /-- Hereditary rawness: every atom node's frames and every struct node's
      conclusion args are RAW-modest (true of eval-derived certificates; the
      transport's 4th certificate). -/
  def _root_.PD.T49.PlaysT.rawAtoms : {me o b : Prog} → {a : Action} → {n : Nat} →
      PlaysT me o b a n → Prop
    | _, _, _, _, _, .const => True
    | _, _, _, _, _, .self t => t.rawAtoms
    | _, _, _, _, _, .opp t => t.rawAtoms
    | _, _, _, _, _, .bot t => t.rawAtoms
    | _, _, _, _, _, .sim t => t.rawAtoms
    | _, _, _, _, _, .ite_t tb _ tp => tb.rawAtoms ∧ tp.rawAtoms
    | _, _, _, _, _, .ite_f tb _ tq => tb.rawAtoms ∧ tq.rawAtoms
    | _, _, _, _, _, .search_t tg tp => tg.rawAtoms ∧ tp.rawAtoms
    | _, _, _, _, _, .search_f tr tq => tr.rawAtoms ∧ tq.rawAtoms

  def _root_.PD.T49.AtomT.rawAtoms : {k : Nat} → {φ : Formula} → AtomT k φ → Prop
    | _, _, .mk pl _ => pl.rawFrames ∧ pl.rawAtoms

  def _root_.PD.T49.ProvT.rawAtoms : {k : Nat} → {φ : Formula} → ProvT k φ → Prop
    | _, ξ', .struct _ _ => rawArgsF ξ' = true
    | _, _, .atom t => t.rawAtoms
    | _, _, .weakenImpl _ _ _ t _ => t.rawAtoms
    | _, _, .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ t _ _ => t.rawAtoms
    | _, _, .implTrans _ _ _ _ _ t1 t2 _ => t1.rawAtoms ∧ t2.rawAtoms
    | _, _, .atomBoxImpl _ _ _ _ t _ => t.rawAtoms
    | _, _, .boxIntro _ _ _ t _ => t.rawAtoms
    | _, _, .app _ _ _ _ _ t1 t2 _ => t1.rawAtoms ∧ t2.rawAtoms
    | _, _, .axK _ _ _ _ _ _ _ t _ _ => t.rawAtoms
    | _, _, .box4 _ _ _ _ _ _ => True
    | _, _, .diagF _ _ _ _ _ t _ => t.rawAtoms
    | _, _, .diagB _ _ _ _ _ t _ => t.rawAtoms
    | _, _, .axKf _ _ _ _ _ _ _ _ => True
    | _, _, .impS2 _ _ _ _ _ _ t1 t2 _ => t1.rawAtoms ∧ t2.rawAtoms
    | _, _, .boxMono _ _ _ _ _ _ => True
    | _, _, .atomNeg _ _ _ _ _ t _ _ => t.rawAtoms
end

/-! ## 4. THE TRANSPORT — full `gateOK (instGate P N)` from cut-sites + cite caps.

The §28 tie-down, live at the repaired gate: conclusions ARE instance-gated now.
Hypotheses: the node's conclusion gate, `cutsOK` (app/implTrans/impS2 — what
excision guarantees), `citesLE M` (cite budgets), `m ≤ M`, `2^M ≤ N` (for the
diag subscripts), and `PoolOK P`. The plays walk carries the frame triple. -/

mutual
theorem PlaysT.transport {P : List Prog} {N M : Nat}
    (hMN : 2 ^ M ≤ N) :
    {me o b : Prog} → {a : Action} → {n : Nat} → (t : PlaysT me o b a n) →
    t.cutsOK (instGate P N) → t.citesLE M → t.rawAtoms →
    argOKP P me = true → T43.modestP me = true → T42.maxLitP me ≤ N →
    argOKP P o = true → T43.modestP o = true → T42.maxLitP o ≤ N →
    T43.modestP b = true → T42.maxLitP b ≤ N →
    t.gateOK (instGate P N)
  | _, _, _, _, _, .const, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, _, .self t, hc, hl, hr, h1, h2, h3, h4, h5, h6, _, _ =>
      PlaysT.transport hMN t hc hl hr h1 h2 h3 h4 h5 h6 h2 h3
  | _, _, _, _, _, .opp t, hc, hl, hr, h1, h2, h3, h4, h5, h6, _, _ =>
      PlaysT.transport hMN t hc hl hr h1 h2 h3 h4 h5 h6 h5 h6
  | _, _, _, _, _, .bot (p := p) t, hc, hl, hr, h1, h2, h3, h4, h5, h6, hb, hbl => by
      have hb' : T43.modestP p = true := hb
      have hbl' : T42.maxLitP p ≤ N := by
        simp only [T42.maxLitP] at hbl; exact hbl
      exact PlaysT.transport hMN t hc hl hr h1 h2 h3 h4 h5 h6 hb' hbl'
  | me, o, _, _, _, .sim (p := p) (q := q) t, hc, hl, hr,
      h1, h2, h3, h4, h5, h6, hb, hbl => by
      simp only [T43.modestP, Bool.and_eq_true] at hb
      have hlp : T42.maxLitP p ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      have hlq : T42.maxLitP q ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      have hp : argOKP P (p.subst me o) = true ∧ T43.modestP (p.subst me o) = true := by
        rcases T43.argOK_subst hb.1.1.1 me o with h' | h' | ⟨h', hcl⟩
        · rw [h']; exact ⟨h1, h2⟩
        · rw [h']; exact ⟨h4, h5⟩
        · rw [h']
          exact ⟨by simp only [argOKP, hcl, hb.1.2, Bool.and_self, Bool.or_true, Bool.true_or], hb.1.2⟩
      have hq : argOKP P (q.subst me o) = true ∧ T43.modestP (q.subst me o) = true := by
        rcases T43.argOK_subst hb.1.1.2 me o with h' | h' | ⟨h', hcl⟩
        · rw [h']; exact ⟨h1, h2⟩
        · rw [h']; exact ⟨h4, h5⟩
        · rw [h']
          exact ⟨by simp only [argOKP, hcl, hb.2, Bool.and_self, Bool.or_true, Bool.true_or], hb.2⟩
      have hlp' : T42.maxLitP (p.subst me o) ≤ N :=
        le_trans (T46.maxLitP_subst me o p) (by omega)
      have hlq' : T42.maxLitP (q.subst me o) ≤ N :=
        le_trans (T46.maxLitP_subst me o q) (by omega)
      exact PlaysT.transport hMN t hc hl hr hp.1 hp.2 hlp' hq.1 hq.2 hlq' hp.2 hlp'
  | _, _, _, _, _, .ite_t (b := bg) (p := p) tb hbr tp, hc, hl, hr,
      h1, h2, h3, h4, h5, h6, hb, hbl => by
      simp only [T43.modestP, Bool.and_eq_true] at hb
      have hlb : T42.maxLitP bg ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      have hlp : T42.maxLitP p ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      exact ⟨PlaysT.transport hMN tb hc.1 hl.1 hr.1 h1 h2 h3 h4 h5 h6 hb.1.1 hlb,
        PlaysT.transport hMN tp hc.2 hl.2 hr.2 h1 h2 h3 h4 h5 h6 hb.1.2 hlp⟩
  | _, _, _, _, _, .ite_f (b := bg) (q := q) tb hbr tq, hc, hl, hr,
      h1, h2, h3, h4, h5, h6, hb, hbl => by
      simp only [T43.modestP, Bool.and_eq_true] at hb
      have hlb : T42.maxLitP bg ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      have hlq : T42.maxLitP q ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      exact ⟨PlaysT.transport hMN tb hc.1 hl.1 hr.1 h1 h2 h3 h4 h5 h6 hb.1.1 hlb,
        PlaysT.transport hMN tq hc.2 hl.2 hr.2 h1 h2 h3 h4 h5 h6 hb.2 hlq⟩
  | me, o, _, _, _, .search_t (k := kg) (φ := φg) (p := pb) tg tp, hc, hl, hr,
      h1, h2, h3, h4, h5, h6, hb, hbl => by
      simp only [T43.modestP, Bool.and_eq_true] at hb
      have hgate : instGate P N (φg.subst me o) := by
        constructor
        · refine le_trans (T46.maxLitF_subst me o φg) ?_
          have : T42.maxLitF φg ≤ N := by
            simp only [T42.maxLitP] at hbl; omega
          omega
        · exact modestF_subst_inst P me o h1 h4
            (modestP_instModestP P me h2) (modestP_instModestP P o h5) φg hb.1.1
      have hlpb : T42.maxLitP pb ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      exact ⟨ProvT.transport hMN tg hc.1 hl.2.1 hr.1 hl.1 hgate,
        PlaysT.transport hMN tp hc.2 hl.2.2 hr.2 h1 h2 h3 h4 h5 h6 hb.1.2 hlpb⟩
  | me, o, _, _, _, .search_f (m := mg) (φ := φg) (q := qb) tr tq, hc, hl, hr,
      h1, h2, h3, h4, h5, h6, hb, hbl => by
      simp only [T43.modestP, Bool.and_eq_true] at hb
      have hgate : instGate P N (.neg (φg.subst me o)) := by
        constructor
        · show T42.maxLitF (φg.subst me o) ≤ N
          refine le_trans (T46.maxLitF_subst me o φg) ?_
          have : T42.maxLitF φg ≤ N := by
            simp only [T42.maxLitP] at hbl; omega
          omega
        · show instModestF P (φg.subst me o) = true
          exact modestF_subst_inst P me o h1 h4
            (modestP_instModestP P me h2) (modestP_instModestP P o h5) φg hb.1.1
      have hlqb : T42.maxLitP qb ≤ N := by
        simp only [T42.maxLitP] at hbl; omega
      exact ⟨ProvT.transport hMN tr hc.1 hl.2.1 hr.1 hl.1 hgate,
        PlaysT.transport hMN tq hc.2 hl.2.2 hr.2 h1 h2 h3 h4 h5 h6 hb.2 hlqb⟩

theorem AtomT.transport {P : List Prog} {N M : Nat}
    (hMN : 2 ^ M ≤ N) :
    {k : Nat} → {φ : Formula} → (t : AtomT k φ) →
    t.cutsOK (instGate P N) → t.citesLE M → t.rawAtoms → instGate P N φ →
    t.gateOK (instGate P N)
  | _, _, .mk pl hn, hc, hl, hr, hξ => by
      obtain ⟨hlit, hmod⟩ := hξ
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [T42.maxLitF] at hlit
      exact PlaysT.transport hMN pl hc hl hr.2
        hmod.1.1.1 hr.1.1 (by omega) hmod.1.1.2 hr.1.2 (by omega)
        hr.1.1 (by omega)

theorem ProvT.transport {P : List Prog} {N M : Nat}
    (hMN : 2 ^ M ≤ N) :
    {m : Nat} → {ξ : Formula} → (t : ProvT m ξ) →
    t.cutsOK (instGate P N) → t.citesLE M → t.rawAtoms → m ≤ M →
    instGate P N ξ →
    t.gateOK (instGate P N)
  | _, _, .struct d _, _, _, hr, _, hξ => derivGateOK_of_conclusion_raw d hξ hr
  | _, _, .atom t, hc, hl, hr, _, hξ => AtomT.transport hMN t hc hl hr hξ
  | _, _, .weakenImpl φ' ψ' m' tw hle, hc, hl, hr, hm, hξ =>
      ProvT.transport hMN tw hc hl hr
        (le_trans (by have := Formula.size_pos (.impl φ' ψ'); omega) hm)
        (instGate_impl_iff.mp hξ).2
  | _, _, .searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 qe _ opnt rfl tw hm hsz,
      hc, hl, hr, hmM, hξ => by
      have hpl := (instGate_impl_iff.mp hξ).2
      obtain ⟨hlit, hmod⟩ := hpl
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [T42.maxLitF] at hlit
      have hmee := hmod.1.2
      simp only [instModestP, Bool.and_eq_true] at hmee
      have hgate : instGate P N (ψ₂.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) qe) opnt) := by
        constructor
        · refine le_trans (T46.maxLitF_subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) qe) opnt ψ₂) ?_
          have : T42.maxLitF ψ₂ ≤ N := by
            have := hlit
            simp only [T42.maxLitP] at this ⊢
            omega
          omega
        · exact modestF_subst_inst P
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) qe) opnt
            hmod.1.1.1 hmod.1.1.2 hmod.1.2 hmod.2 ψ₂ hmee.1.2.1.1
      exact ProvT.transport hMN tw hc (hl.2) hr (le_trans hm hl.1) hgate
  | _, _, .implTrans φ' ψ' χ' a b t1 t2 hle, hc, hl, hr, hm, hξ => by
      have h1 := (instGate_impl_iff.mp hξ).1
      have h2 := (instGate_impl_iff.mp hξ).2
      exact ⟨hc.1,
        ProvT.transport hMN t1 hc.2.1 hl.1 hr.1
          (le_trans (by have := Formula.size_pos (.impl φ' χ'); omega) hm)
          (instGate_impl_iff.mpr ⟨h1, hc.1⟩),
        ProvT.transport hMN t2 hc.2.2 hl.2 hr.2
          (le_trans (by have := Formula.size_pos (.impl φ' χ'); omega) hm)
          (instGate_impl_iff.mpr ⟨hc.1, h2⟩)⟩
  | _, _, .atomBoxImpl kB p' q' a' cert hle, hc, hl, hr, hm, hξ =>
      AtomT.transport hMN cert hc hl hr (instGate_impl_iff.mp hξ).1
  | _, _, .boxIntro kIn K φ' tc hle, hc, hl, hr, hm, hξ => by
      obtain ⟨hlit, hmod⟩ := hξ
      simp only [T42.maxLitF] at hlit
      exact ProvT.transport hMN tc hc hl hr
        (le_trans (by have := Formula.size_pos (.box kIn φ'); omega) hm)
        ⟨by omega, hmod⟩
  | _, _, .app K m₁ m₂ φ' α t1 t2 hle, hc, hl, hr, hm, hξ =>
      ⟨hc.1,
        ProvT.transport hMN t1 hc.2.1 hl.1 hr.1
          (le_trans (by have := Formula.size_pos α; omega) hm)
          (instGate_impl_iff.mpr ⟨hc.1, hξ⟩),
        ProvT.transport hMN t2 hc.2.2 hl.2 hr.2
          (le_trans (by have := Formula.size_pos α; omega) hm) hc.1⟩
  | _, _, .axK a' b' c' m'' K φ' α' tP hg1 hle, hc, hl, hr, hm, hξ => by
      have htied := instGate_axK_tied hξ hg1
      exact ⟨htied, ProvT.transport hMN tP hc hl hr
        (le_trans (by have := Formula.size_pos (.impl (.box b' φ') (.box c' α')); omega) hm)
        htied⟩
  | _, _, .box4 _ _ _ _ _ _, _, _, _, _, _ => trivial
  | _, _, .diagF pm fb g K tgt tP hle, hc, hl, hr, hm, hξ => by
      have hfb : fb ≤ N := by
        have hd := PD.T48.diag_lit_bound (ProvT.sound tP)
        have hpm : pm ≤ M := le_trans
          (by have := Formula.size_pos (.impl (.diag g tgt)
                (.impl (.box g (.diag g tgt)) tgt)); omega) hm
        have : (2:Nat) ^ pm ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hpm
        omega
      have htied := instGate_diag_tied (instGate_impl_iff.mp hξ).2 hfb
      exact ⟨htied, ProvT.transport hMN tP hc hl hr
        (le_trans (by have := Formula.size_pos (.impl (.diag g tgt)
          (.impl (.box g (.diag g tgt)) tgt)); omega) hm) htied⟩
  | _, _, .diagB pm fb g K tgt tP hle, hc, hl, hr, hm, hξ => by
      have hfb : fb ≤ N := by
        have hd := PD.T48.diag_lit_bound (ProvT.sound tP)
        have hpm : pm ≤ M := le_trans
          (by have := Formula.size_pos (.impl (.impl (.box g (.diag g tgt)) tgt)
                (.diag g tgt)); omega) hm
        have : (2:Nat) ^ pm ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hpm
        omega
      have htied := instGate_diag_tied (instGate_impl_iff.mp hξ).1 hfb
      exact ⟨htied, ProvT.transport hMN tP hc hl hr
        (le_trans (by have := Formula.size_pos (.impl (.impl (.box g
          (.diag g tgt)) tgt) (.diag g tgt)); omega) hm) htied⟩
  | _, _, .axKf _ _ _ _ _ _ _ _, _, _, _, _, _ => trivial
  | _, _, .impS2 φ' ψ' χ' m₁ m₂ K t1 t2 hle, hc, hl, hr, hm, hξ => by
      have h1 := (instGate_impl_iff.mp hξ).1
      have h2 := (instGate_impl_iff.mp hξ).2
      exact ⟨hc.1,
        ProvT.transport hMN t1 hc.2.1 hl.1 hr.1
          (le_trans (by have := Formula.size_pos (.impl φ' χ'); omega) hm)
          (instGate_impl_iff.mpr ⟨h1, instGate_impl_iff.mpr ⟨hc.1, h2⟩⟩),
        ProvT.transport hMN t2 hc.2.2 hl.2 hr.2
          (le_trans (by have := Formula.size_pos (.impl φ' χ'); omega) hm)
          (instGate_impl_iff.mpr ⟨h1, hc.1⟩)⟩
  | _, _, .boxMono _ _ _ _ _ _, _, _, _, _, _ => trivial
  | _, _, .atomNeg p' q' b' aN m'' tc hne hle, hc, hl, hr, hm, hξ => by
      obtain ⟨hlit, hmod⟩ := hξ
      simp only [instModestF, Bool.and_eq_true] at hmod
      simp only [T42.maxLitF] at hlit
      exact AtomT.transport hMN tc hc hl hr
        ⟨by simp only [T42.maxLitF]; omega,
         by simp only [instModestF, Bool.and_eq_true]; exact hmod⟩
end

/-! ## 5. THE FIRST CERTIFIED INSTANCE of the revised CutRelevance.

DupocBot self-cooperation — a genuine self-referential Löb fact, `Provable` by
`bloeb_engine` — lands in the INSTANCE-GATED stratum, kernel-checked end to end:
the raw tree's full diet passes `instOKb` (verdict (d)), soundness bridges to the
Prop gate, and the gate-generic `toG` produces the `ProvableG` certificate. -/

theorem dupoc_selfcoop_certified :
    T42.ProvableG (instGate [meD] kD) (4096 * W) tgtD :=
  ProvT.toG treeD
    (ProvT.gateOKb_sound (fun _ hb => instOKb_iff.mp hb) treeD (by decide))

#eval s!"(e) kernel-certified: ProvableG (instGate [DupocBot]) of the Löb fact ✓"
