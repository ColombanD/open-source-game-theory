import PrisonersDilemma.Research.Spikes.transcript.T31EngineDecider
import PrisonersDilemma.Research.Spikes.transcript.T42ProvableB
import PrisonersDilemma.Research.Spikes.transcript.T43ModestUniverse

/-!
# T4.4 spike — `decB`: the modest-bounded decider (part a: the step operator, SOUND).

`DECIDABILITY_ROADMAP.md` T4.2 pipeline (i), assembly stage. The target relation is
`ProvableG (modestGate N)` (T4.2's gate-parametric system at the DECIDABLE gate): cut
formulas and the enumerated `axK`/`diag` premises must be literal-bounded (`maxLitF ≤ N` —
keeps hop budgets in a finite set, T4.1a) AND modest (`modestF` — keeps the cert queries
their atoms spawn inside the T4.3 finite universe).

This part ships the computable machinery and its SOUNDNESS:

  * `cutOKb N` — the Bool gate; `modestGate N` — its Prop counterpart;
  * the six GATED checker variants (`chkITransB`/`chkAppEB`/`chkAxKB`/`chkDiagFEB`/
    `chkDiagBEB`/`chkImpS2EB`) — T3.1's checkers with the gate inserted into the
    enumeration sweeps; the other ten checkers are reused from T3.1 verbatim;
  * **`stepB N`** — one rule-firing pass over an approximation `S : Nat → Formula → Bool`:
    the logic rules via the checkers, the atom side via T3.1's `decCertG` run WITH `S` AS
    THE GUARD ORACLE (budget-bounded recursion, fuel `k+1` — the cert layer needs no
    stabilization of its own: its budgets strictly decrease; only the guard hops cross
    back into `S`);
  * `decB N fuel := stepB N ^[fuel] ⊥` — simultaneously the fueled decider AND the
    iteration whose stabilization (part b) will yield the fuel bound `|query space|`;
  * `decCertG_soundG` / `certOG_soundG` — T3.1's certificate soundness re-targeted at the
    gated triple;
  * **`decB_sound`** — every hit at every fuel is a real `ProvableG (modestGate N)`
    derivation (hence `Provable`, via `ProvableG_sound`).

Part b (next): ∃-fuel completeness for `ProvableG (modestGate N)`, the in-space closure
(consuming T4.3's step lemmas), and the T4.1a countP-stabilization giving the computable
fuel bound — decidability of the modest stratum.
-/

namespace PD.T44
open PD PD.T31 PD.T42 PD.T43

/-! ## 1. The decidable gate. -/

/-- The Prop gate: literal-bounded (finite hop budgets) and modest (finite cert universe). -/
def modestGate (N : Nat) : Formula → Prop :=
  fun B => maxLitF B ≤ N ∧ modestF B = true

/-- The Bool gate used inside the checkers. -/
def cutOKb (N : Nat) (B : Formula) : Bool :=
  decide (maxLitF B ≤ N) && modestF B

theorem cutOKb_iff {N : Nat} {B : Formula} :
    cutOKb N B = true ↔ modestGate N B := by
  simp [cutOKb, modestGate, Bool.and_eq_true]

/-! ## 2. The six gated checker variants (T3.1's shapes + the gate in the sweep). -/

def chkITransB (N : Nat) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        cutOKb N ψ' &&
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A ψ') &&
        rec (k - (Formula.impl A C).size - m₁) (.impl ψ' C)
  | _ => false

def chkAppEB (N : Nat) (rec : Nat → Formula → Bool) (k : Nat) (φ : Formula) : Bool :=
  (List.range k).any fun m₁ => (enumFormula k).any fun φ' =>
    cutOKb N φ' &&
    decide (m₁ + φ.size ≤ k) && rec m₁ (.impl φ' φ) && rec (k - φ.size - m₁) φ'

def chkAxKB (N : Nat) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.box b ψ) (.box c α) =>
      decide ((Formula.impl (.box b ψ) (.box c α)).size ≤ k) &&
      ((List.range (c+1)).any fun a =>
        cutOKb N (.box a (.impl ψ α)) &&
        decide (a + b + α.size ≤ c) &&
        rec (k - (Formula.impl (.box b ψ) (.box c α)).size) (.box a (.impl ψ α)))
  | _ => false

def chkDiagFEB (N : Nat) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.diag g t) (.impl (.box g' (.diag g'' t')) t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        cutOKb N (.impl (.box fb t) t) &&
        rec (k - (Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkDiagBEB (N : Nat) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.impl (.box g (.diag g' t)) t') (.diag g'' t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        cutOKb N (.impl (.box fb t) t) &&
        rec (k - (Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkImpS2EB (N : Nat) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        cutOKb N ψ' &&
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A (.impl ψ' C)) &&
        rec (k - (Formula.impl A C).size - m₁) (.impl A ψ')
  | _ => false

/-! ## 3. The step operator and its iteration. -/

/-- One rule-firing pass. The atom side runs T3.1's `decCertG` with the current
    approximation `S` as the guard oracle (fuel `k+1` covers the budget-bounded cert
    recursion; guard hops and `search_f` refutations consult `S`). -/
def stepB (N : Nat) (S : Nat → Formula → Bool) : Nat → Formula → Bool := fun k φ =>
  decDeriv k k φ ||
  certOG S (k+1) k φ ||
  chkWeaken S k φ ||
  chkSTS S k φ ||
  chkITransB N S k φ ||
  chkAtomBox (fun m ψ => certOG S (m+1) m ψ) k φ ||
  chkBoxIntroE S k φ ||
  chkAppEB N S k φ ||
  chkAxKB N S k φ ||
  chkBox4E k φ ||
  chkDiagFEB N S k φ ||
  chkDiagBEB N S k φ ||
  chkAxKfE k φ ||
  chkImpS2EB N S k φ ||
  chkBoxMonoE k φ ||
  chkAtomNeg (fun m ψ => certOG S (m+1) m ψ) k φ

/-- The bounded decider: `fuel`-fold iteration of the step operator from `⊥`. Computable,
    total. -/
def decB (N : Nat) : Nat → Nat → Formula → Bool
  | 0 => fun _ _ => false
  | fuel+1 => stepB N (decB N fuel)

/-! ## 4. Certificate soundness, re-targeted at the gated triple. -/

theorem decCertG_soundG {G : Formula → Prop} (D : Nat → Formula → Bool)
    (hD : ∀ m ψ, D m ψ = true → ProvableG G m ψ) :
    ∀ fuel b me oppo body a, decCertG D fuel b me oppo body a = true →
      ∃ n, PlaysProofG G me oppo body a n ∧ n ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro b me oppo body a h; simp [decCertG] at h
  | succ f ih =>
    intro b me oppo body a h
    rw [decCertG.eq_def] at h
    simp only [] at h
    cases body with
    | const c =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, hb⟩ := h
        exact ⟨c_leaf, .const, hb⟩
    | self =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .self cert, by omega⟩
    | opp =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .opp cert, by omega⟩
    | bot p =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .bot cert, by omega⟩
    | sim p q =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .sim cert, by omega⟩
    | ite g a' p q =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
          List.mem_range] at h
        obtain ⟨hb, m, hm, r, _, ⟨hmb, hg⟩, hbr⟩ := h
        obtain ⟨n₁, cert₁, hn₁⟩ := ih _ _ _ _ _ hg
        by_cases hr : (r == a') = true
        · rw [if_pos hr] at hbr
          obtain ⟨n₂, cert₂, hn₂⟩ := ih _ _ _ _ _ hbr
          exact ⟨n₁ + n₂ + c_node, .ite_t cert₁ hr cert₂, by omega⟩
        · rw [if_neg hr] at hbr
          obtain ⟨n₂, cert₂, hn₂⟩ := ih _ _ _ _ _ hbr
          have hrf : (r == a') = false := by simpa using hr
          exact ⟨n₁ + n₂ + c_node, .ite_f cert₁ hrf cert₂, by omega⟩
    | search kg g p q =>
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
          List.mem_range] at h
        rcases h with ⟨⟨hGuard, hcost⟩, hr⟩ | ⟨m, hm, ⟨hNeg, hcost⟩, hr⟩
        · obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
          exact ⟨n + c_guard kg + c_node, .search_t (hD _ _ hGuard) cert, by omega⟩
        · obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
          exact ⟨n + m + kg + c_node, .search_f (hD _ _ hNeg) cert, by omega⟩

theorem certOG_soundG {G : Formula → Prop} (D : Nat → Formula → Bool)
    (hD : ∀ m ψ, D m ψ = true → ProvableG G m ψ) (fuel : Nat) :
    ∀ k φ, certOG D fuel k φ = true → AtomProvableG G k φ := by
  intro k φ h
  unfold certOG at h
  split at h
  · rename_i p q a
    obtain ⟨n, cert, hn⟩ := decCertG_soundG D hD fuel k p q p a h
    exact ⟨cert, hn⟩
  · simp at h

/-! ## 5. SOUNDNESS of the bounded decider. -/

theorem decB_sound (N : Nat) : ∀ fuel k φ, decB N fuel k φ = true →
    ProvableG (modestGate N) k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decB] at h
  | succ f ih =>
    intro k φ h
    rw [decB] at h
    unfold stepB at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
      | h) | h) | h) | h
    · -- struct
      obtain ⟨d, hsz⟩ := decDeriv_sound k k φ h
      exact ProvableG.struct ⟨d, hsz⟩
    · -- atom (cert search with the lagged approximation as guard oracle)
      exact ProvableG.atom (certOG_soundG _ (fun m ψ hh => ih m ψ hh) _ k φ h)
    · -- weakenImpl
      unfold chkWeaken at h
      split at h
      · rename_i A B
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, hr⟩ := h
        exact ProvableG.weakenImpl A B _ (ih _ _ hr) (by omega)
      · simp at h
    · -- searchThenSearch_t
      unfold chkSTS at h
      split at h
      · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩, hr⟩ := h
        exact ProvableG.searchThenSearch_t k₁ k₂ k₂ ψ₁ ψ₂ c0 c1 q _ opnt rfl
          (ih _ _ hr) (Nat.le_refl _) hsz
      · simp at h
    · -- implTrans (gated)
      unfold chkITransB at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨⟨⟨⟨hlit, hmod⟩, hsz⟩, h1⟩, h2⟩⟩ := h
        exact ProvableG.implTrans A ψ' C m₁ _ (ih _ _ h1) (ih _ _ h2) (by omega)
          ⟨hlit, hmod⟩
      · simp at h
    · -- atomBoxImpl
      unfold chkAtomBox at h
      split at h
      · rename_i p q a kB p' q' a'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hgate⟩, hOr⟩ := h
        exact ProvableG.atomBoxImpl kB p q a
          (certOG_soundG _ (fun m ψ hh => ih m ψ hh) _ _ _ hOr) hgate
      · simp at h
    · -- boxIntro
      unfold chkBoxIntroE at h
      split at h
      · rename_i kIn ψ
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hgate, hr⟩ := h
        exact ProvableG.boxIntro kIn k ψ (ih _ _ hr) hgate
      · simp at h
    · -- app (gated)
      unfold chkAppEB at h
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
        decide_eq_true_eq] at h
      obtain ⟨m₁, hm₁, φ', _, ⟨⟨⟨⟨hlit, hmod⟩, hsz⟩, h1⟩, h2⟩⟩ := h
      exact ProvableG.app k m₁ _ φ' φ (ih _ _ h1) (ih _ _ h2) (by omega) ⟨hlit, hmod⟩
    · -- axK (gated)
      unfold chkAxKB at h
      split at h
      · rename_i b ψ c α
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨hsz, a, _, ⟨⟨⟨hlit, hmod⟩, hgate⟩, hr⟩⟩ := h
        exact ProvableG.axK a b c _ k ψ α (ih _ _ hr) hgate (by omega) ⟨hlit, hmod⟩
      · simp at h
    · -- box4
      unfold chkBox4E at h
      split at h
      · rename_i a ψ b a' ψ'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hgate⟩, hsz⟩ := h
        exact ProvableG.box4 a b k ψ hgate hsz
      · simp at h
    · -- diagF (gated)
      unfold chkDiagFEB at h
      split at h
      · rename_i g t g' g'' t' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, ⟨⟨hlit, hmod⟩, hr⟩⟩ := h
        exact ProvableG.diagF _ fb g k t (ih _ _ hr) (by omega) ⟨hlit, hmod⟩
      · simp at h
    · -- diagB (gated)
      unfold chkDiagBEB at h
      split at h
      · rename_i g g' t t' g'' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, ⟨⟨hlit, hmod⟩, hr⟩⟩ := h
        exact ProvableG.diagB _ fb g k t (ih _ _ hr) (by omega) ⟨hlit, hmod⟩
      · simp at h
    · -- axKf
      unfold chkAxKfE at h
      split at h
      · rename_i a ψ α b ψ' c α'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hgate⟩, hsz⟩ := h
        exact ProvableG.axKf a b c k ψ α hgate hsz
      · simp at h
    · -- impS2 (gated)
      unfold chkImpS2EB at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨⟨⟨⟨hlit, hmod⟩, hsz⟩, h1⟩, h2⟩⟩ := h
        exact ProvableG.impS2 A ψ' C m₁ _ k (ih _ _ h1) (ih _ _ h2) (by omega)
          ⟨hlit, hmod⟩
      · simp at h
    · -- boxMono
      unfold chkBoxMonoE at h
      split at h
      · rename_i a ψ b ψ'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, hab⟩, hsz⟩ := h
        exact ProvableG.boxMono a b k ψ hab hsz
      · simp at h
    · -- atomNeg
      unfold chkAtomNeg at h
      split at h
      · rename_i p q aN
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, hcase⟩ := h
        have hs1 := Formula.size_pos (Formula.neg (.plays p q aN))
        rcases hcase with ⟨hOr, hne⟩ | ⟨hOr, hne⟩
        · exact ProvableG.atomNeg p q .C aN _
            (certOG_soundG _ (fun m ψ hh => ih m ψ hh) _ _ _ hOr)
            (fun hh => hne hh.symm) (by omega)
        · exact ProvableG.atomNeg p q .D aN _
            (certOG_soundG _ (fun m ψ hh => ih m ψ hh) _ _ _ hOr)
            (fun hh => hne hh.symm) (by omega)
      · simp at h

/-- Corollary: every `decB` hit is a real engine theorem. -/
theorem decB_sound_Provable (N : Nat) (fuel k : Nat) (φ : Formula)
    (h : decB N fuel k φ = true) : Provable k φ :=
  ProvableG_sound (decB_sound N fuel k φ h)

end PD.T44
