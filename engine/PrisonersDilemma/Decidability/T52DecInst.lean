import PrisonersDilemma.Decidability.T47Stabilization
import PrisonersDilemma.Decidability.T50InstanceLob

/-! # T52 — THE GATE-PARAMETRIC DECIDER (the T44 layer over an arbitrary Bool gate).

T44's bounded decider, checkers, soundness and completeness, with `cutOKb N`
abstracted to `(Gb : Formula → Bool)` and `modestGate N` to a Prop gate `G` tied by
`hGb : ∀ B, Gb B = true ↔ G B`. Coverage needs nothing new: `enumFormula` already
enumerates ALL formulas by size (`enum_complete`), so instance cuts are proposed and
only the gate filter decides. Instantiations at the bottom: the original modest gate
(sanity) and THE INSTANCE GATE — semidecidability of `ProvableG (instGate P N)`.
Everything below the header is T44's text transformed mechanically. -/

namespace PD.T52
open PD PD.T31 PD.T42 PD.T43 PD.T44 PD.T49 PD.T50

section
variable {G : Formula → Prop}

def chkITransG (Gb : Formula → Bool) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        Gb ψ' &&
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A ψ') &&
        rec (k - (Formula.impl A C).size - m₁) (.impl ψ' C)
  | _ => false

def chkAppEG (Gb : Formula → Bool) (rec : Nat → Formula → Bool) (k : Nat) (φ : Formula) : Bool :=
  (List.range k).any fun m₁ => (enumFormula k).any fun φ' =>
    Gb φ' &&
    decide (m₁ + φ.size ≤ k) && rec m₁ (.impl φ' φ) && rec (k - φ.size - m₁) φ'

def chkAxKG (Gb : Formula → Bool) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.box b ψ) (.box c α) =>
      decide ((Formula.impl (.box b ψ) (.box c α)).size ≤ k) &&
      ((List.range (c+1)).any fun a =>
        Gb (.box a (.impl ψ α)) &&
        decide (a + b + α.size ≤ c) &&
        rec (k - (Formula.impl (.box b ψ) (.box c α)).size) (.box a (.impl ψ α)))
  | _ => false

def chkDiagFEG (Gb : Formula → Bool) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.diag g t) (.impl (.box g' (.diag g'' t')) t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        Gb (.impl (.box fb t) t) &&
        rec (k - (Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkDiagBEG (Gb : Formula → Bool) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.impl (.box g (.diag g' t)) t') (.diag g'' t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        Gb (.impl (.box fb t) t) &&
        rec (k - (Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkImpS2EG (Gb : Formula → Bool) (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        Gb ψ' &&
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A (.impl ψ' C)) &&
        rec (k - (Formula.impl A C).size - m₁) (.impl A ψ')
  | _ => false

/-! ## 3. The step operator and its iteration. -/

/-- One rule-firing pass. The atom side runs T3.1's `decCertG` with the current
    approximation `S` as the guard oracle (fuel `k+1` covers the budget-bounded cert
    recursion; guard hops and `search_f` refutations consult `S`). -/
def stepG (Gb : Formula → Bool) (S : Nat → Formula → Bool) : Nat → Formula → Bool := fun k φ =>
  decDeriv k k φ ||
  certOG S (k+1) k φ ||
  chkWeaken S k φ ||
  chkSTS S k φ ||
  chkITransG Gb S k φ ||
  chkAtomBox (fun m ψ => certOG S (m+1) m ψ) k φ ||
  chkBoxIntroE S k φ ||
  chkAppEG Gb S k φ ||
  chkAxKG Gb S k φ ||
  chkBox4E k φ ||
  chkDiagFEG Gb S k φ ||
  chkDiagBEG Gb S k φ ||
  chkAxKfE k φ ||
  chkImpS2EG Gb S k φ ||
  chkBoxMonoE k φ ||
  chkAtomNeg (fun m ψ => certOG S (m+1) m ψ) k φ

/-- The bounded decider: `fuel`-fold iteration of the step operator from `⊥`. Computable,
    total. -/
def decG (Gb : Formula → Bool) : Nat → Nat → Formula → Bool
  | 0 => fun _ _ => false
  | fuel+1 => stepG Gb (decG Gb fuel)

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

theorem decB_sound (Gb : Formula → Bool) (hGb : ∀ B, Gb B = true ↔ G B) : ∀ fuel k φ, decG Gb fuel k φ = true →
    ProvableG (G) k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decG] at h
  | succ f ih =>
    intro k φ h
    rw [decG] at h
    unfold stepG at h
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
      unfold chkITransG at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨⟨⟨hg, hsz⟩, h1⟩, h2⟩⟩ := h
        exact ProvableG.implTrans A ψ' C m₁ _ (ih _ _ h1) (ih _ _ h2) (by omega)
          ((hGb _).mp hg)
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
      unfold chkAppEG at h
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
        decide_eq_true_eq] at h
      obtain ⟨m₁, hm₁, φ', _, ⟨⟨⟨hg, hsz⟩, h1⟩, h2⟩⟩ := h
      exact ProvableG.app k m₁ _ φ' φ (ih _ _ h1) (ih _ _ h2) (by omega) ((hGb _).mp hg)
    · -- axK (gated)
      unfold chkAxKG at h
      split at h
      · rename_i b ψ c α
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨hsz, a, _, ⟨⟨hg, hgate⟩, hr⟩⟩ := h
        exact ProvableG.axK a b c _ k ψ α (ih _ _ hr) hgate (by omega) ((hGb _).mp hg)
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
      unfold chkDiagFEG at h
      split at h
      · rename_i g t g' g'' t' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, ⟨hg, hr⟩⟩ := h
        exact ProvableG.diagF _ fb g k t (ih _ _ hr) (by omega) ((hGb _).mp hg)
      · simp at h
    · -- diagB (gated)
      unfold chkDiagBEG at h
      split at h
      · rename_i g g' t t' g'' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, ⟨hg, hr⟩⟩ := h
        exact ProvableG.diagB _ fb g k t (ih _ _ hr) (by omega) ((hGb _).mp hg)
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
      unfold chkImpS2EG at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, cutOKb,
          decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨⟨⟨hg, hsz⟩, h1⟩, h2⟩⟩ := h
        exact ProvableG.impS2 A ψ' C m₁ _ k (ih _ _ h1) (ih _ _ h2) (by omega)
          ((hGb _).mp hg)
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
        have hs1 := T31.Formula.size_pos (Formula.neg (.plays p q aN))
        rcases hcase with ⟨hOr, hne⟩ | ⟨hOr, hne⟩
        · exact ProvableG.atomNeg p q .C aN _
            (certOG_soundG _ (fun m ψ hh => ih m ψ hh) _ _ _ hOr)
            (fun hh => hne hh.symm) (by omega)
        · exact ProvableG.atomNeg p q .D aN _
            (certOG_soundG _ (fun m ψ hh => ih m ψ hh) _ _ _ hOr)
            (fun hh => hne hh.symm) (by omega)
      · simp at h

/-- Corollary: every `decG` hit is a real engine theorem. -/
theorem decB_sound_Provable (Gb : Formula → Bool) (hGb : ∀ B, Gb B = true ↔ G B) (fuel k : Nat) (φ : Formula)
    (h : decG Gb fuel k φ = true) : Provable k φ :=
  ProvableG_sound (decB_sound Gb hGb fuel k φ h)

/-! ## 6. Monotonicity — more fuel never loses a hit (part b). -/

theorem stepB_mono {Gb : Formula → Bool} {S₁ S₂ : Nat → Formula → Bool}
    (hS : ∀ m ψ, S₁ m ψ = true → S₂ m ψ = true) :
    ∀ k φ, stepG Gb S₁ k φ = true → stepG Gb S₂ k φ = true := by
  intro k φ h
  unfold stepG at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with ((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
    | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))))))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        (certOG_mono2 S₁ S₂ hS _ _ (Nat.le_refl _) _ _ h)))))))))))))))
  · -- chkWeaken
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))))))))
    unfold chkWeaken at h ⊢
    split at h
    · rename_i A B
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, hS _ _ h.2⟩
    · simp at h
  · -- chkSTS
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (Or.inl (Or.inr ?_))))))))))))
    unfold chkSTS at h ⊢
    split at h
    · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, hS _ _ h.2⟩
    · simp at h
  · -- chkITransG
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (Or.inr ?_)))))))))))
    unfold chkITransG at h ⊢
    split at h
    · rename_i A C
      simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
      obtain ⟨m₁, hm₁, ψ', hψ', ⟨⟨hcut, hg⟩, h1⟩, h2⟩ := h
      exact ⟨m₁, hm₁, ψ', hψ', ⟨⟨hcut, hg⟩, hS _ _ h1⟩, hS _ _ h2⟩
    · simp at h
  · -- chkAtomBox (oracle = lagged certOG)
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ?_))))))))))
    unfold chkAtomBox at h ⊢
    split at h
    · rename_i p q a kB p' q' a'
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, certOG_mono2 S₁ S₂ hS _ _ (Nat.le_refl _) _ _ h.2⟩
    · simp at h
  · -- chkBoxIntroE
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ?_)))))))))
    unfold chkBoxIntroE at h ⊢
    split at h
    · rename_i kIn ψ
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, hS _ _ h.2⟩
    · simp at h
  · -- chkAppEG
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))))
    unfold chkAppEG at h ⊢
    simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
    obtain ⟨m₁, hm₁, ψ', hψ', ⟨⟨hcut, hg⟩, h1⟩, h2⟩ := h
    exact ⟨m₁, hm₁, ψ', hψ', ⟨⟨hcut, hg⟩, hS _ _ h1⟩, hS _ _ h2⟩
  · -- chkAxKG
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))
    unfold chkAxKG at h ⊢
    split at h
    · rename_i b ψ c α
      simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
      obtain ⟨hsz, a, ha, ⟨hcut, hg⟩, hr⟩ := h
      exact ⟨hsz, a, ha, ⟨hcut, hg⟩, hS _ _ hr⟩
    · simp at h
  · -- chkBox4E (no rec)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · -- chkDiagFEG
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
    unfold chkDiagFEG at h ⊢
    split at h
    · rename_i g t g' g'' t' t''
      simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
      obtain ⟨hpre, fb, hfb, hcut, hr⟩ := h
      exact ⟨hpre, fb, hfb, hcut, hS _ _ hr⟩
    · simp at h
  · -- chkDiagBEG
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
    unfold chkDiagBEG at h ⊢
    split at h
    · rename_i g g' t t' g'' t''
      simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
      obtain ⟨hpre, fb, hfb, hcut, hr⟩ := h
      exact ⟨hpre, fb, hfb, hcut, hS _ _ hr⟩
    · simp at h
  · -- chkAxKfE (no rec)
    exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · -- chkImpS2EG
    refine Or.inl (Or.inl (Or.inr ?_))
    unfold chkImpS2EG at h ⊢
    split at h
    · rename_i A C
      simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
      obtain ⟨m₁, hm₁, ψ', hψ', ⟨⟨hcut, hg⟩, h1⟩, h2⟩ := h
      exact ⟨m₁, hm₁, ψ', hψ', ⟨⟨hcut, hg⟩, hS _ _ h1⟩, hS _ _ h2⟩
    · simp at h
  · -- chkBoxMonoE (no rec)
    exact Or.inl (Or.inr h)
  · -- chkAtomNeg (oracle = lagged certOG)
    refine Or.inr ?_
    unfold chkAtomNeg at h ⊢
    split at h
    · rename_i p q aN
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      obtain ⟨hsz, hcase⟩ := h
      refine ⟨hsz, ?_⟩
      rcases hcase with ⟨hOr, hne⟩ | ⟨hOr, hne⟩
      · exact Or.inl ⟨certOG_mono2 S₁ S₂ hS _ _ (Nat.le_refl _) _ _ hOr, hne⟩
      · exact Or.inr ⟨certOG_mono2 S₁ S₂ hS _ _ (Nat.le_refl _) _ _ hOr, hne⟩
    · simp at h

theorem decB_mono (Gb : Formula → Bool) : ∀ f₁ f₂, f₁ ≤ f₂ → ∀ k φ,
    decG Gb f₁ k φ = true → decG Gb f₂ k φ = true := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ _ k φ h; simp [decG] at h
  | succ f ih =>
    intro f₂ hle k φ h
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    have hff : f ≤ f₂' := by omega
    rw [decG] at h
    rw [decG]
    exact stepB_mono (fun m ψ => ih f₂' hff m ψ) k φ h

/-! ## 7. ∃-fuel COMPLETENESS — every gated derivation is found. -/

set_option maxHeartbeats 1000000 in
theorem decB_complete (Gb : Formula → Bool) (hGb : ∀ B, Gb B = true ↔ G B) : ∀ {m φ}, ProvableG (G) m φ →
    ∀ K, m ≤ K → ∃ fuel, decG Gb fuel K φ = true := by
  intro m φ h
  refine ProvableG.rec
    (motive_1 := fun me oppo body a n _ =>
      ∀ b, n ≤ b → ∃ F, decCertG (decG Gb F) (b+1) b me oppo body a = true)
    (motive_2 := fun k φ _ => ∀ K, k ≤ K → ∃ F, certOG (decG Gb F) (K+1) K φ = true)
    (motive_3 := fun k φ _ => ∀ K, k ≤ K → ∃ F, decG Gb F K φ = true)
    ?pConst ?pSelf ?pOpp ?pBot ?pSim ?pIte_t ?pIte_f ?pSearch_t ?pSearch_f ?pMk
    ?cStruct ?cAtom ?cWeaken ?cSTS ?cITrans ?cAtomBox ?cBoxIntro ?cApp ?cAxK ?cBox4
    ?cDiagF ?cDiagB ?cAxKf ?cImpS2 ?cBoxMono ?cAtomNeg
    h
  case pConst =>
      intro me oppo a b hb
      refine ⟨0, ?_⟩
      rw [decCertG.eq_def]
      simp [hb]
  case pSelf =>
      intro me oppo a n _ ih b hb
      have hcn : c_node = 1 := rfl
      obtain ⟨F, e⟩ := ih (b - c_node) (by omega)
      refine ⟨F, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega,
        decCertG_mono2 _ _ (fun m ψ hh => hh) _ b (by omega) _ _ _ _ _ e⟩
  case pOpp =>
      intro me oppo a n _ ih b hb
      have hcn : c_node = 1 := rfl
      obtain ⟨F, e⟩ := ih (b - c_node) (by omega)
      refine ⟨F, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega,
        decCertG_mono2 _ _ (fun m ψ hh => hh) _ b (by omega) _ _ _ _ _ e⟩
  case pBot =>
      intro me oppo p a n _ ih b hb
      have hcn : c_node = 1 := rfl
      obtain ⟨F, e⟩ := ih (b - c_node) (by omega)
      refine ⟨F, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega,
        decCertG_mono2 _ _ (fun m ψ hh => hh) _ b (by omega) _ _ _ _ _ e⟩
  case pSim =>
      intro a n me oppo p q _ ih b hb
      have hcn : c_node = 1 := rfl
      obtain ⟨F, e⟩ := ih (b - c_node) (by omega)
      refine ⟨F, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega,
        decCertG_mono2 _ _ (fun m ψ hh => hh) _ b (by omega) _ _ _ _ _ e⟩
  case pIte_t =>
      intro me oppo g r m a' p a n q _ hr _ ihg ihp b hb
      have hcn : c_node = 1 := rfl
      have hpos : 1 ≤ n := by
        cases ‹PlaysProofG _ me oppo p a n› <;>
          simp only [c_leaf, c_node, c_guard] <;> omega
      obtain ⟨F₁, e₁⟩ := ihg m le_rfl
      obtain ⟨F₂, e₂⟩ := ihp (b - m - c_node) (by omega)
      refine ⟨max F₁ F₂, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
      refine ⟨by omega, m, by omega, r, by cases r <;> simp, ⟨by omega, ?_⟩, ?_⟩
      · exact decCertG_mono2 _ _
          (fun mm ψ hh => decB_mono Gb F₁ (max F₁ F₂) (by omega) mm ψ hh)
          _ b (by omega) _ _ _ _ _ e₁
      · rw [if_pos hr]
        exact decCertG_mono2 _ _
          (fun mm ψ hh => decB_mono Gb F₂ (max F₁ F₂) (by omega) mm ψ hh)
          _ b (by omega) _ _ _ _ _ e₂
  case pIte_f =>
      intro me oppo g r m a' q a n p _ hr _ ihg ihq b hb
      have hcn : c_node = 1 := rfl
      have hpos : 1 ≤ n := by
        cases ‹PlaysProofG _ me oppo q a n› <;>
          simp only [c_leaf, c_node, c_guard] <;> omega
      obtain ⟨F₁, e₁⟩ := ihg m le_rfl
      obtain ⟨F₂, e₂⟩ := ihq (b - m - c_node) (by omega)
      refine ⟨max F₁ F₂, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
      refine ⟨by omega, m, by omega, r, by cases r <;> simp, ⟨by omega, ?_⟩, ?_⟩
      · exact decCertG_mono2 _ _
          (fun mm ψ hh => decB_mono Gb F₁ (max F₁ F₂) (by omega) mm ψ hh)
          _ b (by omega) _ _ _ _ _ e₁
      · rw [if_neg (by simp [hr])]
        exact decCertG_mono2 _ _
          (fun mm ψ hh => decB_mono Gb F₂ (max F₁ F₂) (by omega) mm ψ hh)
          _ b (by omega) _ _ _ _ _ e₂
  case pSearch_t =>
      intro kg me oppo p a n g q _ _ ihg ihp b hb
      have hcn : c_node = 1 := rfl
      have hcg : 1 ≤ c_guard kg := by unfold c_guard; omega
      obtain ⟨F₁, e₁⟩ := ihg kg le_rfl
      obtain ⟨F₂, e₂⟩ := ihp (b - c_guard kg - c_node) (by omega)
      refine ⟨max F₁ F₂, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine Or.inl ⟨⟨decB_mono Gb F₁ (max F₁ F₂) (by omega) _ _ e₁, by omega⟩, ?_⟩
      exact decCertG_mono2 _ _
        (fun mm ψ hh => decB_mono Gb F₂ (max F₁ F₂) (by omega) mm ψ hh)
        _ b (by omega) _ _ _ _ _ e₂
  case pSearch_f =>
      intro m me oppo q a n kg g p _ _ ihn ihq b hb
      have hcn : c_node = 1 := rfl
      obtain ⟨F₁, e₁⟩ := ihn m le_rfl
      obtain ⟨F₂, e₂⟩ := ihq (b - m - kg - c_node) (by omega)
      refine ⟨max F₁ F₂, ?_⟩
      rw [decCertG.eq_def]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.mem_range]
      refine Or.inr ⟨m, by omega,
        ⟨decB_mono Gb F₁ (max F₁ F₂) (by omega) _ _ e₁, by omega⟩, ?_⟩
      exact decCertG_mono2 _ _
        (fun mm ψ hh => decB_mono Gb F₂ (max F₁ F₂) (by omega) mm ψ hh)
        _ b (by omega) _ _ _ _ _ e₂
  case pMk =>
      intro me oppo a n k _ hle ih K hmK
      obtain ⟨F, e⟩ := ih K (by omega)
      exact ⟨F, e⟩
  case cStruct =>
      intro φ0 k0 hd K hmK
      obtain ⟨d, hsz⟩ := hd
      refine ⟨1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire := decDeriv_complete d K K (by omega) le_rfl
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtom =>
      intro k0 φ0 _hatom ih K hmK
      obtain ⟨F, e⟩ := ih K hmK
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      simp only [e, Bool.or_true, Bool.true_or]
  case cWeaken =>
      intro k A B m' hψ hle ih K hmK
      have h1 := T31.Formula.size_pos (Formula.impl A B)
      obtain ⟨F, e⟩ := ih (K - (Formula.impl A B).size) (by omega)
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkWeaken (decG Gb F) K (Formula.impl A B) = true := by
        unfold chkWeaken
        have hg : (Formula.impl A B).size ≤ K := by omega
        simp [e, hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cSTS =>
      intro k k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle ih K hmK
      subst hme
      obtain ⟨F, e⟩ := ih k₂ hmk
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkSTS (decG Gb F) K
          (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)) = true := by
        unfold chkSTS
        have hg : c_guard k₂ + (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)).size ≤ K := by
          omega
        simp [e, hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cITrans =>
      intro k A B C a b h1 h2 hle hg ih1 ih2 K hmK
      have hAC := T31.Formula.size_pos (Formula.impl A C)
      obtain ⟨F₁, e₁⟩ := ih1 a le_rfl
      obtain ⟨F₂, e₂⟩ := ih2 (K - (Formula.impl A C).size - a) (by omega)
      refine ⟨max F₁ F₂ + 1, ?_⟩
      rw [decG]
      unfold stepG
      have e₁' := decB_mono Gb F₁ (max F₁ F₂) (Nat.le_max_left _ _) _ _ e₁
      have e₂' := decB_mono Gb F₂ (max F₁ F₂) (Nat.le_max_right _ _) _ _ e₂
      have hi1 := provable_impl_size (ProvableG_sound h1)
      have hfire : chkITransG Gb (decG Gb (max F₁ F₂)) K (Formula.impl A C) = true := by
        unfold chkITransG
        simp only [List.any_eq_true, List.mem_range]
        have hBsz : B.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨a, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have hgg : a + (Formula.impl A C).size ≤ K := by omega
        simp [e₁', e₂', hgg, (hGb _).mpr hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtomBox =>
      intro k kBox p q a _hatom hle ih K hmK
      obtain ⟨F, e⟩ := ih kBox le_rfl
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkAtomBox (fun m ψ => certOG (decG Gb F) (m+1) m ψ) K
          (Formula.impl (.plays p q a) (.box kBox (.plays p q a))) = true := by
        unfold chkAtomBox
        have hg : kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ K := by
          omega
        simp [e, hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBoxIntro =>
      intro kIn K' A hprem hle ih K hmK
      have h1 := T31.Formula.size_pos (Formula.box kIn A)
      obtain ⟨F, e⟩ := ih kIn le_rfl
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkBoxIntroE (decG Gb F) K (Formula.box kIn A) = true := by
        unfold chkBoxIntroE
        have hg : kIn + (Formula.box kIn A).size ≤ K := by omega
        simp [e, hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cApp =>
      intro k' m₁ m₂ A B h1 h2 hle hg ih1 ih2 K hmK
      have hB := T31.Formula.size_pos B
      obtain ⟨F₁, e₁⟩ := ih1 m₁ le_rfl
      obtain ⟨F₂, e₂⟩ := ih2 (K - B.size - m₁) (by omega)
      refine ⟨max F₁ F₂ + 1, ?_⟩
      rw [decG]
      unfold stepG
      have e₁' := decB_mono Gb F₁ (max F₁ F₂) (Nat.le_max_left _ _) _ _ e₁
      have e₂' := decB_mono Gb F₂ (max F₁ F₂) (Nat.le_max_right _ _) _ _ e₂
      have hi1 := provable_impl_size (ProvableG_sound h1)
      have hfire : chkAppEG Gb (decG Gb (max F₁ F₂)) K B = true := by
        unfold chkAppEG
        simp only [List.any_eq_true, List.mem_range]
        have hAsz : A.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨m₁, by omega, A, (enum_complete K).2 A hAsz, ?_⟩
        have hgg : m₁ + B.size ≤ K := by omega
        simp [e₁', e₂', hgg, (hGb _).mpr hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAxK =>
      intro a b c m' K' A B hprem hgate hle hg ih K hmK
      have h1 := T31.Formula.size_pos (Formula.impl (.box b A) (.box c B))
      obtain ⟨F, e⟩ := ih (K - (Formula.impl (.box b A) (.box c B)).size) (by omega)
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkAxKG Gb (decG Gb F) K
          (Formula.impl (.box b A) (.box c B)) = true := by
        unfold chkAxKG
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
        have hB := T31.Formula.size_pos B
        exact ⟨by omega, a, by omega, ⟨(hGb _).mpr hg, by omega⟩, e⟩
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBox4 =>
      intro a b K' A hgate hle K hmK
      refine ⟨1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkBox4E K (Formula.impl (.box a A) (.box b (.box a A))) = true := by
        unfold chkBox4E
        have hgg : (Formula.impl (.box a A) (.box b (.box a A))).size ≤ K := by omega
        simp [hgate, hgg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cDiagF =>
      intro pm fb g K' tgt hgate hle hg ih K hmK
      have h1 := T31.Formula.size_pos (Formula.impl (.diag g tgt)
        (.impl (.box g (.diag g tgt)) tgt))
      have hgsz := provable_impl_size (ProvableG_sound hgate)
      obtain ⟨F, e⟩ := ih (K - (Formula.impl (.diag g tgt)
        (.impl (.box g (.diag g tgt)) tgt)).size) (by omega)
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkDiagFEG Gb (decG Gb F) K
          (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)) = true := by
        unfold chkDiagFEG
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_self_eq_true,
          decide_eq_true_eq, and_true, true_and]
        have hgg : (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K := by
          omega
        refine ⟨hgg, fb, ?_, (hGb _).mpr hg, e⟩
        refine lt_two_pow_of_log2_lt ?_
        simp only [Formula.size] at hgsz
        omega
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cDiagB =>
      intro pm fb g K' tgt hgate hle hg ih K hmK
      have h1 := T31.Formula.size_pos (Formula.impl (.impl (.box g (.diag g tgt)) tgt)
        (.diag g tgt))
      have hgsz := provable_impl_size (ProvableG_sound hgate)
      obtain ⟨F, e⟩ := ih (K - (Formula.impl (.impl (.box g (.diag g tgt)) tgt)
        (.diag g tgt)).size) (by omega)
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkDiagBEG Gb (decG Gb F) K
          (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)) = true := by
        unfold chkDiagBEG
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_self_eq_true,
          decide_eq_true_eq, and_true, true_and]
        have hgg : (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K := by
          omega
        refine ⟨hgg, fb, ?_, (hGb _).mpr hg, e⟩
        refine lt_two_pow_of_log2_lt ?_
        simp only [Formula.size] at hgsz
        omega
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAxKf =>
      intro a b c K' A B hgate hle K hmK
      refine ⟨1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkAxKfE K (Formula.impl (.box a (.impl A B))
          (.impl (.box b A) (.box c B))) = true := by
        unfold chkAxKfE
        have hgg : (Formula.impl (.box a (.impl A B)) (.impl (.box b A) (.box c B))).size ≤ K := by
          omega
        simp [hgate, hgg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cImpS2 =>
      intro A B C m₁ m₂ K' h1 h2 hle hg ih1 ih2 K hmK
      have hAC := T31.Formula.size_pos (Formula.impl A C)
      obtain ⟨F₁, e₁⟩ := ih1 m₁ le_rfl
      obtain ⟨F₂, e₂⟩ := ih2 (K - (Formula.impl A C).size - m₁) (by omega)
      refine ⟨max F₁ F₂ + 1, ?_⟩
      rw [decG]
      unfold stepG
      have e₁' := decB_mono Gb F₁ (max F₁ F₂) (Nat.le_max_left _ _) _ _ e₁
      have e₂' := decB_mono Gb F₂ (max F₁ F₂) (Nat.le_max_right _ _) _ _ e₂
      have hi1 := provable_impl_size (ProvableG_sound h1)
      have hfire : chkImpS2EG Gb (decG Gb (max F₁ F₂)) K (Formula.impl A C) = true := by
        unfold chkImpS2EG
        simp only [List.any_eq_true, List.mem_range]
        have hBsz : B.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨m₁, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have hgg : m₁ + (Formula.impl A C).size ≤ K := by omega
        simp [e₁', e₂', hgg, (hGb _).mpr hg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBoxMono =>
      intro a b K' A hab hle K hmK
      refine ⟨1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkBoxMonoE K (Formula.impl (.box a A) (.box b A)) = true := by
        unfold chkBoxMonoE
        have hgg : (Formula.impl (.box a A) (.box b A)).size ≤ K := by omega
        simp [hab, hgg]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtomNeg =>
      intro k p q b aN m' _hatom hne hle ih K hmK
      have h1 := T31.Formula.size_pos (Formula.neg (.plays p q aN))
      obtain ⟨F, e⟩ := ih (K - (Formula.neg (.plays p q aN)).size) (by omega)
      refine ⟨F + 1, ?_⟩
      rw [decG]
      unfold stepG
      have hfire : chkAtomNeg (fun m ψ => certOG (decG Gb F) (m+1) m ψ) K
          (Formula.neg (.plays p q aN)) = true := by
        unfold chkAtomNeg
        have hsz : (Formula.neg (.plays p q aN)).size ≤ K := by omega
        cases b with
        | C =>
            have hne' : aN ≠ Action.C := fun hh => hne hh.symm
            simp [e, hne', hsz]
        | D =>
            have hne' : aN ≠ Action.D := fun hh => hne hh.symm
            simp [e, hne', hsz]
      simp only [hfire, Bool.or_true, Bool.true_or]

/-! ## 8. THE PAYOFF (part b) — the modest stratum is semidecidable by its own enumerator;
the fuel bound over the finite query space (part c) will upgrade this to DECIDABLE. -/

theorem ProvableG_iff_decG (Gb : Formula → Bool) (hGb : ∀ B, Gb B = true ↔ G B)
    (k : Nat) (φ : Formula) :
    ProvableG G k φ ↔ ∃ fuel, decG Gb fuel k φ = true :=
  ⟨fun h => decB_complete Gb hGb h k le_rfl,
   fun ⟨f, hf⟩ => decB_sound Gb hGb f k φ hf⟩


end

/-! ## Instantiations. -/

/-- Sanity: the original modest decider is the `cutOKb` instantiation. -/
theorem ProvableG_modest_iff_decG (N k : Nat) (φ : Formula) :
    ProvableG (T44.modestGate N) k φ ↔ ∃ fuel, decG (T44.cutOKb N) fuel k φ = true :=
  ProvableG_iff_decG (T44.cutOKb N) (fun _ => T44.cutOKb_iff) k φ

/-- **THE PAYOFF**: the instance-gated stratum is semidecidable both ways — the
    repaired CutRelevance target is captured by a computable enumerator. -/
theorem ProvableG_inst_iff_decG (P : List Prog) (N k : Nat) (φ : Formula) :
    ProvableG (instGate P N) k φ ↔ ∃ fuel, decG (instOKb P N) fuel k φ = true :=
  ProvableG_iff_decG (instOKb P N) (fun _ => instOKb_iff) k φ

end PD.T52
