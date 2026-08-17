import PrisonersDilemma.BaseTheorems

/-!
# LlmLemmas — the proof agent's DERIVED-rule library

Theorems over the existing proof system `Pf`, added autonomously by the proof agent via
the `add_base_lemma` tool (Tier 1 of the OUTCOME-OPEN escalation ladder). Everything here
is kernel-checked against the unchanged engine — nothing is postulated, so this file
carries no trust obligations beyond the engine itself. Additive-only; each block below is
one tool call.
-/

open PD PD.BaseTheorems

namespace PD.LlmLemmas

/-- Seed example (the expected format): reflect a fired oracle back into provability. -/
theorem pf_of_proofSearch {k : Nat} {φ : Formula} (h : proofSearch k φ = true) : Pf k φ :=
  (proofSearch_spec k φ).1 h


/-! ### loeb_premise_boxMono (agent-added) -/

/-- Weaken a Löb premise's box subscript DOWN in the antecedent: from `□_b φ → φ`
    and `a ≤ b`, get `□_a φ → φ` (upward `boxMono` into the premise's antecedent). -/
theorem loeb_premise_boxMono {a b m K : Nat} {φ : Formula}
    (h : Pf m (.impl (.box b φ) φ)) (hab : a ≤ b)
    (hsz : (Formula.impl (.box a φ) (.box b φ)).size + m
           + (Formula.impl (.box a φ) φ).size ≤ K) :
    Pf K (.impl (.box a φ) φ) :=
  Pf.implTrans _ _ _ _ m
    (Pf.boxMono a b _ φ hab (Nat.le_refl _)) h hsz


/-! ### wv_budget_census (agent-added) -/

/-- Parametric budget-gated WV census: for a play-C-forced relation `S` closed under sim,
    whose members never actually-play `.D` within budget `≤ k` (`h_noD`, the FLOOR), every
    `≤ k`-provable formula is `WV S`-true. This is the budget-aware variant of the master
    `wv_sound_upto` for SEARCHER bases with a DEFECTING else-branch (where the master's
    UNCONDITIONAL `h_search_f` obligation `a = .C` is unsatisfiable — the else literally plays
    `.D` — but the `search_f` cost FLOOR keeps that `.D`-certificate strictly above every budget
    `≤ k`, so the only rule that could refute a WV-forced `.neg`-atom, `atomNeg`, cannot fire).
    Consumed by the WaryBot-vs-DupocBot outcome (both bots are searchers whose "wrong" branch
    defects, so neither can sit in the master's `S`). -/
theorem wv_budget_census (k : Nat) (S : Prog → Prog → Prop)
    (h_nb : ∀ oppo z, ¬ S oppo (.bot z))
    (h_simS : ∀ p q o, S (p.subst (.sim p q) o) (q.subst (.sim p q) o) → S (.sim p q) o)
    (h_botsimS : ∀ p q o, S (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      S (.bot (.sim p q)) o)
    (h_noD : ∀ p q, S p q → ∀ n, PlaysProof p q p .D n → k < n) :
    ∀ K φ, Pf K φ → K ≤ k → WV S φ := by
  intro K φ hp
  induction hp using Pf.induct with
  | atom k' φ' h =>
      intro _hK
      cases h with
      | mk hpp hn =>
          rename_i me oppo a nn
          rw [WV_plays]
          exact Or.inr ((sound_upto nn).1 me oppo me a nn hpp le_rfl)
  | atomNeg k' p q b aN m hcert hne hle =>
      intro hK
      rw [WV_neg, WV_plays]
      rintro (⟨rfl, hSpq⟩ | hint)
      · cases b with
        | C => exact hne rfl
        | D =>
            have hmk : m ≤ k := by
              have := Formula.size_pos (Formula.neg (.plays p q .C)); omega
            cases hcert with
            | mk hpp hn => have hlt := h_noD p q hSpq _ hpp; omega
      · exact (Pf_sound k' _ (Pf.atomNeg p q b aN m hcert hne hle)) hint
  | searchBranch k' g ψ a b me opponent hme hle =>
      intro _hK
      rw [WV_impl, WV_box]; intro hbox; rw [WV_plays]
      exact Or.inr ((Pf_sound k' _ (Pf.searchBranch g ψ a b me opponent hme hle)) hbox)
  | simStep k' me p q opponent a hme hle =>
      intro _hK
      rw [WV_impl, WV_plays, WV_plays]
      rintro (⟨rfl, hSP⟩ | hint)
      · subst hme; exact Or.inl ⟨rfl, h_simS p q opponent hSP⟩
      · exact Or.inr ((Pf_sound k' _ (Pf.simStep me p q opponent a hme hle)) hint)
  | botSimStep k' me p q opponent a hme hle =>
      intro _hK
      rw [WV_impl, WV_plays, WV_plays]
      rintro (⟨rfl, hSP⟩ | hint)
      · subst hme; exact Or.inl ⟨rfl, h_botsimS p q opponent hSP⟩
      · exact Or.inr ((Pf_sound k' _ (Pf.botSimStep me p q opponent a hme hle)) hint)
  | botSearchStep k' g ψ a b me opponent hme hle =>
      intro _hK
      rw [WV_impl, WV_box]; intro hbox; rw [WV_plays]
      exact Or.inr ((Pf_sound k' _ (Pf.botSearchStep g ψ a b me opponent hme hle)) hbox)
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle =>
      intro _hK
      rw [WV_impl, WV_impl, WV_box]; intro hprobe hbox; rw [WV_plays]
      exact Or.inr ((Pf_sound k' _ (Pf.iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle))
        (interp_of_WV_probe h_nb hprobe) hbox)
  | searchThenSearch_t k' k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      intro _hK
      rw [WV_impl, WV_box]; intro hbox; rw [WV_plays]
      exact Or.inr ((Pf_sound k' _
        (Pf.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle)) hbox)
  | searchChain k' g₁ ψ₁ e₁ L a me opponent hme hle =>
      intro _hK
      rw [WV_impl, WV_box]; intro hbox
      exact WV_of_interp_searchChain me opponent a L
        ((Pf_sound k' _ (Pf.searchChain g₁ ψ₁ e₁ L a me opponent hme hle)) hbox)
  | ctxChain k' hd L a me opponent hme hle =>
      intro _hK
      have hI := Pf_sound k' _ (Pf.ctxChain hd L a me opponent hme hle)
      cases hd with
      | searchL g ψ e =>
          simp only [ctxGuard] at hI ⊢
          rw [WV_impl, WV_box]; intro hbox
          exact WV_of_interp_ctxChain h_nb me opponent a L (hI hbox)
      | iteL z aT other =>
          simp only [ctxGuard] at hI ⊢
          rw [WV_impl]; intro hprobe
          exact WV_of_interp_ctxChain h_nb me opponent a L
            (hI (interp_of_WV_probe h_nb hprobe))
  | searchElseChain k' hd L a me opnt hme hle =>
      intro _hK
      exact WV_of_interp_plug2 me opnt a (hd :: L)
        (Pf_sound k' _ (Pf.searchElseChain hd L a me opnt hme hle))
  | eqRefl k' p hle => intro _hK; rw [WV_eq]
  | eqNeg k' p q hne hle => intro _hK; rw [WV_neg, WV_eq]; exact hne
  | mp k' m₁ m₂ A B0 h1 h2 hle ih1 ih2 =>
      intro hK
      have i1 := ih1 (by omega); rw [WV_impl] at i1; exact i1 (ih2 (by omega))
  | implTrans k' A B0 C a b h1 h2 hle ih1 ih2 =>
      intro hK
      have i1 := ih1 (by omega); have i2 := ih2 (by omega)
      rw [WV_impl] at i1 i2 ⊢; exact fun h => i2 (i1 h)
  | weakenImpl k' A B0 m hψ hle ih =>
      intro hK; rw [WV_impl]; exact fun _ => ih (by omega)
  | impS2 A B0 C m₁ m₂ K0 h1 h2 hle ih1 ih2 =>
      intro hK
      have i1 := ih1 (by omega); have i2 := ih2 (by omega)
      rw [WV_impl] at i1 i2 ⊢; intro h; have hi := i1 h; rw [WV_impl] at hi; exact hi (i2 h)
  | implRefl k' A hle => intro _hK; rw [WV_impl]; exact id
  | implK k' A B0 hle => intro _hK; rw [WV_impl]; intro h; rw [WV_impl]; exact fun _ => h
  | implS k' A B0 C0 hle =>
      intro _hK; rw [WV_impl]; intro hf; rw [WV_impl]; intro hg; rw [WV_impl]; intro hx
      rw [WV_impl] at hf hg; have h1 := hf hx; rw [WV_impl] at h1; exact h1 (hg hx)
  | contrapose k' A B0 m h hle ih =>
      intro hK
      have i := ih (by omega); rw [WV_impl] at i
      rw [WV_impl, WV_neg, WV_neg]; exact fun hnψ hφ => hnψ (i hφ)
  | negElim k' A B0 m₁ m₂ h1 h2 hle ih1 ih2 =>
      intro hK
      have i1 := ih1 (by omega); rw [WV_neg] at i1; exact absurd (ih2 (by omega)) i1
  | boxIntro kIn K0 A hprem hle _ih => intro _hK; rw [WV_box]; exact hprem
  | atomBoxImpl k' kBox p q a hatom hle =>
      intro _hK; rw [WV_impl, WV_box]; exact fun _ => Pf.atom hatom
  | axK a b c m K0 A B0 hprem hgate hle ih =>
      intro hK
      have i := ih (by omega); rw [WV_box] at i
      rw [WV_impl, WV_box, WV_box]; exact fun hb => Pf.mp a b A B0 i hb hgate
  | axKf a b c K0 A B0 hgate hsz =>
      intro _hK; rw [WV_impl, WV_box, WV_impl, WV_box, WV_box]
      exact fun h1 hb => Pf.mp a b A B0 h1 hb hgate
  | box4 a b K0 A hgate hsz =>
      intro _hK; rw [WV_impl, WV_box, WV_box]; exact fun hp => Pf.boxIntro a b A hp hgate
  | boxMono a b K0 A hab hsz =>
      intro _hK; rw [WV_impl, WV_box, WV_box]; exact fun hp => Pf_mono hp hab
  | diagF pm fb g K0 tgt hgate hle _ih =>
      intro _hK; rw [WV_impl, WV_diag, WV_impl, WV_box]; exact fun hd => hd
  | diagB pm fb g K0 tgt hgate hle _ih =>
      intro _hK; rw [WV_impl, WV_impl, WV_box, WV_diag]; exact fun hd => hd

end PD.LlmLemmas
