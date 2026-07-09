import PrisonersDilemma.Decidability.T52DecInst

/-!
# Cut relevance VI — decidability at the instance gate.

T47's stabilization, re-run at `instOKb`: `decideProvableG_inst` decides
`ProvableG (instGate (players r₁ r₂) N) k₀ φ₀` with the computable fuel bound
`|SL|`, under the same hypotheses as the modest original (modest roots,
universe-resident root arguments).

T47's finite query space (`SL`/`InvP`/`ZS`) is gate-free and reused verbatim;
the new content is the instance read-classification (`enumArg_mem_inst`:
instance-gated cuts' arguments re-enter the universe — frames are self/opp,
closed raw-modest, or players), then the step congruence, the countP
stabilization, and the `Decidable` payoff, transformed mechanically from T47.
-/

namespace PD.T53
open PD PD.BaseTheorems PD.T31 PD.T42 PD.T43 PD.T44 PD.T45 PD.T46 PD.T47
open PD.T50 PD.T52

variable (r₁ r₂ : Prog) (N k₀ : Nat) (φ₀ : Formula)

/-- The canonical pool for the instance gate. -/
abbrev PP : List Prog := T43.players r₁ r₂

/-- Players live in the program universe. -/
theorem players_sub_AP : ∀ {p : Prog}, p ∈ PP r₁ r₂ → p ∈ AP r₁ r₂ N k₀ φ₀ := by
  intro p hp
  simp only [PP, T43.players, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨p, by simp [baseProgs], mem_subsP_self _⟩
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨p, by simp [baseProgs], mem_subsP_self _⟩
  · have hc := (List.mem_filter.mp hp).1
    simp only [T43.certU, List.mem_append] at hc
    simp only [AP, allowedProgs, List.mem_flatMap]
    rcases hc with hc | hc
    · exact ⟨r₁, by simp [baseProgs], hc⟩
    · exact ⟨r₂, by simp [baseProgs], hc⟩

/-- Atom args of instance-modest formulas are admissible and instance-modest. -/
theorem playsArgs_instModest (P : List Prog) : ∀ (φ : Formula),
    instModestF P φ = true →
    ∀ q ∈ playsArgsF φ, argOKP P q = true ∧ instModestP P q = true := by
  intro φ
  refine Formula.rec (motive_1 := fun _ => True)
    (motive_2 := fun φ => instModestF P φ = true →
      ∀ q ∈ playsArgsF φ, argOKP P q = true ∧ instModestP P q = true)
    ?const ?self ?opp ?bot ?sim ?ite ?search ?plays ?impl ?neg ?box ?eq ?diag φ
  case const => intro _; trivial
  case self => trivial
  case opp => trivial
  case bot => intro _ _; trivial
  case sim => intro _ _ _ _; trivial
  case ite => intro _ _ _ _ _ _ _; trivial
  case search => intro _ _ _ _ _ _ _; trivial
  case plays =>
      intro p q a _ _ h P' hP'
      simp only [instModestF, Bool.and_eq_true] at h
      simp only [playsArgsF, List.mem_cons, List.not_mem_nil, or_false] at hP'
      rcases hP' with rfl | rfl
      · exact ⟨h.1.1.1, h.1.2⟩
      · exact ⟨h.1.1.2, h.2⟩
  case impl =>
      intro φ ψ ihφ ihψ h P' hP'
      simp only [instModestF, Bool.and_eq_true] at h
      simp only [playsArgsF, List.mem_append] at hP'
      rcases hP' with hP' | hP'
      · exact ihφ h.1 P' hP'
      · exact ihψ h.2 P' hP'
  case neg => intro φ ih h P' hP'; exact ih h P' hP'
  case box => intro n φ ih h P' hP'; exact ih h P' hP'
  case eq =>
      intro p q _ _ h P' hP'
      simp [playsArgsF] at hP'
  case diag =>
      intro g φ ih h P' hP'
      simp [playsArgsF] at hP'

/-- **The instance read-classification**: every atom arg of an instance-gated enum
    formula is a universe program. -/
theorem enumArg_mem_inst {K : Nat} (hK : K ≤ RR r₁ r₂ N k₀ φ₀) {ψ' : Formula}
    (hmem : ψ' ∈ enumFormula K) (hgate : instOKb (PP r₁ r₂) N ψ' = true) :
    ∀ {q : Prog}, q ∈ playsArgsF ψ' → q ∈ AP r₁ r₂ N k₀ φ₀ := by
  intro q hq
  have hgate' := instOKb_iff.mp hgate
  obtain ⟨hargOK, hqmod⟩ := playsArgs_instModest (PP r₁ r₂) ψ' hgate'.2 q hq
  have hsubs : q ∈ subsF ψ' := playsArgsF_subset_subsF ψ' q hq
  simp only [argOKP, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hargOK
  rcases hargOK with ((rfl | rfl) | ⟨hclosed, hmodest⟩) | hmemP
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨.self, by simp [baseProgs], mem_subsP_self _⟩
  · simp only [AP, allowedProgs, List.mem_flatMap]
    exact ⟨.opp, by simp [baseProgs], mem_subsP_self _⟩
  · have hqsz : q.size ≤ SB r₁ r₂ N k₀ φ₀ := by
      have h1 := sizeF_of_mem ψ' q hsubs
      have h2 := le_EB hmem
      have h3 := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
      simp only [SB]; omega
    have hqlit : maxLitP q ≤ N := by
      have h1 := maxLitF_of_mem ψ' q hsubs
      have h2 := hgate'.1
      omega
    simp only [AP, allowedProgs, List.mem_flatMap]
    refine ⟨q, ?_, mem_subsP_self q⟩
    simp only [baseProgs, List.mem_cons]
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(enum_complete _).1 q hqsz, ⟨hclosed, hmodest⟩, hqlit⟩
  · exact players_sub_AP r₁ r₂ N k₀ φ₀ (by simpa using hmemP)

/-! ## 4. The congruence: `T52.stepG` at an in-space query reads only in-space queries. -/

/-- Cert-layer reads are answered equally by space-agreeing approximations. -/
theorem cert_reads_ok (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {S₁ S₂ : Nat → Formula → Bool}
    (hag : ∀ b ψ, b ≤ RR r₁ r₂ N k₀ φ₀ → ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b →
      InvP r₁ r₂ N k₀ φ₀ ψ → S₁ b ψ = S₂ b ψ)
    {p q : Prog} (hp : p ∈ AP r₁ r₂ N k₀ φ₀) (hq : q ∈ AP r₁ r₂ N k₀ φ₀)
    {b : Nat} (hb : b ≤ RR r₁ r₂ N k₀ φ₀) :
    ∀ m ψ, CertRead b p q p m ψ → S₁ m ψ = S₂ m ψ := by
  intro m ψ hr
  have hlp := allowedProgs_lit r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hp
  have hlq := allowedProgs_lit r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hq
  have hbud := certRead_budget r₁ r₂ N hr hlp hlq hlp
  have hLU : LU r₁ r₂ N ≤ RR r₁ r₂ N k₀ φ₀ := by
    simp only [RR, LL]; omega
  have hmR : m ≤ RR r₁ r₂ N k₀ φ₀ := by omega
  rcases certRead_mem_GF r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) h₁ h₂ hp hq hr
    with hmem | ⟨ψ₀, hψ₀, rfl⟩
  · have hGF : ψ ∈ GFall r₁ r₂ N k₀ φ₀ := List.mem_append_left _ hmem
    refine hag m ψ hmR ?_ (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ hGF)
    have := GFall_size r₁ r₂ N k₀ φ₀ hGF
    simp only [ZS]; omega
  · have hGF : Formula.neg ψ₀ ∈ GFall r₁ r₂ N k₀ φ₀ :=
      List.mem_append_right _ (List.mem_map.mpr ⟨ψ₀, hψ₀, rfl⟩)
    refine hag m _ hmR ?_ (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ hGF)
    have := GFall_size r₁ r₂ N k₀ φ₀ hGF
    simp only [ZS]; omega

set_option maxHeartbeats 4000000 in
/-- **THE CONGRUENCE**: at an in-space query, `T52.stepG` is determined by the approximation's
    values at in-space queries. -/
theorem stepG_congr (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {S₁ S₂ : Nat → Formula → Bool}
    (hag : ∀ b ψ, b ≤ RR r₁ r₂ N k₀ φ₀ → ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b →
      InvP r₁ r₂ N k₀ φ₀ ψ → S₁ b ψ = S₂ b ψ)
    {K : Nat} {φ : Formula} (hK : K ≤ RR r₁ r₂ N k₀ φ₀)
    (hsz : φ.size ≤ ZS r₁ r₂ N k₀ φ₀ K) (hInv : InvP r₁ r₂ N k₀ φ₀ φ) :
    T52.stepG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.stepG (instOKb (PP r₁ r₂) N) S₂ K φ := by
  obtain ⟨hargs, hlit⟩ := hInv
  have hN_LL : N ≤ LL r₁ r₂ N φ₀ := by simp only [LL, LU]; omega
  have hLL_RR : LL r₁ r₂ N φ₀ ≤ RR r₁ r₂ N k₀ φ₀ := by simp only [RR]; omega
  have h_cert : certOG S₁ (K+1) K φ = certOG S₂ (K+1) K φ := by
    unfold certOG
    split
    · rename_i p q a
      exact decCertG_congr (K+1) K p q p a
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag
          (hargs p (by simp [playsArgsF])) (hargs q (by simp [playsArgsF])) hK)
    · rfl
  have h_weaken : chkWeaken S₁ K φ = chkWeaken S₂ K φ := by
    unfold chkWeaken
    split
    · rename_i A B
      have hInvB : InvP r₁ r₂ N k₀ φ₀ B := by
        constructor
        · intro P hP
          exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inr hP)
        · simp only [maxLitF] at hlit; omega
      have hszB : B.size ≤ ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl A B).size) := by
        have hZ := ZS_anti r₁ r₂ N k₀ φ₀
          (show K - (Formula.impl A B).size ≤ K by omega)
        simp only [numCost, Formula.size] at hsz
        omega
      rw [hag (K - (Formula.impl A B).size) B (by omega) hszB hInvB]
    · rfl
  have h_STS : chkSTS S₁ K φ = chkSTS S₂ K φ := by
    unfold chkSTS
    split
    · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
      have hme : (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q)
          ∈ AP r₁ r₂ N k₀ φ₀ := hargs _ (by simp [playsArgsF])
      have hopnt : opnt ∈ AP r₁ r₂ N k₀ φ₀ := hargs _ (by simp [playsArgsF])
      have hinner : (Prog.search k₂ ψ₂ (.const c0') (.const c1)) ∈
          certU (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt := by
        refine List.mem_append_left _ ?_
        simp [subsP]
      have hmeP : (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) ∈
          players (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt := by
        simp only [players, List.mem_cons]
        exact Or.inl trivial
      have hopntP : opnt ∈
          players (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt := by
        simp only [players, List.mem_cons]
        exact Or.inr (Or.inl trivial)
      have hread := step_search
        (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt
        hmeP hopntP hinner
      have hGF : (ψ₂.subst (Prog.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q)
          opnt) ∈ GFall r₁ r₂ N k₀ φ₀ :=
        List.mem_append_left _
          (mem_GF r₁ r₂ N (SB r₁ r₂ N k₀ φ₀) hme hopnt hread)
      have hk₂ : k₂ ≤ RR r₁ r₂ N k₀ φ₀ := by
        simp only [maxLitF, maxLitP] at hlit
        omega
      rw [hag k₂ _ hk₂
        (by have := GFall_size r₁ r₂ N k₀ φ₀ hGF; simp only [ZS]; omega)
        (GFall_Inv r₁ r₂ N k₀ φ₀ h₁ h₂ hGF)]
    · rfl
  have h_ITrans : T52.chkITransG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.chkITransG (instOKb (PP r₁ r₂) N) S₂ K φ := by
    unfold T52.chkITransG
    split
    · rename_i A C
      apply anyCongr; intro m₁ hm₁
      apply anyCongr; intro ψ' hψ'
      have hm₁K : m₁ < K := List.mem_range.mp hm₁
      cases hc : instOKb (PP r₁ r₂) N ψ' with
      | false => simp [hc]
      | true =>
          have hψsz := le_EB hψ'
          have hEBR := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
          have hstep := ZS_step r₁ r₂ N k₀ φ₀ hm₁K hK
          have hstep2 := ZS_step r₁ r₂ N k₀ φ₀
            (show K - (Formula.impl A C).size - m₁ < K by
              have := Formula.size_pos (Formula.impl A C); omega) hK
          have hInv1 : InvP r₁ r₂ N k₀ φ₀ (.impl A ψ') := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inl hP)
              · exact enumArg_mem_inst r₁ r₂ N k₀ φ₀ hK hψ' hc hP
            · have := (instOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hInv2 : InvP r₁ r₂ N k₀ φ₀ (.impl ψ' C) := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP
              · exact enumArg_mem_inst r₁ r₂ N k₀ φ₀ hK hψ' hc hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inr hP)
            · have := (instOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hsz1 : (Formula.impl A ψ').size ≤ ZS r₁ r₂ N k₀ φ₀ m₁ := by
            simp only [numCost, Formula.size] at hsz ⊢
            omega
          have hsz2 : (Formula.impl ψ' C).size ≤
              ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl A C).size - m₁) := by
            simp only [numCost, Formula.size] at hsz hstep2 ⊢
            omega
          rw [hag m₁ _ (by omega) hsz1 hInv1,
            hag (K - (Formula.impl A C).size - m₁) _ (by omega) hsz2 hInv2]
    · rfl
  have h_AtomBox : chkAtomBox (fun m ψ => certOG S₁ (m+1) m ψ) K φ =
      chkAtomBox (fun m ψ => certOG S₂ (m+1) m ψ) K φ := by
    unfold chkAtomBox
    split
    · rename_i p q a kB p' q' a'
      have hkB : kB ≤ RR r₁ r₂ N k₀ φ₀ := by
        simp only [maxLitF, maxLitP] at hlit
        omega
      have hOG := certOG_congr (kB+1) kB
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag
          (hargs p (by simp [playsArgsF])) (hargs q (by simp [playsArgsF])) hkB)
        (a := a)
      have hOG' : (fun m ψ => certOG S₁ (m+1) m ψ) kB (Formula.plays p q a) =
          (fun m ψ => certOG S₂ (m+1) m ψ) kB (Formula.plays p q a) := hOG
      rw [hOG']
    · rfl
  have h_BoxIntro : chkBoxIntroE S₁ K φ = chkBoxIntroE S₂ K φ := by
    unfold chkBoxIntroE
    split
    · rename_i kIn ψ
      cases hg : decide (kIn + (Formula.box kIn ψ).size ≤ K) with
      | false => simp [hg]
      | true =>
          have hgle := of_decide_eq_true hg
          have hkK : kIn < K := by
            have := Formula.size_pos ψ
            simp only [numCost, Formula.size] at hgle
            omega
          have hstep := ZS_step r₁ r₂ N k₀ φ₀ hkK hK
          have hszψ : ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ kIn := by
            simp only [numCost, Formula.size] at hsz
            omega
          have hInvψ : InvP r₁ r₂ N k₀ φ₀ ψ := by
            constructor
            · intro P hP
              exact hargs P (by simp only [playsArgsF]; exact hP)
            · simp only [maxLitF] at hlit; omega
          rw [hag kIn ψ (by omega) hszψ hInvψ]
    · rfl
  have h_AppE : T52.chkAppEG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.chkAppEG (instOKb (PP r₁ r₂) N) S₂ K φ := by
    unfold T52.chkAppEG
    apply anyCongr; intro m₁ hm₁
    apply anyCongr; intro ψ' hψ'
    have hm₁K : m₁ < K := List.mem_range.mp hm₁
    cases hc : instOKb (PP r₁ r₂) N ψ' with
    | false => simp [hc]
    | true =>
        have hψsz := le_EB hψ'
        have hEBR := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
        have hstep := ZS_step r₁ r₂ N k₀ φ₀ hm₁K hK
        have hstep2 := ZS_step r₁ r₂ N k₀ φ₀
          (show K - φ.size - m₁ < K by
            have := Formula.size_pos φ; omega) hK
        have hInvC : InvP r₁ r₂ N k₀ φ₀ ψ' := by
          constructor
          · intro P hP
            exact enumArg_mem_inst r₁ r₂ N k₀ φ₀ hK hψ' hc hP
          · have := (instOKb_iff.mp hc).1
            omega
        have hInv1 : InvP r₁ r₂ N k₀ φ₀ (.impl ψ' φ) := by
          constructor
          · intro P hP
            simp only [playsArgsF, List.mem_append] at hP
            rcases hP with hP | hP
            · exact enumArg_mem_inst r₁ r₂ N k₀ φ₀ hK hψ' hc hP
            · exact hargs P hP
          · have := (instOKb_iff.mp hc).1
            simp only [maxLitF]
            omega
        have hsz1 : (Formula.impl ψ' φ).size ≤ ZS r₁ r₂ N k₀ φ₀ m₁ := by
          simp only [numCost, Formula.size]
          omega
        have hsz2 : ψ'.size ≤ ZS r₁ r₂ N k₀ φ₀ (K - φ.size - m₁) := by
          omega
        rw [hag m₁ _ (by omega) hsz1 hInv1,
          hag (K - φ.size - m₁) _ (by omega) hsz2 hInvC]
  have h_AxK : T52.chkAxKG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.chkAxKG (instOKb (PP r₁ r₂) N) S₂ K φ := by
    unfold T52.chkAxKG
    split
    · rename_i b ψ c α
      cases hgate : decide ((Formula.impl (.box b ψ) (.box c α)).size ≤ K) with
      | false => simp [hgate]
      | true =>
          have hgle := of_decide_eq_true hgate
          simp only [Bool.true_and]
          apply anyCongr; intro a ha
          cases hc : instOKb (PP r₁ r₂) N (.box a (.impl ψ α)) with
          | false => simp [hc]
          | true =>
              have hcut := instOKb_iff.mp hc
              have haN : a ≤ N := by
                have := hcut.1
                simp only [maxLitF] at this
                omega
              have hKpos : K - (Formula.impl (.box b ψ) (.box c α)).size < K := by
                have := Formula.size_pos (Formula.impl (.box b ψ) (.box c α))
                omega
              have hstep := ZS_step r₁ r₂ N k₀ φ₀ hKpos hK
              have hlog : Nat.log2 a ≤ RR r₁ r₂ N k₀ φ₀ := by
                have hl1 := log2_mono haN
                have hl2 := log2_le_self N
                omega
              have hszr : (Formula.box a (Formula.impl ψ α)).size ≤
                  ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl (.box b ψ) (.box c α)).size) := by
                simp only [numCost, Formula.size] at hsz hstep ⊢
                omega
              have hInvr : InvP r₁ r₂ N k₀ φ₀ (.box a (.impl ψ α)) := by
                constructor
                · intro P hP
                  simp only [playsArgsF, List.mem_append] at hP
                  refine hargs P ?_
                  simp only [playsArgsF, List.mem_append]
                  exact hP
                · have := hcut.1
                  simp only [maxLitF] at hlit ⊢
                  omega
              rw [hag (K - (Formula.impl (.box b ψ) (.box c α)).size) _ (by omega)
                hszr hInvr]
    · rfl
  have h_DiagF : T52.chkDiagFEG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.chkDiagFEG (instOKb (PP r₁ r₂) N) S₂ K φ := by
    unfold T52.chkDiagFEG
    split
    · rename_i g t g' g'' t' t''
      cases ht1 : (t == t') with
      | false => simp
      | true =>
          cases ht2 : (t == t'') with
          | false => simp
          | true =>
              have het1 := eq_of_beq ht1
              have het2 := eq_of_beq ht2
              subst het1
              subst het2
              cases hgate : decide ((Formula.impl (.diag g t)
                  (.impl (.box g (.diag g t)) t)).size ≤ K) with
              | false => simp
              | true =>
                  have hgle := of_decide_eq_true hgate
                  congr 1
                  apply anyCongr; intro fb hfb
                  cases hc : instOKb (PP r₁ r₂) N (.impl (.box fb t) t) with
                  | false => simp [hc]
                  | true =>
                      have hcut := instOKb_iff.mp hc
                      have hfbN : fb ≤ N := by
                        have := hcut.1
                        simp only [maxLitF] at this
                        omega
                      have hKpos : K - (Formula.impl (.diag g t)
                          (.impl (.box g (.diag g t)) t)).size < K := by
                        have := Formula.size_pos (Formula.impl (.diag g t)
                          (.impl (.box g (.diag g t)) t))
                        omega
                      have hstep := ZS_step r₁ r₂ N k₀ φ₀ hKpos hK
                      have hlog : Nat.log2 fb ≤ RR r₁ r₂ N k₀ φ₀ := by
                        have hl1 := log2_mono hfbN
                        have hl2 := log2_le_self N
                        omega
                      have hszr : (Formula.impl (.box fb t) t).size ≤
                          ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl (.diag g t)
                            (.impl (.box g (.diag g t)) t)).size) := by
                        simp only [numCost, Formula.size] at hsz hstep ⊢
                        omega
                      have hInvr : InvP r₁ r₂ N k₀ φ₀ (.impl (.box fb t) t) := by
                        constructor
                        · intro P hP
                          refine hargs P ?_
                          simp only [playsArgsF, List.mem_append, List.not_mem_nil,
                            false_or, or_false] at hP ⊢
                          rcases hP with hP | hP
                          · exact hP
                          · exact hP
                        · have := hcut.1
                          simp only [maxLitF] at hlit ⊢
                          omega
                      rw [hag (K - (Formula.impl (.diag g t)
                        (.impl (.box g (.diag g t)) t)).size) _ (by omega) hszr hInvr]
    · rfl
  have h_DiagB : T52.chkDiagBEG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.chkDiagBEG (instOKb (PP r₁ r₂) N) S₂ K φ := by
    unfold T52.chkDiagBEG
    split
    · rename_i g g' t t' g'' t''
      cases ht1 : (t == t') with
      | false => simp
      | true =>
          cases ht2 : (t == t'') with
          | false => simp
          | true =>
              have het1 := eq_of_beq ht1
              have het2 := eq_of_beq ht2
              subst het1
              subst het2
              cases hgate : decide ((Formula.impl (.impl (.box g (.diag g t)) t)
                  (.diag g t)).size ≤ K) with
              | false => simp
              | true =>
                  have hgle := of_decide_eq_true hgate
                  congr 1
                  apply anyCongr; intro fb hfb
                  cases hc : instOKb (PP r₁ r₂) N (.impl (.box fb t) t) with
                  | false => simp [hc]
                  | true =>
                      have hcut := instOKb_iff.mp hc
                      have hfbN : fb ≤ N := by
                        have := hcut.1
                        simp only [maxLitF] at this
                        omega
                      have hKpos : K - (Formula.impl (.impl (.box g (.diag g t)) t)
                          (.diag g t)).size < K := by
                        have := Formula.size_pos (Formula.impl
                          (.impl (.box g (.diag g t)) t) (.diag g t))
                        omega
                      have hstep := ZS_step r₁ r₂ N k₀ φ₀ hKpos hK
                      have hlog : Nat.log2 fb ≤ RR r₁ r₂ N k₀ φ₀ := by
                        have hl1 := log2_mono hfbN
                        have hl2 := log2_le_self N
                        omega
                      have hszr : (Formula.impl (.box fb t) t).size ≤
                          ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl
                            (.impl (.box g (.diag g t)) t) (.diag g t)).size) := by
                        simp only [numCost, Formula.size] at hsz hstep ⊢
                        omega
                      have hInvr : InvP r₁ r₂ N k₀ φ₀ (.impl (.box fb t) t) := by
                        constructor
                        · intro P hP
                          refine hargs P ?_
                          simp only [playsArgsF, List.mem_append, List.not_mem_nil,
                            false_or, or_false] at hP ⊢
                          rcases hP with hP | hP
                          · exact hP
                          · exact hP
                        · have := hcut.1
                          simp only [maxLitF] at hlit ⊢
                          omega
                      rw [hag (K - (Formula.impl (.impl (.box g (.diag g t)) t)
                        (.diag g t)).size) _ (by omega) hszr hInvr]
    · rfl
  have h_ImpS2 : T52.chkImpS2EG (instOKb (PP r₁ r₂) N) S₁ K φ = T52.chkImpS2EG (instOKb (PP r₁ r₂) N) S₂ K φ := by
    unfold T52.chkImpS2EG
    split
    · rename_i A C
      apply anyCongr; intro m₁ hm₁
      apply anyCongr; intro ψ' hψ'
      have hm₁K : m₁ < K := List.mem_range.mp hm₁
      cases hc : instOKb (PP r₁ r₂) N ψ' with
      | false => simp [hc]
      | true =>
          have hψsz := le_EB hψ'
          have hEBR := EB_le_EBR r₁ r₂ N k₀ φ₀ hK
          have hstep := ZS_step r₁ r₂ N k₀ φ₀ hm₁K hK
          have hstep2 := ZS_step r₁ r₂ N k₀ φ₀
            (show K - (Formula.impl A C).size - m₁ < K by
              have := Formula.size_pos (Formula.impl A C); omega) hK
          have hInv1 : InvP r₁ r₂ N k₀ φ₀ (.impl A (.impl ψ' C)) := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP | hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inl hP)
              · exact enumArg_mem_inst r₁ r₂ N k₀ φ₀ hK hψ' hc hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inr hP)
            · have := (instOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hInv2 : InvP r₁ r₂ N k₀ φ₀ (.impl A ψ') := by
            constructor
            · intro P hP
              simp only [playsArgsF, List.mem_append] at hP
              rcases hP with hP | hP
              · exact hargs P (by simp only [playsArgsF, List.mem_append]; exact Or.inl hP)
              · exact enumArg_mem_inst r₁ r₂ N k₀ φ₀ hK hψ' hc hP
            · have := (instOKb_iff.mp hc).1
              simp only [maxLitF] at hlit ⊢
              omega
          have hsz1 : (Formula.impl A (.impl ψ' C)).size ≤ ZS r₁ r₂ N k₀ φ₀ m₁ := by
            simp only [numCost, Formula.size] at hsz ⊢
            omega
          have hsz2 : (Formula.impl A ψ').size ≤
              ZS r₁ r₂ N k₀ φ₀ (K - (Formula.impl A C).size - m₁) := by
            simp only [numCost, Formula.size] at hsz hstep2 ⊢
            omega
          rw [hag m₁ _ (by omega) hsz1 hInv1,
            hag (K - (Formula.impl A C).size - m₁) _ (by omega) hsz2 hInv2]
    · rfl
  have h_AtomNeg : chkAtomNeg (fun m ψ => certOG S₁ (m+1) m ψ) K φ =
      chkAtomNeg (fun m ψ => certOG S₂ (m+1) m ψ) K φ := by
    unfold chkAtomNeg
    split
    · rename_i p q aN
      have hpin : p ∈ AP r₁ r₂ N k₀ φ₀ := hargs p (by simp [playsArgsF])
      have hqin : q ∈ AP r₁ r₂ N k₀ φ₀ := hargs q (by simp [playsArgsF])
      have hb : K - (Formula.neg (.plays p q aN)).size ≤ RR r₁ r₂ N k₀ φ₀ := by omega
      have hOC := certOG_congr ((K - (Formula.neg (.plays p q aN)).size) + 1)
        (K - (Formula.neg (.plays p q aN)).size)
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag hpin hqin hb) (a := Action.C)
      have hOD := certOG_congr ((K - (Formula.neg (.plays p q aN)).size) + 1)
        (K - (Formula.neg (.plays p q aN)).size)
        (cert_reads_ok r₁ r₂ N k₀ φ₀ h₁ h₂ hag hpin hqin hb) (a := Action.D)
      have hOC' : (fun m ψ => certOG S₁ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .C) =
          (fun m ψ => certOG S₂ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .C) := hOC
      have hOD' : (fun m ψ => certOG S₁ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .D) =
          (fun m ψ => certOG S₂ (m+1) m ψ)
          (K - (Formula.neg (.plays p q aN)).size) (Formula.plays p q .D) := hOD
      rw [hOC', hOD']
    · rfl
  unfold T52.stepG
  rw [h_cert, h_weaken, h_STS, h_ITrans, h_AtomBox, h_BoxIntro, h_AppE, h_AxK,
    h_DiagF, h_DiagB, h_ImpS2, h_AtomNeg]

/-! ## 5. The countP kit (T4.1a verbatim). -/

theorem countP_le {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = true → g x = true) → l.countP f ≤ l.countP g := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      rw [List.countP_cons, List.countP_cons]
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      by_cases hfa : f a = true
      · have := h a (List.mem_cons_self ..) hfa
        simp [hfa, this]; omega
      · simp only [Bool.not_eq_true] at hfa
        simp [hfa]; omega

theorem countP_lt {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = true → g x = true) →
      ∀ x ∈ l, f x = false → g x = true → l.countP f < l.countP g := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a t ih =>
      intro h x hx hfx hgx
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp hx with rfl | hxt
      · have ht := countP_le (fun y hy => h y (List.mem_cons_of_mem _ hy))
        simp [hfx, hgx]; omega
      · have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hxt hfx hgx
        by_cases hfa : f a = true
        · have := h a (List.mem_cons_self ..) hfa
          simp [hfa, this]; omega
        · simp only [Bool.not_eq_true] at hfa
          by_cases hga : g a = true <;> simp [hfa, hga] <;> omega

theorem countP_le_len {α : Type} (f : α → Bool) : ∀ l : List α, l.countP f ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.length_cons]
      by_cases hfa : f a = true
      · simp [hfa]; omega
      · simp only [Bool.not_eq_true] at hfa
        simp [hfa]; omega

/-! ## 6. Stabilization (the T4.1a template over `SL`). -/

/-- Two consecutive iterates agree on the space. -/
def Agree (n : Nat) : Prop :=
  ∀ q ∈ SL r₁ r₂ N k₀ φ₀, T52.decG (instOKb (PP r₁ r₂) N) n q.1 q.2 = T52.decG (instOKb (PP r₁ r₂) N) (n+1) q.1 q.2

theorem agree_succ (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {n : Nat} (h : Agree r₁ r₂ N k₀ φ₀ n) : Agree r₁ r₂ N k₀ φ₀ (n+1) := by
  intro q hq
  obtain ⟨b, ψ⟩ := q
  obtain ⟨hb, hsz, hInv⟩ := mem_SL_elim r₁ r₂ N k₀ φ₀ hq
  show T52.decG (instOKb (PP r₁ r₂) N) (n+1) b ψ = T52.decG (instOKb (PP r₁ r₂) N) (n+2) b ψ
  show T52.stepG (instOKb (PP r₁ r₂) N) (T52.decG (instOKb (PP r₁ r₂) N) n) b ψ = T52.stepG (instOKb (PP r₁ r₂) N) (T52.decG (instOKb (PP r₁ r₂) N) (n+1)) b ψ
  refine stepG_congr r₁ r₂ N k₀ φ₀ h₁ h₂ ?_ hb hsz hInv
  intro b' ψ' hb' hsz' hInv'
  exact h (b', ψ') (mem_SL_intro r₁ r₂ N k₀ φ₀ hb' hsz' hInv')

theorem agree_ge (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {n : Nat} (h : Agree r₁ r₂ N k₀ φ₀ n) :
    ∀ m, n ≤ m → ∀ q ∈ SL r₁ r₂ N k₀ φ₀,
      T52.decG (instOKb (PP r₁ r₂) N) m q.1 q.2 = T52.decG (instOKb (PP r₁ r₂) N) n q.1 q.2 := by
  intro m
  induction m with
  | zero =>
      intro hm q _
      have : n = 0 := by omega
      subst this; rfl
  | succ m ih =>
      intro hm q hq
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hAm : Agree r₁ r₂ N k₀ φ₀ m := by
          have haux : ∀ j, n + j ≤ m → Agree r₁ r₂ N k₀ φ₀ (n + j) := by
            intro j
            induction j with
            | zero => intro _; simpa using h
            | succ j ihj =>
                intro hj
                have := ihj (by omega)
                exact agree_succ r₁ r₂ N k₀ φ₀ h₁ h₂ this
          have hnm : n ≤ m := by omega
          have h4 := haux (m - n) (by omega)
          have heq : n + (m - n) = m := by omega
          rw [heq] at h4
          exact h4
        have e1 : T52.decG (instOKb (PP r₁ r₂) N) (m + 1) q.1 q.2 = T52.decG (instOKb (PP r₁ r₂) N) m q.1 q.2 :=
          (hAm q hq).symm
        rw [e1, ih (by omega) q hq]
      · have : n = m + 1 := by omega
        subst this; rfl

theorem exists_agree (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true) :
    ∃ n, n ≤ (SL r₁ r₂ N k₀ φ₀).length ∧ Agree r₁ r₂ N k₀ φ₀ n := by
  apply Classical.byContradiction
  intro hcon
  have hall : ∀ j, j ≤ (SL r₁ r₂ N k₀ φ₀).length → ¬ Agree r₁ r₂ N k₀ φ₀ j := by
    intro j hj hag
    exact hcon ⟨j, hj, hag⟩
  have hstrict : ∀ j, j ≤ (SL r₁ r₂ N k₀ φ₀).length →
      (SL r₁ r₂ N k₀ φ₀).countP (fun q => T52.decG (instOKb (PP r₁ r₂) N) j q.1 q.2) <
      (SL r₁ r₂ N k₀ φ₀).countP (fun q => T52.decG (instOKb (PP r₁ r₂) N) (j+1) q.1 q.2) := by
    intro j hj
    have hnag := hall j hj
    have hex : ∃ q, q ∈ SL r₁ r₂ N k₀ φ₀ ∧
        T52.decG (instOKb (PP r₁ r₂) N) j q.1 q.2 ≠ T52.decG (instOKb (PP r₁ r₂) N) (j+1) q.1 q.2 := by
      apply Classical.byContradiction
      intro hno
      exact hnag (fun q hq => Classical.byContradiction (fun hne => hno ⟨q, hq, hne⟩))
    obtain ⟨q, hq, hne⟩ := hex
    have hmono : ∀ x ∈ SL r₁ r₂ N k₀ φ₀,
        T52.decG (instOKb (PP r₁ r₂) N) j x.1 x.2 = true → T52.decG (instOKb (PP r₁ r₂) N) (j+1) x.1 x.2 = true :=
      fun x _ hx => T52.decB_mono (instOKb (PP r₁ r₂) N) j (j+1) (by omega) _ _ hx
    have hfj : T52.decG (instOKb (PP r₁ r₂) N) j q.1 q.2 = false := by
      cases hj' : T52.decG (instOKb (PP r₁ r₂) N) j q.1 q.2 with
      | false => rfl
      | true =>
          have h2 := T52.decB_mono (instOKb (PP r₁ r₂) N) j (j+1) (by omega) _ _ hj'
          rw [hj', h2] at hne
          exact absurd rfl hne
    have hgj : T52.decG (instOKb (PP r₁ r₂) N) (j+1) q.1 q.2 = true := by
      cases hj'' : T52.decG (instOKb (PP r₁ r₂) N) (j+1) q.1 q.2 with
      | true => rfl
      | false =>
          rw [hfj, hj''] at hne
          exact absurd rfl hne
    exact countP_lt hmono q hq hfj hgj
  have hge : ∀ j, j ≤ (SL r₁ r₂ N k₀ φ₀).length + 1 →
      j ≤ (SL r₁ r₂ N k₀ φ₀).countP (fun q => T52.decG (instOKb (PP r₁ r₂) N) j q.1 q.2) := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih =>
        intro hj
        have hx1 := ih (by omega)
        have hx2 := hstrict j (by omega)
        omega
  have hx1 := hge ((SL r₁ r₂ N k₀ φ₀).length + 1) (Nat.le_refl _)
  have hx2 := countP_le_len
    (fun q => T52.decG (instOKb (PP r₁ r₂) N) ((SL r₁ r₂ N k₀ φ₀).length + 1) q.1 q.2) (SL r₁ r₂ N k₀ φ₀)
  omega

/-- Any ∃-fuel hit at an in-space query is already a hit at fuel `|SL|`. -/
theorem decG_bound (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    {n b : Nat} {ψ : Formula} (hb : b ≤ RR r₁ r₂ N k₀ φ₀)
    (hsz : ψ.size ≤ ZS r₁ r₂ N k₀ φ₀ b) (hInv : InvP r₁ r₂ N k₀ φ₀ ψ)
    (h : T52.decG (instOKb (PP r₁ r₂) N) n b ψ = true) : T52.decG (instOKb (PP r₁ r₂) N) (SL r₁ r₂ N k₀ φ₀).length b ψ = true := by
  obtain ⟨j, hjle, hag⟩ := exists_agree r₁ r₂ N k₀ φ₀ h₁ h₂
  have hqmem : (b, ψ) ∈ SL r₁ r₂ N k₀ φ₀ := mem_SL_intro r₁ r₂ N k₀ φ₀ hb hsz hInv
  rcases Nat.le_total n (SL r₁ r₂ N k₀ φ₀).length with hle | hge
  · exact T52.decB_mono (instOKb (PP r₁ r₂) N) n _ hle _ _ h
  · have e1 := agree_ge r₁ r₂ N k₀ φ₀ h₁ h₂ hag n (by omega) (b, ψ) hqmem
    have e2 := agree_ge r₁ r₂ N k₀ φ₀ h₁ h₂ hag (SL r₁ r₂ N k₀ φ₀).length
      (by omega) (b, ψ) hqmem
    simp only at e1 e2
    rw [e2, ← e1]
    exact h

/-! ## 7. THE PAYOFF — the modest stratum is DECIDABLE over the zoo universe. -/

/-- **DECIDABILITY of the modest stratum**, with the computable fuel bound `|SL|`. The only
    substantive hypotheses: the roots are modest (the whole zoo is, T4.3) and the root
    formula's `.plays` arguments live in the universe (automatic for `guardU` members —
    i.e. for every bot-guard instance — via `GF_args`). -/
theorem ProvableG_inst_iff_decG_bound (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    (hargs₀ : ∀ P ∈ playsArgsF φ₀, P ∈ AP r₁ r₂ N k₀ φ₀) :
    ProvableG (instGate (PP r₁ r₂) N) k₀ φ₀ ↔
      T52.decG (instOKb (PP r₁ r₂) N) (SL r₁ r₂ N k₀ φ₀).length k₀ φ₀ = true := by
  have hk : k₀ ≤ RR r₁ r₂ N k₀ φ₀ := by simp only [RR]; omega
  have hsz : φ₀.size ≤ ZS r₁ r₂ N k₀ φ₀ k₀ := by
    simp only [ZS, Z₀]; omega
  have hInv : InvP r₁ r₂ N k₀ φ₀ φ₀ := ⟨hargs₀, by simp only [LL]; omega⟩
  constructor
  · intro h
    obtain ⟨F, hF⟩ := T52.decB_complete (instOKb (PP r₁ r₂) N) (fun _ => instOKb_iff) h k₀ (Nat.le_refl _)
    exact decG_bound r₁ r₂ N k₀ φ₀ h₁ h₂ hk hsz hInv hF
  · intro h
    exact T52.decB_sound (instOKb (PP r₁ r₂) N) (fun _ => instOKb_iff) _ k₀ φ₀ h

/-- The `Decidable` instance — bounded provability over the modest stratum is decided by
    a terminating computation. -/
def decideProvableG_inst (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true)
    (hargs₀ : ∀ P ∈ playsArgsF φ₀, P ∈ AP r₁ r₂ N k₀ φ₀) :
    Decidable (ProvableG (instGate (PP r₁ r₂) N) k₀ φ₀) :=
  if h : T52.decG (instOKb (PP r₁ r₂) N) (SL r₁ r₂ N k₀ φ₀).length k₀ φ₀ = true then
    .isTrue ((ProvableG_inst_iff_decG_bound r₁ r₂ N k₀ φ₀ h₁ h₂ hargs₀).mpr h)
  else
    .isFalse (fun hg => h ((ProvableG_inst_iff_decG_bound r₁ r₂ N k₀ φ₀ h₁ h₂ hargs₀).mp hg))


end PD.T53
