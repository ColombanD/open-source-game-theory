import PrisonersDilemma.BaseTheorems

/-!
# T3.1 spike — the ENGINE's `Provable` is decidable RELATIVE to the atom layer.

`DECIDABILITY_ROADMAP.md` T3.1. Lifts the T3.0 method (`T3DeciderMini.lean`) to the real engine:
a computable backward search `decProv` over ALL 15 `Provable` constructors — including `struct`
(its own `Derivation` backward search `decDeriv`) — parameterized by an **atom oracle**
`O : Nat → Formula → Bool` standing in for `AtomProvable` (the `PlaysProof`/eval entanglement,
T3.2's job). Headline:

  `OracleSound O   → decProv O fuel k φ = true → Provable k φ`
  `OracleComplete O → Provable k φ → decProv O k k φ = true`

so the WHOLE remaining computability question for `proofSearch` is localized into deciding
`AtomProvable` — every logical/modal/Löb rule is search-complete by the transcript accounting.

## The one refinement over T3.0: atoms are NOT size-paid

`Provable.atom`'s budget bounds the CERTIFICATE cost (eval steps), not the formula's character
size — a huge `.plays` atom can be provable at a tiny budget. So the mini's `prov_size` becomes
`provable_size_or_atom` (`φ.size ≤ k` OR the proof is an atom certificate), and the search space
stays bounded because every rule that concludes an `.impl` DOES pay it: a cut formula `φ'` in
`app`/`implTrans`/`impS2` always also occurs inside an impl-premise `Provable m (.impl φ' _)`,
whence `φ'.size < m ≤ k` (`provable_impl_size`) — cuts range over `enumFormula k` after all.
-/

namespace PD.T31
open PD PD.BaseTheorems

/-! ## 1. Numeral bound + size positivity. -/

theorem lt_two_pow_of_log2_lt {g s : Nat} (h : Nat.log2 g + 1 ≤ s) : g < 2 ^ s := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact Nat.two_pow_pos s
  · have h1 : g < 2 ^ (Nat.log2 g + 1) := by
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two g
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h)

theorem Prog.size_pos : ∀ p : Prog, 1 ≤ p.size := by
  intro p; cases p <;> simp [Prog.size]

theorem Formula.size_pos : ∀ φ : Formula, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp [Formula.size]

/-! ## 2. Enumeration — programs/formulas of size ≤ n form a computably finite set
(numerals pay `log2`, actions are finite). A SUPERSET is all the search needs. -/

mutual
  def enumProg : Nat → List Prog
    | 0 => []
    | n+1 =>
        [Prog.const .C, Prog.const .D, Prog.self, Prog.opp]
        ++ ((enumProg n).map Prog.bot)
        ++ ((enumProg n).flatMap fun p => (enumProg n).map fun q => Prog.sim p q)
        ++ ((enumProg n).flatMap fun b => [Action.C, Action.D].flatMap fun a =>
             (enumProg n).flatMap fun p => (enumProg n).map fun q => Prog.ite b a p q)
        ++ ((List.range (2 ^ (n+1))).flatMap fun k => (enumFormula n).flatMap fun φ =>
             (enumProg n).flatMap fun p => (enumProg n).map fun q => Prog.search k φ p q)

  def enumFormula : Nat → List Formula
    | 0 => []
    | n+1 =>
        ((enumProg n).flatMap fun p => (enumProg n).flatMap fun q =>
          [Action.C, Action.D].map fun a => Formula.plays p q a)
        ++ ((enumFormula n).flatMap fun φ => (enumFormula n).map fun ψ => Formula.impl φ ψ)
        ++ ((enumFormula n).map Formula.neg)
        ++ ((List.range (2 ^ (n+1))).flatMap fun k =>
             (enumFormula n).map fun φ => Formula.box k φ)
        ++ ((enumProg n).flatMap fun p => (enumProg n).map fun q => Formula.eq p q)
        ++ ((List.range (2 ^ (n+1))).flatMap fun g =>
             (enumFormula n).map fun φ => Formula.diag g φ)
end

theorem mem_action_pair (a : Action) : a ∈ [Action.C, Action.D] := by cases a <;> simp

theorem enum_complete : ∀ n : Nat,
    (∀ p : Prog, p.size ≤ n → p ∈ enumProg n) ∧
    (∀ φ : Formula, φ.size ≤ n → φ ∈ enumFormula n) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro p h; have := Prog.size_pos p; omega
      · intro φ h; have := Formula.size_pos φ; omega
  | succ n ih =>
    obtain ⟨ihP, ihF⟩ := ih
    constructor
    · intro p h
      cases p with
      | const a =>
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ ?_)))
          cases a <;> simp
      | self =>
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ ?_)))
          simp
      | opp =>
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ ?_)))
          simp
      | bot q =>
          simp only [Prog.size] at h
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ ?_)))
          exact List.mem_map.2 ⟨q, ihP q (by omega), rfl⟩
      | sim q r =>
          simp only [Prog.size] at h
          have hq := Prog.size_pos q; have hr := Prog.size_pos r
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
          exact List.mem_flatMap.2 ⟨q, ihP q (by omega),
            List.mem_map.2 ⟨r, ihP r (by omega), rfl⟩⟩
      | ite b a q r =>
          simp only [Prog.size] at h
          have hb := Prog.size_pos b; have hq := Prog.size_pos q; have hr := Prog.size_pos r
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.2 ⟨b, ihP b (by omega),
            List.mem_flatMap.2 ⟨a, mem_action_pair a,
              List.mem_flatMap.2 ⟨q, ihP q (by omega),
                List.mem_map.2 ⟨r, ihP r (by omega), rfl⟩⟩⟩⟩
      | search k φ q r =>
          simp only [Prog.size] at h
          have hφ := Formula.size_pos φ; have hq := Prog.size_pos q; have hr := Prog.size_pos r
          refine List.mem_append_right _ ?_
          exact List.mem_flatMap.2 ⟨k, List.mem_range.2 (lt_two_pow_of_log2_lt (by omega)),
            List.mem_flatMap.2 ⟨φ, ihF φ (by omega),
              List.mem_flatMap.2 ⟨q, ihP q (by omega),
                List.mem_map.2 ⟨r, ihP r (by omega), rfl⟩⟩⟩⟩
    · intro φ h
      cases φ with
      | plays q r a =>
          simp only [Formula.size] at h
          have hq := Prog.size_pos q; have hr := Prog.size_pos r
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ ?_))))
          exact List.mem_flatMap.2 ⟨q, ihP q (by omega),
            List.mem_flatMap.2 ⟨r, ihP r (by omega),
              List.mem_map.2 ⟨a, mem_action_pair a, rfl⟩⟩⟩
      | impl A B =>
          simp only [Formula.size] at h
          have hA := Formula.size_pos A; have hB := Formula.size_pos B
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ ?_))))
          exact List.mem_flatMap.2 ⟨A, ihF A (by omega),
            List.mem_map.2 ⟨B, ihF B (by omega), rfl⟩⟩
      | neg A =>
          simp only [Formula.size] at h
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ ?_)))
          exact List.mem_map.2 ⟨A, ihF A (by omega), rfl⟩
      | box k A =>
          simp only [Formula.size] at h
          have hA := Formula.size_pos A
          refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
          exact List.mem_flatMap.2 ⟨k, List.mem_range.2 (lt_two_pow_of_log2_lt (by omega)),
            List.mem_map.2 ⟨A, ihF A (by omega), rfl⟩⟩
      | eq q r =>
          simp only [Formula.size] at h
          have hq := Prog.size_pos q; have hr := Prog.size_pos r
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.2 ⟨q, ihP q (by omega),
            List.mem_map.2 ⟨r, ihP r (by omega), rfl⟩⟩
      | diag g A =>
          simp only [Formula.size] at h
          have hA := Formula.size_pos A
          refine List.mem_append_right _ ?_
          exact List.mem_flatMap.2 ⟨g, List.mem_range.2 (lt_two_pow_of_log2_lt (by omega)),
            List.mem_map.2 ⟨A, ihF A (by omega), rfl⟩⟩

/-! ## 3. Paid conclusions, atom-refined. -/

/-- Every `Provable` proof either pays its conclusion's size or IS an atom certificate
    (whose budget bounds eval-steps, not characters). -/
theorem provable_size_or_atom : ∀ {k φ}, Provable k φ → φ.size ≤ k ∨ AtomProvable k φ := by
  intro k φ h
  cases h with
  | struct hd =>
      obtain ⟨d, hsz⟩ := hd
      exact Or.inl (Nat.le_trans d.concl_size_le hsz)
  | atom hatom => exact Or.inr hatom
  | weakenImpl φ' ψ' m hψ hle => exact Or.inl (by omega)
  | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle => exact Or.inl (by omega)
  | implTrans φ' ψ' χ' a b h1 h2 hle => exact Or.inl (by omega)
  | atomBoxImpl kBox p q a hatom hle => exact Or.inl (by omega)
  | boxIntro kIn K φ' hprem hle => exact Or.inl (by omega)
  | app =>
      rename_i m₁ m₂ φ' h1 h2 hle
      exact Or.inl (by omega)
  | axK a b c m K φ' α hprem hgate hle => exact Or.inl (by omega)
  | box4 a b K φ' hgate hle => exact Or.inl (by omega)
  | diagF pm fb g K tgt hgate hle => exact Or.inl (by omega)
  | diagB pm fb g K tgt hgate hle => exact Or.inl (by omega)
  | axKf a b c K φ' α hgate hle => exact Or.inl (by omega)
  | impS2 φ' ψ' χ' m₁ m₂ K h1 h2 hle => exact Or.inl (by omega)
  | boxMono a b K φ' hab hle => exact Or.inl (by omega)

/-- Non-`.plays` conclusions ARE size-paid: `AtomProvable` only ever holds at a `.plays`. -/
theorem provable_impl_size {k : Nat} {A B : Formula}
    (h : Provable k (.impl A B)) : (Formula.impl A B).size ≤ k := by
  rcases provable_size_or_atom h with hsz | hatom
  · exact hsz
  · cases hatom

/-! ## 4. `struct` — backward search for `∃ d : Derivation φ, d.size ≤ k`.

Same method: `modusPonens`/`hypSyll` pay both subtrees + conclusion (T1's structural
`Derivation.size`), so premise budgets strictly decrease and cut formulas are size-bounded
(`Derivation.concl_size_le`); the source-transparency rules are LEAVES decided by syntactic
shape-matching (`DecidableEq` on `Prog`/`Formula`). -/

def DerivExists (k : Nat) (φ : Formula) : Prop := ∃ d : Derivation φ, d.size ≤ k

-- leaf checkers (shape + size gate; leaf transcript = conclusion size)
def chkEqRefl (k : Nat) : Formula → Bool
  | .eq p q => p == q && decide ((Formula.eq p q).size ≤ k)
  | _ => false

def chkSearchBranch (k : Nat) : Formula → Bool
  | .impl (.box k₁ ψ') (.plays (.search k₁' ψg (.const aT) (.const aE)) opnt a) =>
      decide (k₁ = k₁') && decide (a = aT) &&
      ψ' == ψg.subst (.search k₁' ψg (.const aT) (.const aE)) opnt &&
      decide ((Formula.impl (.box k₁ ψ')
        (.plays (.search k₁' ψg (.const aT) (.const aE)) opnt a)).size ≤ k)
  | _ => false

def chkSimStep (k : Nat) : Formula → Bool
  | .impl (.plays pp qq a₁) (.plays (.sim p q) opnt a₂) =>
      decide (a₁ = a₂) && pp == p.subst (.sim p q) opnt && qq == q.subst (.sim p q) opnt &&
      decide ((Formula.impl (.plays pp qq a₁) (.plays (.sim p q) opnt a₂)).size ≤ k)
  | _ => false

def chkBotSimStep (k : Nat) : Formula → Bool
  | .impl (.plays pp qq a₁) (.plays (.bot (.sim p q)) opnt a₂) =>
      decide (a₁ = a₂) && pp == p.subst (.bot (.sim p q)) opnt &&
      qq == q.subst (.bot (.sim p q)) opnt &&
      decide ((Formula.impl (.plays pp qq a₁) (.plays (.bot (.sim p q)) opnt a₂)).size ≤ k)
  | _ => false

def chkBotSearchStep (k : Nat) : Formula → Bool
  | .impl (.box k₁ ψ') (.plays (.bot (.search k₁' ψg (.const aT) (.const aE))) opnt a) =>
      decide (k₁ = k₁') && decide (a = aT) &&
      ψ' == ψg.subst (.bot (.search k₁' ψg (.const aT) (.const aE))) opnt &&
      decide ((Formula.impl (.box k₁ ψ')
        (.plays (.bot (.search k₁' ψg (.const aT) (.const aE))) opnt a)).size ≤ k)
  | _ => false

def chkIteBranchSearch (k : Nat) : Formula → Bool
  | .impl (.plays opnt1 (.bot z) a') (.impl (.box kg ψ')
      (.plays (.ite (.sim .opp (.bot z')) a'' (.search kg' ψg (.const c0) (.const c1)) q)
        opnt2 c)) =>
      z == z' && decide (a' = a'') && decide (kg = kg') && decide (c = c0) &&
      opnt1 == opnt2 &&
      ψ' == ψg.subst
        (.ite (.sim .opp (.bot z')) a'' (.search kg' ψg (.const c0) (.const c1)) q) opnt2 &&
      decide ((Formula.impl (.plays opnt1 (.bot z) a') (.impl (.box kg ψ')
        (.plays (.ite (.sim .opp (.bot z')) a'' (.search kg' ψg (.const c0) (.const c1)) q)
          opnt2 c))).size ≤ k)
  | _ => false

-- modusPonens (shape-generic; cut over enumFormula k, split point over range k)
def chkMP (rec : Nat → Formula → Bool) (k : Nat) (φ : Formula) : Bool :=
  (List.range k).any fun s₁ => (enumFormula k).any fun φ' =>
    decide (s₁ + φ.size ≤ k) && rec s₁ (.impl φ' φ) && rec (k - φ.size - s₁) φ'

def chkHS (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun s₁ => (enumFormula k).any fun ψ' =>
        decide (s₁ + (Formula.impl A C).size ≤ k) && rec s₁ (.impl A ψ') &&
        rec (k - (Formula.impl A C).size - s₁) (.impl ψ' C)
  | _ => false

def decDeriv : Nat → Nat → Formula → Bool
  | 0, _, _ => false
  | fuel+1, k, φ =>
      chkEqRefl k φ || chkSearchBranch k φ || chkSimStep k φ || chkBotSimStep k φ ||
      chkBotSearchStep k φ || chkIteBranchSearch k φ ||
      chkMP (fun m ψ => decDeriv fuel m ψ) k φ ||
      chkHS (fun m ψ => decDeriv fuel m ψ) k φ

/-! ### `decDeriv` soundness -/

theorem decDeriv_sound : ∀ fuel k φ, decDeriv fuel k φ = true → DerivExists k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decDeriv] at h
  | succ f ih =>
    intro k φ h
    rw [decDeriv] at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
    · -- eqRefl
      unfold chkEqRefl at h
      split at h
      · rename_i p q
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨rfl, hsz⟩ := h
        exact ⟨.eqRefl p, by simpa [Derivation.size] using hsz⟩
      · simp at h
    · -- searchBranch
      unfold chkSearchBranch at h
      split at h
      · rename_i k₁ ψ' k₁' ψg aT aE opnt a
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
        exact ⟨.searchBranch k₁ ψg a aE _ opnt rfl, by simpa [Derivation.size] using hsz⟩
      · simp at h
    · -- simStep
      unfold chkSimStep at h
      split at h
      · rename_i pp qq a₁ p q opnt a₂
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
        exact ⟨.simStep _ p q opnt a₁ rfl, by simpa [Derivation.size] using hsz⟩
      · simp at h
    · -- botSimStep
      unfold chkBotSimStep at h
      split at h
      · rename_i pp qq a₁ p q opnt a₂
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
        exact ⟨.botSimStep _ p q opnt a₁ rfl, by simpa [Derivation.size] using hsz⟩
      · simp at h
    · -- botSearchStep
      unfold chkBotSearchStep at h
      split at h
      · rename_i k₁ ψ' k₁' ψg aT aE opnt a
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
        exact ⟨.botSearchStep k₁ ψg a aE _ opnt rfl, by simpa [Derivation.size] using hsz⟩
      · simp at h
    · -- iteBranchSearch_t
      unfold chkIteBranchSearch at h
      split at h
      · rename_i opnt1 z a' kg ψ' z' a'' kg' ψg c0 c1 q opnt2 c
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hsz⟩ := h
        exact ⟨.iteBranchSearch_t kg z a' c c1 ψg q _ opnt1 rfl,
          by simpa [Derivation.size] using hsz⟩
      · simp at h
    · -- modusPonens
      unfold chkMP at h
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨s₁, hs₁, φ', _, ⟨hguard, h1⟩, h2⟩ := h
      obtain ⟨d1, hd1⟩ := ih s₁ _ h1
      obtain ⟨d2, hd2⟩ := ih _ _ h2
      exact ⟨.modusPonens φ' φ d1 d2, by simp only [Derivation.size]; omega⟩
    · -- hypSyll
      unfold chkHS at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨s₁, hs₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
        obtain ⟨d1, hd1⟩ := ih s₁ _ h1
        obtain ⟨d2, hd2⟩ := ih _ _ h2
        exact ⟨.hypSyll A ψ' C d1 d2, by simp only [Derivation.size]; omega⟩
      · simp at h

/-! ### `decDeriv` completeness -/

set_option linter.unusedSimpArgs false in
theorem decDeriv_complete : ∀ {φ : Formula} (d : Derivation φ),
    ∀ fuel K, d.size ≤ K → K ≤ fuel → decDeriv fuel K φ = true := by
  intro φ d
  induction d with
  | modusPonens A B d1 d2 ih1 ih2 =>
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have hB := Formula.size_pos B
      have hc1 := d1.concl_size_le
      have hd1p : 1 ≤ d1.size := Nat.le_trans (Formula.size_pos _) hc1
      have hd2p : 1 ≤ d2.size := Nat.le_trans (Formula.size_pos _) d2.concl_size_le
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hAsz : A.size ≤ K := by
        simp only [Formula.size] at hc1
        omega
      have hfire : chkMP (fun m ψ => decDeriv f m ψ) K B = true := by
        unfold chkMP
        simp only [List.any_eq_true, List.mem_range]
        refine ⟨d1.size, by omega, A, (enum_complete K).2 A hAsz, ?_⟩
        have e1 : decDeriv f d1.size (.impl A B) = true := ih1 f d1.size le_rfl (by omega)
        have e2 : decDeriv f (K - B.size - d1.size) A = true := ih2 f _ (by omega) (by omega)
        have hg : d1.size + B.size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | hypSyll A B C d1 d2 ih1 ih2 =>
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have hAC := Formula.size_pos (Formula.impl A C)
      have hc1 := d1.concl_size_le
      have hd1p : 1 ≤ d1.size := Nat.le_trans (Formula.size_pos _) hc1
      have hd2p : 1 ≤ d2.size := Nat.le_trans (Formula.size_pos _) d2.concl_size_le
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hBsz : B.size ≤ K := by
        simp only [Formula.size] at hc1
        omega
      have hfire : chkHS (fun m ψ => decDeriv f m ψ) K (Formula.impl A C) = true := by
        unfold chkHS
        simp only [List.any_eq_true, List.mem_range]
        refine ⟨d1.size, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have e1 : decDeriv f d1.size (.impl A B) = true := ih1 f d1.size le_rfl (by omega)
        have e2 : decDeriv f (K - (Formula.impl A C).size - d1.size) (.impl B C) = true :=
          ih2 f _ (by omega) (by omega)
        have hg : d1.size + (Formula.impl A C).size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | searchBranch k₁ ψg aT aE me opnt hme =>
      subst hme
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.impl (.box k₁ (ψg.subst
        (.search k₁ ψg (.const aT) (.const aE)) opnt))
        (.plays (.search k₁ ψg (.const aT) (.const aE)) opnt aT))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkSearchBranch K (Formula.impl (.box k₁ (ψg.subst
          (.search k₁ ψg (.const aT) (.const aE)) opnt))
          (.plays (.search k₁ ψg (.const aT) (.const aE)) opnt aT)) = true := by
        unfold chkSearchBranch
        simp [hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | simStep me p q opnt a hme =>
      subst hme
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.impl
        (.plays (p.subst (.sim p q) opnt) (q.subst (.sim p q) opnt) a)
        (.plays (.sim p q) opnt a))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkSimStep K (Formula.impl
          (.plays (p.subst (.sim p q) opnt) (q.subst (.sim p q) opnt) a)
          (.plays (.sim p q) opnt a)) = true := by
        unfold chkSimStep
        simp [hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | botSimStep me p q opnt a hme =>
      subst hme
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.impl
        (.plays (p.subst (.bot (.sim p q)) opnt) (q.subst (.bot (.sim p q)) opnt) a)
        (.plays (.bot (.sim p q)) opnt a))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkBotSimStep K (Formula.impl
          (.plays (p.subst (.bot (.sim p q)) opnt) (q.subst (.bot (.sim p q)) opnt) a)
          (.plays (.bot (.sim p q)) opnt a)) = true := by
        unfold chkBotSimStep
        simp [hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | botSearchStep k₁ ψg aT aE me opnt hme =>
      subst hme
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.impl (.box k₁ (ψg.subst
        (.bot (.search k₁ ψg (.const aT) (.const aE))) opnt))
        (.plays (.bot (.search k₁ ψg (.const aT) (.const aE))) opnt aT))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkBotSearchStep K (Formula.impl (.box k₁ (ψg.subst
          (.bot (.search k₁ ψg (.const aT) (.const aE))) opnt))
          (.plays (.bot (.search k₁ ψg (.const aT) (.const aE))) opnt aT)) = true := by
        unfold chkBotSearchStep
        simp [hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | iteBranchSearch_t kg z a' c0 c1 ψg q me opnt hme =>
      subst hme
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.impl (.plays opnt (.bot z) a')
        (.impl (.box kg (ψg.subst
          (.ite (.sim .opp (.bot z)) a' (.search kg ψg (.const c0) (.const c1)) q) opnt))
          (.plays (.ite (.sim .opp (.bot z)) a' (.search kg ψg (.const c0) (.const c1)) q)
            opnt c0)))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkIteBranchSearch K (Formula.impl (.plays opnt (.bot z) a')
          (.impl (.box kg (ψg.subst
            (.ite (.sim .opp (.bot z)) a' (.search kg ψg (.const c0) (.const c1)) q) opnt))
            (.plays (.ite (.sim .opp (.bot z)) a' (.search kg ψg (.const c0) (.const c1)) q)
              opnt c0))) = true := by
        unfold chkIteBranchSearch
        simp [hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | eqRefl p =>
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.eq p p)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkEqRefl K (Formula.eq p p) = true := by
        unfold chkEqRefl
        simp [hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]

/-! ## 5. The `Provable` decider — 15 rules, atom-oracle-relative. -/

/-- The stand-in for deciding `AtomProvable` (the `PlaysProof`/eval side — T3.2). -/
def OracleSound (O : Nat → Formula → Bool) : Prop :=
  ∀ k φ, O k φ = true → AtomProvable k φ
def OracleComplete (O : Nat → Formula → Bool) : Prop :=
  ∀ k φ, AtomProvable k φ → O k φ = true

def chkWeaken (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A B =>
      decide ((Formula.impl A B).size ≤ k) && rec (k - (Formula.impl A B).size) B
  | _ => false

def chkSTS (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.box k₁ ψ')
      (.plays (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt c0) =>
      decide (k₁ = k₁') && decide (c0 = c0') &&
      ψ' == ψ₁.subst (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt &&
      decide ((Formula.impl (.box k₁ ψ')
        (.plays (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt c0)).size ≤ k) &&
      rec (min k₂ (k - (Formula.impl (.box k₁ ψ')
        (.plays (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt c0)).size))
        (ψ₂.subst (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt)
  | _ => false

def chkITrans (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A ψ') &&
        rec (k - (Formula.impl A C).size - m₁) (.impl ψ' C)
  | _ => false

def chkAtomBox (O : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.plays p q a) (.box kB (.plays p' q' a')) =>
      p == p' && q == q' && decide (a = a') &&
      decide (kB + (Formula.impl (.plays p q a) (.box kB (.plays p q a))).size ≤ k) &&
      O kB (.plays p q a)
  | _ => false

def chkBoxIntroE (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .box kIn ψ => decide (kIn + (Formula.box kIn ψ).size ≤ k) && rec kIn ψ
  | _ => false

def chkAppE (rec : Nat → Formula → Bool) (k : Nat) (φ : Formula) : Bool :=
  (List.range k).any fun m₁ => (enumFormula k).any fun φ' =>
    decide (m₁ + φ.size ≤ k) && rec m₁ (.impl φ' φ) && rec (k - φ.size - m₁) φ'

def chkAxK (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.box b ψ) (.box c α) =>
      decide ((Formula.impl (.box b ψ) (.box c α)).size ≤ k) &&
      ((List.range (c+1)).any fun a =>
        decide (a + b + α.size ≤ c) &&
        rec (k - (Formula.impl (.box b ψ) (.box c α)).size) (.box a (.impl ψ α)))
  | _ => false

def chkBox4E (k : Nat) : Formula → Bool
  | .impl (.box a ψ) (.box b (.box a' ψ')) =>
      ψ == ψ' && decide (a = a') && decide (a + (Formula.box a ψ).size ≤ b) &&
      decide ((Formula.impl (.box a ψ) (.box b (.box a ψ))).size ≤ k)
  | _ => false

def chkDiagFE (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.diag g t) (.impl (.box g' (.diag g'' t')) t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        rec (k - (Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkDiagBE (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.impl (.box g (.diag g' t)) t') (.diag g'' t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        rec (k - (Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkAxKfE (k : Nat) : Formula → Bool
  | .impl (.box a (.impl ψ α)) (.impl (.box b ψ') (.box c α')) =>
      ψ == ψ' && α == α' && decide (a + b + α.size ≤ c) &&
      decide ((Formula.impl (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α))).size ≤ k)
  | _ => false

def chkImpS2E (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A (.impl ψ' C)) &&
        rec (k - (Formula.impl A C).size - m₁) (.impl A ψ')
  | _ => false

def chkBoxMonoE (k : Nat) : Formula → Bool
  | .impl (.box a ψ) (.box b ψ') =>
      ψ == ψ' && decide (a ≤ b) &&
      decide ((Formula.impl (.box a ψ) (.box b ψ)).size ≤ k)
  | _ => false

def decProv (O : Nat → Formula → Bool) : Nat → Nat → Formula → Bool
  | 0, _, _ => false
  | fuel+1, k, φ =>
      decDeriv k k φ ||
      O k φ ||
      chkWeaken (fun m ψ => decProv O fuel m ψ) k φ ||
      chkSTS (fun m ψ => decProv O fuel m ψ) k φ ||
      chkITrans (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAtomBox O k φ ||
      chkBoxIntroE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAppE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAxK (fun m ψ => decProv O fuel m ψ) k φ ||
      chkBox4E k φ ||
      chkDiagFE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkDiagBE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAxKfE k φ ||
      chkImpS2E (fun m ψ => decProv O fuel m ψ) k φ ||
      chkBoxMonoE k φ

/-! ### `decProv` soundness -/

/-- Every play certificate costs at least one character (each `PlaysProof` step pays ≥ 1). -/
theorem atomProvable_pos {k : Nat} {φ : Formula} (h : AtomProvable k φ) : 1 ≤ k := by
  obtain ⟨cert, hle⟩ := h
  cases cert <;> (simp only [c_leaf, c_node, c_guard] at hle; omega)

theorem decProv_sound (O : Nat → Formula → Bool) (hO : OracleSound O) :
    ∀ fuel k φ, decProv O fuel k φ = true → Provable k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decProv] at h
  | succ f ih =>
    intro k φ h
    rw [decProv] at h
    simp only [Bool.or_eq_true] at h
    rcases h with (((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
      | h) | h) | h
    · -- struct
      obtain ⟨d, hsz⟩ := decDeriv_sound k k φ h
      exact Provable.struct ⟨d, hsz⟩
    · -- atom
      exact Provable.atom (hO k φ h)
    · -- weakenImpl
      unfold chkWeaken at h
      split at h
      · rename_i A B
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, hr⟩ := h
        exact Provable.weakenImpl A B _ (ih _ _ hr) (by omega)
      · simp at h
    · -- searchThenSearch_t
      unfold chkSTS at h
      split at h
      · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩, hr⟩ := h
        refine Provable.searchThenSearch_t k₁ k₂ _ ψ₁ ψ₂ c0 c1 q _ opnt rfl
          (ih _ _ hr) (Nat.min_le_left _ _) ?_
        have := Nat.min_le_right k₂ (k - (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)).size)
        omega
      · simp at h
    · -- implTrans
      unfold chkITrans at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
        exact Provable.implTrans A ψ' C m₁ _ (ih _ _ h1) (ih _ _ h2) (by omega)
      · simp at h
    · -- atomBoxImpl
      unfold chkAtomBox at h
      split at h
      · rename_i p q a kB p' q' a'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hgate⟩, hOr⟩ := h
        exact Provable.atomBoxImpl kB p q a (hO _ _ hOr) hgate
      · simp at h
    · -- boxIntro
      unfold chkBoxIntroE at h
      split at h
      · rename_i kIn ψ
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hgate, hr⟩ := h
        exact Provable.boxIntro kIn k ψ (ih _ _ hr) hgate
      · simp at h
    · -- app
      unfold chkAppE at h
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨m₁, hm₁, φ', _, ⟨hguard, h1⟩, h2⟩ := h
      exact Provable.app k m₁ _ φ' φ (ih _ _ h1) (ih _ _ h2) (by omega)
    · -- axK
      unfold chkAxK at h
      split at h
      · rename_i b ψ c α
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, a, _, hgate, hr⟩ := h
        exact Provable.axK a b c _ k ψ α (ih _ _ hr) hgate (by omega)
      · simp at h
    · -- box4
      unfold chkBox4E at h
      split at h
      · rename_i a ψ b a' ψ'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hgate⟩, hsz⟩ := h
        exact Provable.box4 a b k ψ hgate hsz
      · simp at h
    · -- diagF
      unfold chkDiagFE at h
      split at h
      · rename_i g t g' g'' t' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, hr⟩ := h
        exact Provable.diagF _ fb g k t (ih _ _ hr) (by omega)
      · simp at h
    · -- diagB
      unfold chkDiagBE at h
      split at h
      · rename_i g g' t t' g'' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, hr⟩ := h
        exact Provable.diagB _ fb g k t (ih _ _ hr) (by omega)
      · simp at h
    · -- axKf
      unfold chkAxKfE at h
      split at h
      · rename_i a ψ α b ψ' c α'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hgate⟩, hsz⟩ := h
        exact Provable.axKf a b c k ψ α hgate hsz
      · simp at h
    · -- impS2
      unfold chkImpS2E at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
        exact Provable.impS2 A ψ' C m₁ _ k (ih _ _ h1) (ih _ _ h2) (by omega)
      · simp at h
    · -- boxMono
      unfold chkBoxMonoE at h
      split at h
      · rename_i a ψ b ψ'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, hab⟩, hsz⟩ := h
        exact Provable.boxMono a b k ψ hab hsz
      · simp at h

/-! ### `decProv` completeness -/

set_option linter.unusedSimpArgs false in
theorem decProv_complete (O : Nat → Formula → Bool) (hO : OracleComplete O) :
    ∀ {m φ}, Provable m φ →
      ∀ fuel K, m ≤ K → K ≤ fuel → decProv O fuel K φ = true := by
  intro m φ h
  refine Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun k φ _ => ∀ fuel K, k ≤ K → K ≤ fuel → decProv O fuel K φ = true)
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    ?cStruct ?cAtom ?cWeaken ?cSTS ?cITrans ?cAtomBox ?cBoxIntro ?cApp ?cAxK ?cBox4
    ?cDiagF ?cDiagB ?cAxKf ?cImpS2 ?cBoxMono
    h
  case cStruct =>
      intro φ0 k0 hd fuel K hmK hKf
      obtain ⟨d, hsz⟩ := hd
      have hd1 : 1 ≤ d.size := Nat.le_trans (Formula.size_pos _) d.concl_size_le
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire := decDeriv_complete d K K (by omega) le_rfl
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtom =>
      intro k0 φ0 hatom _ fuel K hmK hKf
      have h1 := atomProvable_pos hatom
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : O K _ = true := hO K _ (atom_monotone _ K _ hmK hatom)
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cWeaken =>
      intro k A B m' hψ hle ih fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl A B)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkWeaken (fun m ψ => decProv O f m ψ) K (Formula.impl A B) = true := by
        unfold chkWeaken
        have e := ih f (K - (Formula.impl A B).size) (by omega) (by omega)
        have hg : (Formula.impl A B).size ≤ K := by omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cSTS =>
      intro k k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle ih fuel K hmK hKf
      subst hme
      have h1 := Formula.size_pos (Formula.impl (.box k₁ (ψ₁.subst
        (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
        (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkSTS (fun m ψ => decProv O f m ψ) K (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)) = true := by
        unfold chkSTS
        have e := ih f (min k₂ (K - (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)).size))
          (by omega) (by
            have := Nat.min_le_right k₂ (K - (Formula.impl (.box k₁ (ψ₁.subst
              (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
              (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)).size)
            omega)
        have hg : (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)).size ≤ K := by
          omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cITrans =>
      intro k A B C a b h1 h2 hle ih1 ih2 fuel K hmK hKf
      have hAC := Formula.size_pos (Formula.impl A C)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hi1 := provable_impl_size h1
      have hA := Formula.size_pos A
      have hfire : chkITrans (fun m ψ => decProv O f m ψ) K (Formula.impl A C) = true := by
        unfold chkITrans
        simp only [List.any_eq_true, List.mem_range]
        have hBsz : B.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨a, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have e1 : decProv O f a (.impl A B) = true := ih1 f a le_rfl (by omega)
        have e2 : decProv O f (K - (Formula.impl A C).size - a) (.impl B C) = true :=
          ih2 f _ (by omega) (by omega)
        have hg : a + (Formula.impl A C).size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtomBox =>
      intro k kBox p q a hatom hle _ fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.plays p q a) (.box kBox (.plays p q a)))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkAtomBox O K
          (Formula.impl (.plays p q a) (.box kBox (.plays p q a))) = true := by
        unfold chkAtomBox
        have e := hO kBox _ hatom
        have hg : kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ K := by
          omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBoxIntro =>
      intro kIn K' A hprem hle ih fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.box kIn A)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkBoxIntroE (fun m ψ => decProv O f m ψ) K (Formula.box kIn A) = true := by
        unfold chkBoxIntroE
        have e : decProv O f kIn A = true := ih f kIn le_rfl (by omega)
        have hg : kIn + (Formula.box kIn A).size ≤ K := by omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cApp =>
      intro k' m₁ m₂ A B h1 h2 hle ih1 ih2 fuel K hmK hKf
      have hB := Formula.size_pos B
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hi1 := provable_impl_size h1
      have hfire : chkAppE (fun m ψ => decProv O f m ψ) K B = true := by
        unfold chkAppE
        simp only [List.any_eq_true, List.mem_range]
        have hAsz : A.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨m₁, by omega, A, (enum_complete K).2 A hAsz, ?_⟩
        have e1 : decProv O f m₁ (.impl A B) = true := ih1 f m₁ le_rfl (by omega)
        have e2 : decProv O f (K - B.size - m₁) A = true := ih2 f _ (by omega) (by omega)
        have hg : m₁ + B.size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAxK =>
      intro a b c m' K' A B hprem hgate hle ih fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.box b A) (.box c B))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkAxK (fun m ψ => decProv O f m ψ) K
          (Formula.impl (.box b A) (.box c B)) = true := by
        unfold chkAxK
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
        have hB := Formula.size_pos B
        refine ⟨by omega, a, by omega, by omega, ?_⟩
        exact ih f (K - (Formula.impl (.box b A) (.box c B)).size) (by omega) (by omega)
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBox4 =>
      intro a b K' A hgate hle fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.box a A) (.box b (.box a A)))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkBox4E K (Formula.impl (.box a A) (.box b (.box a A))) = true := by
        unfold chkBox4E
        have hg : (Formula.impl (.box a A) (.box b (.box a A))).size ≤ K := by omega
        simp [hgate, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cDiagF =>
      intro pm fb g K' tgt hgate hle ih fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.diag g tgt)
        (.impl (.box g (.diag g tgt)) tgt))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hgsz := provable_impl_size hgate
      have hfire : chkDiagFE (fun m ψ => decProv O f m ψ) K
          (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)) = true := by
        unfold chkDiagFE
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_self_eq_true,
          decide_eq_true_eq, Bool.true_and, and_true, true_and]
        have hg : (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K := by
          omega
        refine ⟨hg, fb, ?_, ?_⟩
        · refine lt_two_pow_of_log2_lt ?_
          simp only [Formula.size] at hgsz
          omega
        · exact ih f _ (by omega) (by omega)
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cDiagB =>
      intro pm fb g K' tgt hgate hle ih fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.impl (.box g (.diag g tgt)) tgt)
        (.diag g tgt))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hgsz := provable_impl_size hgate
      have hfire : chkDiagBE (fun m ψ => decProv O f m ψ) K
          (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)) = true := by
        unfold chkDiagBE
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_self_eq_true,
          decide_eq_true_eq, Bool.true_and, and_true, true_and]
        have hg : (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K := by
          omega
        refine ⟨hg, fb, ?_, ?_⟩
        · refine lt_two_pow_of_log2_lt ?_
          simp only [Formula.size] at hgsz
          omega
        · exact ih f _ (by omega) (by omega)
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAxKf =>
      intro a b c K' A B hgate hle fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.box a (.impl A B))
        (.impl (.box b A) (.box c B)))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkAxKfE K (Formula.impl (.box a (.impl A B))
          (.impl (.box b A) (.box c B))) = true := by
        unfold chkAxKfE
        have hg : (Formula.impl (.box a (.impl A B)) (.impl (.box b A) (.box c B))).size ≤ K := by
          omega
        simp [hgate, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cImpS2 =>
      intro A B C m₁ m₂ K' h1 h2 hle ih1 ih2 fuel K hmK hKf
      have hAC := Formula.size_pos (Formula.impl A C)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hi1 := provable_impl_size h1
      have hfire : chkImpS2E (fun m ψ => decProv O f m ψ) K (Formula.impl A C) = true := by
        unfold chkImpS2E
        simp only [List.any_eq_true, List.mem_range]
        have hBsz : B.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨m₁, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have e1 : decProv O f m₁ (.impl A (.impl B C)) = true := ih1 f m₁ le_rfl (by omega)
        have e2 : decProv O f (K - (Formula.impl A C).size - m₁) (.impl A B) = true :=
          ih2 f _ (by omega) (by omega)
        have hg : m₁ + (Formula.impl A C).size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBoxMono =>
      intro a b K' A hab hle fuel K hmK hKf
      have h1 := Formula.size_pos (Formula.impl (.box a A) (.box b A))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkBoxMonoE K (Formula.impl (.box a A) (.box b A)) = true := by
        unfold chkBoxMonoE
        have hg : (Formula.impl (.box a A) (.box b A)).size ≤ K := by omega
        simp [hab, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]

/-! ## 6. THE PAYOFF — `Provable` is decidable RELATIVE to the atom layer. -/

theorem decProv_iff (O : Nat → Formula → Bool)
    (hOs : OracleSound O) (hOc : OracleComplete O) (k : Nat) (φ : Formula) :
    decProv O k k φ = true ↔ Provable k φ :=
  ⟨decProv_sound O hOs k k φ, fun h => decProv_complete O hOc h k k le_rfl le_rfl⟩

/-- **The T3.1 headline.** Given ANY correct decision procedure for the atom layer
    (`AtomProvable` — the eval entanglement, T3.2), the engine's full `Provable` is decidable:
    every logical / modal / Löb / source-transparency rule is handled by bounded backward
    search, made finite by transcript accounting. `proofSearch := decProv O k` then makes
    `eval` computable (T4). -/
def provableRelDecidable (O : Nat → Formula → Bool)
    (hOs : OracleSound O) (hOc : OracleComplete O) (k : Nat) (φ : Formula) :
    Decidable (Provable k φ) :=
  decidable_of_iff (decProv O k k φ = true) (decProv_iff O hOs hOc k φ)

end PD.T31
