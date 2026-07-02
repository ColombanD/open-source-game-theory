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
  | atomNeg p q b aN m hatom hne hle => exact Or.inl (by omega)

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

def chkEqNeg (k : Nat) : Formula → Bool
  | .neg (.eq p q) => decide (p ≠ q) && decide ((Formula.neg (.eq p q)).size ≤ k)
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
      chkHS (fun m ψ => decDeriv fuel m ψ) k φ ||
      chkEqNeg k φ

/-! ### `decDeriv` soundness -/

theorem decDeriv_sound : ∀ fuel k φ, decDeriv fuel k φ = true → DerivExists k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decDeriv] at h
  | succ f ih =>
    intro k φ h
    rw [decDeriv] at h
    simp only [Bool.or_eq_true] at h
    rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
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

    · -- eqNeg
      unfold chkEqNeg at h
      split at h
      · rename_i p q
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hne, hsz⟩ := h
        exact ⟨.eqNeg p q hne, by simpa [Derivation.size] using hsz⟩
      · simp at h

/-! ### `decDeriv` completeness -/

set_option linter.unusedSimpArgs false in
theorem decDeriv_complete : ∀ {φ : Formula} (d : Derivation φ),
    ∀ fuel K, d.size ≤ K → K ≤ fuel → decDeriv fuel K φ = true := by
  intro φ d
  induction d with
  | eqNeg p q hne =>
      intro fuel K hsz hKf
      simp only [Derivation.size] at hsz
      have h1 := Formula.size_pos (Formula.neg (.eq p q))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkEqNeg K (Formula.neg (.eq p q)) = true := by
        unfold chkEqNeg
        simp [hne, hsz]
      rw [decDeriv]
      simp only [hfire, Bool.or_true, Bool.true_or]
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
      -- CITE model (2026-07-03): the rule pays `c_guard k₂` and checks the inner premise at
      -- its literal `k₂` — the premise budget is NOT linked to `k` (this is why decider
      -- completeness is the ∃-fuel/semidecidability form).
      decide (k₁ = k₁') && decide (c0 = c0') &&
      ψ' == ψ₁.subst (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt &&
      decide (c_guard k₂ + (Formula.impl (.box k₁ ψ')
        (.plays (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt c0)).size ≤ k) &&
      rec k₂ (ψ₂.subst (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt)
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

def chkAtomNeg (O : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .neg (.plays p q aN) =>
      decide ((Formula.neg (.plays p q aN)).size ≤ k) &&
      ((O (k - (Formula.neg (.plays p q aN)).size) (.plays p q .C) && decide (aN ≠ Action.C)) ||
       (O (k - (Formula.neg (.plays p q aN)).size) (.plays p q .D) && decide (aN ≠ Action.D)))
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
      chkBoxMonoE k φ ||
      chkAtomNeg O k φ

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
    rcases h with ((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
      | h) | h) | h) | h
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
        exact Provable.searchThenSearch_t k₁ k₂ k₂ ψ₁ ψ₂ c0 c1 q _ opnt rfl
          (ih _ _ hr) (Nat.le_refl _) hsz
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

    · -- atomNeg
      unfold chkAtomNeg at h
      split at h
      · rename_i p q aN
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, hcase⟩ := h
        have hs1 := Formula.size_pos (Formula.neg (.plays p q aN))
        rcases hcase with ⟨hOr, hne⟩ | ⟨hOr, hne⟩
        · exact Provable.atomNeg p q .C aN _ (hO _ _ hOr) (fun hh => hne hh.symm) (by omega)
        · exact Provable.atomNeg p q .D aN _ (hO _ _ hOr) (fun hh => hne hh.symm) (by omega)
      · simp at h

/-! ### Fuel monotonicity — more fuel never loses a hit. -/

theorem decProv_mono (O : Nat → Formula → Bool) :
    ∀ f₁ f₂, f₁ ≤ f₂ → ∀ k φ, decProv O f₁ k φ = true → decProv O f₂ k φ = true := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ _ k φ h; simp [decProv] at h
  | succ f ih =>
    intro f₂ hle k φ h
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    have hff : f ≤ f₂' := by omega
    rw [decProv] at h
    rw [decProv]
    simp only [Bool.or_eq_true] at h ⊢
    have step : ∀ m ψ, decProv O f m ψ = true → decProv O f₂' m ψ = true :=
      fun m ψ => ih f₂' hff m ψ
    rcases h with ((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
      | h) | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))))))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))))))
    · -- chkWeaken
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))))))))
      unfold chkWeaken at h ⊢
      split at h
      · rename_i A B
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, step _ _ h.2⟩
      · simp at h
    · -- chkSTS
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Or.inl (Or.inr ?_))))))))))))
      unfold chkSTS at h ⊢
      split at h
      · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, step _ _ h.2⟩
      · simp at h
    · -- chkITrans
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Or.inr ?_)))))))))))
      unfold chkITrans at h ⊢
      split at h
      · rename_i A C
        simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
        obtain ⟨m₁, hm₁, ψ', hψ', ⟨hg, h1⟩, h2⟩ := h
        exact ⟨m₁, hm₁, ψ', hψ', ⟨hg, step _ _ h1⟩, step _ _ h2⟩
      · simp at h
    · -- chkAtomBox (oracle only)
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inr h))))))))))
    · -- chkBoxIntroE
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inr ?_)))))))))
      unfold chkBoxIntroE at h ⊢
      split at h
      · rename_i kIn ψ
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, step _ _ h.2⟩
      · simp at h
    · -- chkAppE
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))))
      unfold chkAppE at h ⊢
      simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
      obtain ⟨m₁, hm₁, ψ', hψ', ⟨hg, h1⟩, h2⟩ := h
      exact ⟨m₁, hm₁, ψ', hψ', ⟨hg, step _ _ h1⟩, step _ _ h2⟩
    · -- chkAxK
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))
      unfold chkAxK at h ⊢
      split at h
      · rename_i b ψ c α
        simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
        obtain ⟨hsz, a, ha, hg, hr⟩ := h
        exact ⟨hsz, a, ha, hg, step _ _ hr⟩
      · simp at h
    · -- chkBox4E (no rec)
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    · -- chkDiagFE
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
      unfold chkDiagFE at h ⊢
      split at h
      · rename_i g t g' g'' t' t''
        simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
        obtain ⟨hpre, fb, hfb, hr⟩ := h
        exact ⟨hpre, fb, hfb, step _ _ hr⟩
      · simp at h
    · -- chkDiagBE
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
      unfold chkDiagBE at h ⊢
      split at h
      · rename_i g g' t t' g'' t''
        simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
        obtain ⟨hpre, fb, hfb, hr⟩ := h
        exact ⟨hpre, fb, hfb, step _ _ hr⟩
      · simp at h
    · -- chkAxKfE (no rec)
      exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · -- chkImpS2E
      refine Or.inl (Or.inl (Or.inr ?_))
      unfold chkImpS2E at h ⊢
      split at h
      · rename_i A C
        simp only [List.any_eq_true, Bool.and_eq_true] at h ⊢
        obtain ⟨m₁, hm₁, ψ', hψ', ⟨hg, h1⟩, h2⟩ := h
        exact ⟨m₁, hm₁, ψ', hψ', ⟨hg, step _ _ h1⟩, step _ _ h2⟩
      · simp at h
    · -- chkBoxMonoE (no rec)
      exact Or.inl (Or.inr h)
    · -- chkAtomNeg (oracle only)
      exact Or.inr h

/-! ### `decProv` completeness — ∃-FUEL (semidecidability).

The `∀ fuel ≥ K` form died with the CITE model: `searchThenSearch_t`'s inner premise lives at
a SOURCE literal `k₂` unbounded by the conclusion's budget, so no budget-tied fuel covers it.
The honest statement — and exactly T3.2c's target — is the enumerator form: every provable
formula is FOUND at some fuel. -/

set_option linter.unusedSimpArgs false in
theorem decProv_complete (O : Nat → Formula → Bool) (hO : OracleComplete O) :
    ∀ {m φ}, Provable m φ →
      ∀ K, m ≤ K → ∃ fuel, decProv O fuel K φ = true := by
  intro m φ h
  refine Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun k φ _ => ∀ K, k ≤ K → ∃ fuel, decProv O fuel K φ = true)
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    ?cStruct ?cAtom ?cWeaken ?cSTS ?cITrans ?cAtomBox ?cBoxIntro ?cApp ?cAxK ?cBox4
    ?cDiagF ?cDiagB ?cAxKf ?cImpS2 ?cBoxMono ?cAtomNeg
    h
  case cStruct =>
      intro φ0 k0 hd K hmK
      obtain ⟨d, hsz⟩ := hd
      refine ⟨1, ?_⟩
      have hfire := decDeriv_complete d K K (by omega) le_rfl
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtom =>
      intro k0 φ0 hatom _ K hmK
      refine ⟨1, ?_⟩
      have hfire : O K _ = true := hO K _ (atom_monotone _ K _ hmK hatom)
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cWeaken =>
      intro k A B m' hψ hle ih K hmK
      have h1 := Formula.size_pos (Formula.impl A B)
      obtain ⟨f, e⟩ := ih (K - (Formula.impl A B).size) (by omega)
      refine ⟨f + 1, ?_⟩
      have hfire : chkWeaken (fun m ψ => decProv O f m ψ) K (Formula.impl A B) = true := by
        unfold chkWeaken
        have hg : (Formula.impl A B).size ≤ K := by omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cSTS =>
      intro k k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle ih K hmK
      subst hme
      obtain ⟨f, e⟩ := ih k₂ hmk
      refine ⟨f + 1, ?_⟩
      have hfire : chkSTS (fun m ψ => decProv O f m ψ) K (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)) = true := by
        unfold chkSTS
        have hg : c_guard k₂ + (Formula.impl (.box k₁ (ψ₁.subst
          (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt))
          (.plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opnt c0)).size ≤ K := by
          omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cITrans =>
      intro k A B C a b h1 h2 hle ih1 ih2 K hmK
      have hAC := Formula.size_pos (Formula.impl A C)
      have hi1 := provable_impl_size h1
      obtain ⟨f₁, e₁⟩ := ih1 a le_rfl
      obtain ⟨f₂, e₂⟩ := ih2 (K - (Formula.impl A C).size - a) (by omega)
      refine ⟨max f₁ f₂ + 1, ?_⟩
      have e₁' := decProv_mono O f₁ (max f₁ f₂) (Nat.le_max_left _ _) _ _ e₁
      have e₂' := decProv_mono O f₂ (max f₁ f₂) (Nat.le_max_right _ _) _ _ e₂
      have hfire : chkITrans (fun m ψ => decProv O (max f₁ f₂) m ψ) K
          (Formula.impl A C) = true := by
        unfold chkITrans
        simp only [List.any_eq_true, List.mem_range]
        have hBsz : B.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨a, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have hg : a + (Formula.impl A C).size ≤ K := by omega
        simp [e₁', e₂', hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtomBox =>
      intro k kBox p q a hatom hle _ K hmK
      refine ⟨1, ?_⟩
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
      intro kIn K' A hprem hle ih K hmK
      have h1 := Formula.size_pos (Formula.box kIn A)
      obtain ⟨f, e⟩ := ih kIn le_rfl
      refine ⟨f + 1, ?_⟩
      have hfire : chkBoxIntroE (fun m ψ => decProv O f m ψ) K (Formula.box kIn A) = true := by
        unfold chkBoxIntroE
        have hg : kIn + (Formula.box kIn A).size ≤ K := by omega
        simp [e, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cApp =>
      intro k' m₁ m₂ A B h1 h2 hle ih1 ih2 K hmK
      have hB := Formula.size_pos B
      have hi1 := provable_impl_size h1
      obtain ⟨f₁, e₁⟩ := ih1 m₁ le_rfl
      obtain ⟨f₂, e₂⟩ := ih2 (K - B.size - m₁) (by omega)
      refine ⟨max f₁ f₂ + 1, ?_⟩
      have e₁' := decProv_mono O f₁ (max f₁ f₂) (Nat.le_max_left _ _) _ _ e₁
      have e₂' := decProv_mono O f₂ (max f₁ f₂) (Nat.le_max_right _ _) _ _ e₂
      have hfire : chkAppE (fun m ψ => decProv O (max f₁ f₂) m ψ) K B = true := by
        unfold chkAppE
        simp only [List.any_eq_true, List.mem_range]
        have hAsz : A.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨m₁, by omega, A, (enum_complete K).2 A hAsz, ?_⟩
        have hg : m₁ + B.size ≤ K := by omega
        simp [e₁', e₂', hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAxK =>
      intro a b c m' K' A B hprem hgate hle ih K hmK
      have h1 := Formula.size_pos (Formula.impl (.box b A) (.box c B))
      obtain ⟨f, e⟩ := ih (K - (Formula.impl (.box b A) (.box c B)).size) (by omega)
      refine ⟨f + 1, ?_⟩
      have hfire : chkAxK (fun m ψ => decProv O f m ψ) K
          (Formula.impl (.box b A) (.box c B)) = true := by
        unfold chkAxK
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
        have hB := Formula.size_pos B
        exact ⟨by omega, a, by omega, by omega, e⟩
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBox4 =>
      intro a b K' A hgate hle K hmK
      refine ⟨1, ?_⟩
      have hfire : chkBox4E K (Formula.impl (.box a A) (.box b (.box a A))) = true := by
        unfold chkBox4E
        have hg : (Formula.impl (.box a A) (.box b (.box a A))).size ≤ K := by omega
        simp [hgate, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cDiagF =>
      intro pm fb g K' tgt hgate hle ih K hmK
      have h1 := Formula.size_pos (Formula.impl (.diag g tgt)
        (.impl (.box g (.diag g tgt)) tgt))
      have hgsz := provable_impl_size hgate
      obtain ⟨f, e⟩ := ih (K - (Formula.impl (.diag g tgt)
        (.impl (.box g (.diag g tgt)) tgt)).size) (by omega)
      refine ⟨f + 1, ?_⟩
      have hfire : chkDiagFE (fun m ψ => decProv O f m ψ) K
          (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)) = true := by
        unfold chkDiagFE
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_self_eq_true,
          decide_eq_true_eq, Bool.true_and, and_true, true_and]
        have hg : (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K := by
          omega
        refine ⟨hg, fb, ?_, e⟩
        refine lt_two_pow_of_log2_lt ?_
        simp only [Formula.size] at hgsz
        omega
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cDiagB =>
      intro pm fb g K' tgt hgate hle ih K hmK
      have h1 := Formula.size_pos (Formula.impl (.impl (.box g (.diag g tgt)) tgt)
        (.diag g tgt))
      have hgsz := provable_impl_size hgate
      obtain ⟨f, e⟩ := ih (K - (Formula.impl (.impl (.box g (.diag g tgt)) tgt)
        (.diag g tgt)).size) (by omega)
      refine ⟨f + 1, ?_⟩
      have hfire : chkDiagBE (fun m ψ => decProv O f m ψ) K
          (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)) = true := by
        unfold chkDiagBE
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_self_eq_true,
          decide_eq_true_eq, Bool.true_and, and_true, true_and]
        have hg : (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K := by
          omega
        refine ⟨hg, fb, ?_, e⟩
        refine lt_two_pow_of_log2_lt ?_
        simp only [Formula.size] at hgsz
        omega
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAxKf =>
      intro a b c K' A B hgate hle K hmK
      refine ⟨1, ?_⟩
      have hfire : chkAxKfE K (Formula.impl (.box a (.impl A B))
          (.impl (.box b A) (.box c B))) = true := by
        unfold chkAxKfE
        have hg : (Formula.impl (.box a (.impl A B)) (.impl (.box b A) (.box c B))).size ≤ K := by
          omega
        simp [hgate, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cImpS2 =>
      intro A B C m₁ m₂ K' h1 h2 hle ih1 ih2 K hmK
      have hAC := Formula.size_pos (Formula.impl A C)
      have hi1 := provable_impl_size h1
      obtain ⟨f₁, e₁⟩ := ih1 m₁ le_rfl
      obtain ⟨f₂, e₂⟩ := ih2 (K - (Formula.impl A C).size - m₁) (by omega)
      refine ⟨max f₁ f₂ + 1, ?_⟩
      have e₁' := decProv_mono O f₁ (max f₁ f₂) (Nat.le_max_left _ _) _ _ e₁
      have e₂' := decProv_mono O f₂ (max f₁ f₂) (Nat.le_max_right _ _) _ _ e₂
      have hfire : chkImpS2E (fun m ψ => decProv O (max f₁ f₂) m ψ) K
          (Formula.impl A C) = true := by
        unfold chkImpS2E
        simp only [List.any_eq_true, List.mem_range]
        have hBsz : B.size ≤ K := by
          simp only [Formula.size] at hi1
          omega
        refine ⟨m₁, by omega, B, (enum_complete K).2 B hBsz, ?_⟩
        have hg : m₁ + (Formula.impl A C).size ≤ K := by omega
        simp [e₁', e₂', hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cBoxMono =>
      intro a b K' A hab hle K hmK
      refine ⟨1, ?_⟩
      have hfire : chkBoxMonoE K (Formula.impl (.box a A) (.box b A)) = true := by
        unfold chkBoxMonoE
        have hg : (Formula.impl (.box a A) (.box b A)).size ≤ K := by omega
        simp [hab, hg]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]
  case cAtomNeg =>
      intro k p q b aN m' hatom hne hle _ K hmK
      have h1 := Formula.size_pos (Formula.neg (.plays p q aN))
      refine ⟨1, ?_⟩
      have hfire : chkAtomNeg O K (Formula.neg (.plays p q aN)) = true := by
        unfold chkAtomNeg
        have e : O (K - (Formula.neg (.plays p q aN)).size) (.plays p q b) = true :=
          hO _ _ (atom_monotone m' _ _ (by omega) hatom)
        have hsz : (Formula.neg (.plays p q aN)).size ≤ K := by omega
        cases b with
        | C =>
            have hne' : aN ≠ Action.C := fun hh => hne hh.symm
            simp [e, hne', hsz]
        | D =>
            have hne' : aN ≠ Action.D := fun hh => hne hh.symm
            simp [e, hne', hsz]
      rw [decProv]
      simp only [hfire, Bool.or_true, Bool.true_or]

/-! ## 6. THE PAYOFF — the engine's `Provable` is SEMIDECIDABLE relative to the atom layer.

`decProv O` is a COMPUTABLE enumerator: with a sound-and-complete atom oracle,
`Provable k φ ↔ ∃ fuel, decProv O fuel k φ = true`. Soundness holds at EVERY fuel (each hit is
a real derivation), and every derivation is found at some fuel. Full decidability — a
computable fuel bound — is open exactly at the CITED premises (`search_t`'s guards,
`searchThenSearch_t`'s inner searches, both at source literals): the T3.2c/T4 frontier. -/

theorem decProv_iff (O : Nat → Formula → Bool)
    (hOs : OracleSound O) (hOc : OracleComplete O) (k : Nat) (φ : Formula) :
    Provable k φ ↔ ∃ fuel, decProv O fuel k φ = true :=
  ⟨fun h => decProv_complete O hOc h k le_rfl,
   fun ⟨f, hf⟩ => decProv_sound O hOs f k φ hf⟩

/-! ## 7. THE ATOM SIDE — closing the knot (T3.2c part 2, milestone A).

`decCertG D` searches for a play CERTIFICATE within a cost budget, parametrically in a guard
decider `D` (consulted at `search_t`'s cited literal and for `search_f`'s refutations); the
knot is tied by plain structural recursion — `decFull (f+1) = decProv (certOG (decFull f) f)
(f+1)` — so `decFull` is a genuinely computable enumerator for the WHOLE system, atoms
included, with NO oracle hypothesis. Soundness reuses `decProv_sound` wholesale. -/

def decCertG (D : Nat → Formula → Bool) : Nat → Nat → Prog → Prog → Prog → Action → Bool
  | 0, _, _, _, _, _ => false
  | fuel+1, b, me, oppo, body, a =>
    match body with
    | .const c => decide (a = c) && decide (c_leaf ≤ b)
    | .self => decide (c_node ≤ b) && decCertG D fuel (b - c_node) me oppo me a
    | .opp => decide (c_node ≤ b) && decCertG D fuel (b - c_node) me oppo oppo a
    | .bot p => decide (c_node ≤ b) && decCertG D fuel (b - c_node) me oppo p a
    | .sim p q =>
        decide (c_node ≤ b) &&
        decCertG D fuel (b - c_node) (p.subst me oppo) (q.subst me oppo) (p.subst me oppo) a
    | .ite g a' p q =>
        decide (c_node ≤ b) &&
        ((List.range (b+1)).any fun m =>
          [Action.C, Action.D].any fun r =>
            decide (m + c_node ≤ b) &&
            decCertG D fuel m me oppo g r &&
            (if r == a' then decCertG D fuel (b - m - c_node) me oppo p a
             else decCertG D fuel (b - m - c_node) me oppo q a))
    | .search kg g p q =>
        (D kg (g.subst me oppo) && decide (c_guard kg + c_node ≤ b) &&
           decCertG D fuel (b - c_guard kg - c_node) me oppo p a)
        ||
        ((List.range (b+1)).any fun m =>
           D m (.neg (g.subst me oppo)) && decide (m + kg + c_node ≤ b) &&
           decCertG D fuel (b - m - kg - c_node) me oppo q a)

/-- The atom oracle induced by a guard decider: certificate search on plays-atoms. -/
def certOG (D : Nat → Formula → Bool) (fuel : Nat) : Nat → Formula → Bool :=
  fun k φ => match φ with
    | .plays p q a => decCertG D fuel k p q p a
    | _ => false

/-- **The knot**: the full enumerator — logic via `decProv`, atoms via the certificate
    search, each layer consulting the other one fuel lower. Computable, total. -/
def decFull : Nat → Nat → Formula → Bool
  | 0 => fun _ _ => false
  | fuel+1 => decProv (certOG (decFull fuel) fuel) (fuel+1)

/-! ### Soundness — every hit of the full enumerator is a real derivation. -/

theorem decCertG_sound (D : Nat → Formula → Bool)
    (hD : ∀ m ψ, D m ψ = true → Provable m ψ) :
    ∀ fuel b me oppo body a, decCertG D fuel b me oppo body a = true →
      ∃ n, PlaysProof me oppo body a n ∧ n ≤ b := by
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

theorem certOG_sound (D : Nat → Formula → Bool)
    (hD : ∀ m ψ, D m ψ = true → Provable m ψ) (fuel : Nat) :
    OracleSound (certOG D fuel) := by
  intro k φ h
  unfold certOG at h
  split at h
  · rename_i p q a
    obtain ⟨n, cert, hn⟩ := decCertG_sound D hD fuel k p q p a h
    exact ⟨cert, hn⟩
  · simp at h

/-- **Soundness of the full enumerator** — three lines, riding `decProv_sound`. -/
theorem decFull_sound : ∀ fuel k φ, decFull fuel k φ = true → Provable k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decFull] at h
  | succ f ih =>
    intro k φ h
    exact decProv_sound _ (certOG_sound _ (fun m ψ => ih m ψ) f) (f+1) k φ h

end PD.T31
