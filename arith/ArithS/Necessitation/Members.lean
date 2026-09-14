import ArithS.Necessitation.Layout

/-!
# ArithS.Necessitation.Members — the member list of a bit-set (`memberList`)

`M4_BOUNDED_HBL/DESIGN_fragments.md` §3.2/§8.3: a sequent is an HFS bit-set of formula codes;
the layout enumerates its members `x₁ < x₂ < … < x_k` in ASCENDING code order — `memberList s`, a
`PR` on the indices `i ≤ s` (every member of a bit-set is below the set, `lt_of_mem`), appending
`i` when `i ∈ s`. Delivered: the Σ₁ definition (`memberListAux`/`memberList`, `memberListDef` as a
substitution instance — never a DSL wrapper, `SequentLength.lean`'s note), membership both ways
(`mem_memberList_iff`, `nth_memberList_mem`), strict ascent (`memberList_sorted`, hence
`memberList_nodup`), the length bounds (`len_memberList_le`, `len_memberList_le_length` — a strictly
ascending list of values `< N` has at most `N` entries — and `len_memberList_le_setLen` for formula
sets), and **the distinctness lemma the chain's exact length rests on**: the formula lengths of the
listed members (`flenVec`, the `formulaLen` map on vectors) sum EXACTLY to `setLen s`
(`setLen_eq_listSum_memberList`; DESIGN §0 item 5: "the summands are the walked lengths of the actual
distinct members"), so `Σ bnum|xᵢ| ≤ bnum (setLen s)` is a TRUE closed sentence for the `sLemma`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open Classical

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## 1. Two list utilities: the `formulaLen` map and `listSum` over `appendV` -/

section listUtil

namespace FlenVec

noncomputable def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. ∃ l, !(formulaLenGraph LAct) l x ∧ !adjoinDef y l ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := formulaLen LAct x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, formulaLen.defined.iff]

end FlenVec

/-- `flenVec L` — the vector of the formula lengths of the entries of `L`. -/
noncomputable def flenVec (L : V) : V := FlenVec.construction.result ![] L

@[simp] lemma flenVec_nil : flenVec (0 : V) = 0 := by simp [flenVec, FlenVec.construction]
@[simp] lemma flenVec_adjoin (x L : V) : flenVec (x ∷ L) = formulaLen LAct x ∷ flenVec L := by
  simp [flenVec, FlenVec.construction]

noncomputable def flenVecDef : 𝚺₁.Semisentence 2 := FlenVec.blueprint.resultDef

instance flenVec_defined : 𝚺₁-Function₁ (flenVec : V → V) via flenVecDef := .mk
  fun v ↦ by simp [FlenVec.construction.eval_resultDef, flenVecDef]; rfl
instance flenVec_definable : 𝚺₁-Function₁ (flenVec : V → V) := flenVec_defined.to_definable

lemma flenVec_appendV : ∀ A B : V, flenVec (appendV A B) = appendV (flenVec A) (flenVec B) := by
  intro A B
  induction A using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x A ih => rw [appendV_adjoin, flenVec_adjoin, flenVec_adjoin, ih, appendV_adjoin]

lemma len_flenVec : ∀ L : V, len (flenVec L) = len L := by
  intro L
  induction L using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x L ih => rw [flenVec_adjoin, len_adjoin, len_adjoin, ih]

lemma nth_flenVec : ∀ L : V, ∀ m < len L, (flenVec L).[m] = formulaLen LAct L.[m] := by
  intro L
  induction L using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro m hm; simp at hm
  | adjoin x L ih =>
    intro m hm
    rw [flenVec_adjoin]
    rcases zero_or_succ m with rfl | ⟨m', rfl⟩
    · simp
    · rw [nth_adjoin_succ, nth_adjoin_succ]
      exact ih m' (by rw [len_adjoin] at hm; exact lt_of_add_lt_add_right hm)

lemma listSum_appendV : ∀ A B : V, listSum (appendV A B) = listSum A + listSum B := by
  intro A B
  induction A using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x A ih => rw [appendV_adjoin, listSum_adjoin, listSum_adjoin, ih, add_assoc]

/-- A list of entries `≥ 1` sums to at least its length. -/
lemma len_le_listSum_of_one_le : ∀ L : V, (∀ m < len L, 1 ≤ L.[m]) → len L ≤ listSum L := by
  intro L
  induction L using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro _; simp
  | adjoin x L ih =>
    intro h
    rw [len_adjoin, listSum_adjoin, add_comm x]
    refine add_le_add (ih fun m hm ↦ ?_) ?_
    · have := h (m + 1) (by rw [len_adjoin]; exact add_lt_add_left hm 1)
      rwa [nth_adjoin_succ] at this
    · have := h 0 (by rw [len_adjoin]; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self)
      rwa [nth_adjoin_zero] at this

end listUtil

/-! ## 2. `memberList` -/

section memberList

namespace MemberList

/-- `zero s = 0`; `succ s i ih = appendV ih ?[i]` if `i ∈ s`, else `ih`. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y s. y = 0”
  succ := .mkSigma “y ih i s. (i ∈ s → ∃ w, !adjoinDef w i 0 ∧ !appendVDef y ih w) ∧ (¬i ∈ s → y = ih)”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v i ih ↦ if i ∈ v 0 then appendV ih ?[i] else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by
    suffices
      (v 2 ∈ v 3 → v 0 = appendV (v 1) ?[v 2]) ∧ (v 2 ∉ v 3 → v 0 = v 1) ↔
      (v 0 = if v 2 ∈ v 3 then appendV (v 1) ?[v 2] else v 1) by
      simpa [blueprint, appendV_defined.iff]
    by_cases h : v 2 ∈ v 3
    · simp [h]
    · simp [h]

end MemberList

/-- The members of `s` below `i`, ascending. -/
noncomputable def memberListAux (s i : V) : V := MemberList.construction.result ![s] i

/-- **The member list of a bit-set**, ascending (every member is below the set). -/
noncomputable def memberList (s : V) : V := memberListAux s s

@[simp] lemma memberListAux_zero (s : V) : memberListAux s 0 = 0 := by
  simp [memberListAux, MemberList.construction]

lemma memberListAux_succ (s i : V) :
    memberListAux s (i + 1) = if i ∈ s then appendV (memberListAux s i) ?[i] else memberListAux s i := by
  simp [memberListAux, MemberList.construction]

lemma memberListAux_succ_of_mem {s i : V} (h : i ∈ s) :
    memberListAux s (i + 1) = appendV (memberListAux s i) ?[i] := by simp [memberListAux_succ, h]

lemma memberListAux_succ_of_not_mem {s i : V} (h : i ∉ s) :
    memberListAux s (i + 1) = memberListAux s i := by simp [memberListAux_succ, h]

noncomputable def memberListAuxDef : 𝚺₁.Semisentence 3 :=
  MemberList.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance memberListAux_defined : 𝚺₁-Function₂ (memberListAux : V → V → V) via memberListAuxDef := .mk fun v ↦ by
  simp [MemberList.construction.result_defined_iff, memberListAuxDef]; rfl

instance memberListAux_definable : 𝚺₁-Function₂ (memberListAux : V → V → V) := memberListAux_defined.to_definable

/-- `memberList` as a substitution instance of `memberListAuxDef` (not a DSL wrapper). -/
noncomputable def memberListDef : 𝚺₁.Semisentence 2 := memberListAuxDef.rew (Rew.subst ![#0, #1, #1])

instance memberList_defined : 𝚺₁-Function₁ (memberList : V → V) via memberListDef := .mk fun v ↦ by
  simp [memberListDef, memberListAuxDef, MemberList.construction.result_defined_iff, memberList]; rfl

instance memberList_definable : 𝚺₁-Function₁ (memberList : V → V) := memberList_defined.to_definable

/-! ### 2.1 Length, membership, ascent (by induction on the index) -/

lemma len_memberListAux_le (s : V) : ∀ i, len (memberListAux s i) ≤ i := by
  intro i
  induction i using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => simp
  | succ i ih =>
    rw [memberListAux_succ]
    split_ifs with h
    · rw [len_appendV, len_vec1]; exact add_le_add ih le_rfl
    · exact le_trans ih le_self_add

/-- Every entry is a member below the index. -/
lemma nth_memberListAux (s : V) :
    ∀ i, ∀ m < len (memberListAux s i), (memberListAux s i).[m] ∈ s ∧ (memberListAux s i).[m] < i := by
  intro i
  induction i using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro m hm; simp at hm
  | succ i ih =>
    intro m hm
    rw [memberListAux_succ] at hm ⊢
    split_ifs at hm ⊢ with h
    · rw [len_appendV, len_vec1] at hm
      by_cases hm' : m < len (memberListAux s i)
      · rw [nth_appendV_lt _ _ m hm']
        exact ⟨(ih m hm').1, lt_of_lt_of_le (ih m hm').2 le_self_add⟩
      · have hmeq : m = len (memberListAux s i) := le_antisymm (lt_succ_iff_le.mp hm) (not_lt.mp hm')
        have hn := nth_appendV_add (memberListAux s i) ?[i] 0
        rw [add_zero] at hn
        rw [hmeq, hn, nth_adjoin_zero]
        exact ⟨h, lt_succ_iff_le.mpr le_rfl⟩
    · exact ⟨(ih m hm).1, lt_of_lt_of_le (ih m hm).2 le_self_add⟩

/-- Every member below the index is an entry. -/
lemma mem_memberListAux (s : V) :
    ∀ i, ∀ x < i, x ∈ s → ∃ m < len (memberListAux s i), (memberListAux s i).[m] = x := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro x hx; exact absurd hx (not_lt.mpr zero_le)
  | succ i ih =>
    intro x hx hxs
    rw [memberListAux_succ]
    by_cases hxi : x < i
    · obtain ⟨m, hm, hmx⟩ := ih x hxi hxs
      split_ifs with h
      · exact ⟨m, by rw [len_appendV, len_vec1]; exact lt_of_lt_of_le hm le_self_add,
          by rw [nth_appendV_lt _ _ m hm]; exact hmx⟩
      · exact ⟨m, hm, hmx⟩
    · have hxeq : x = i := le_antisymm (lt_succ_iff_le.mp hx) (not_lt.mp hxi)
      subst hxeq
      rw [if_pos hxs]
      have hn := nth_appendV_add (memberListAux s x) ?[x] 0
      rw [add_zero] at hn
      exact ⟨len (memberListAux s x), by rw [len_appendV, len_vec1]; exact lt_succ_iff_le.mpr le_rfl,
        by rw [hn, nth_adjoin_zero]⟩

/-- The entries ascend strictly. -/
lemma memberListAux_sorted (s : V) :
    ∀ i, ∀ a < len (memberListAux s i), ∀ b < len (memberListAux s i), a < b →
      (memberListAux s i).[a] < (memberListAux s i).[b] := by
  intro i
  induction i using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro a ha; simp at ha
  | succ i ih =>
    intro a ha b hb hab
    rw [memberListAux_succ] at ha hb ⊢
    split_ifs at ha hb ⊢ with h
    · rw [len_appendV, len_vec1] at ha hb
      by_cases hb' : b < len (memberListAux s i)
      · have ha' : a < len (memberListAux s i) := lt_trans hab hb'
        rw [nth_appendV_lt _ _ a ha', nth_appendV_lt _ _ b hb']
        exact ih a ha' b hb' hab
      · have hbeq : b = len (memberListAux s i) := le_antisymm (lt_succ_iff_le.mp hb) (not_lt.mp hb')
        have ha' : a < len (memberListAux s i) := hbeq ▸ hab
        have hn := nth_appendV_add (memberListAux s i) ?[i] 0
        rw [add_zero] at hn
        rw [hbeq, hn, nth_adjoin_zero, nth_appendV_lt _ _ a ha']
        exact (nth_memberListAux s i a ha').2
    · exact ih a ha b hb hab

/-! ### 2.2 `memberList` -/

lemma nth_memberList_mem {s m : V} (hm : m < len (memberList s)) : (memberList s).[m] ∈ s :=
  (nth_memberListAux s s m hm).1

lemma mem_memberList_iff {s x : V} : (∃ m < len (memberList s), (memberList s).[m] = x) ↔ x ∈ s := by
  constructor
  · rintro ⟨m, hm, rfl⟩; exact nth_memberList_mem hm
  · intro hx; exact mem_memberListAux s s x (lt_of_mem hx) hx

lemma memberList_sorted {s a b : V} (ha : a < len (memberList s)) (hb : b < len (memberList s)) (hab : a < b) :
    (memberList s).[a] < (memberList s).[b] :=
  memberListAux_sorted s s a ha b hb hab

/-- No repeated entries. -/
lemma memberList_nodup {s a b : V} (ha : a < len (memberList s)) (hb : b < len (memberList s))
    (h : (memberList s).[a] = (memberList s).[b]) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd (memberList_sorted ha hb hab) (by rw [h]; exact _root_.lt_irrefl _)
  · exact hab
  · exact absurd (memberList_sorted hb ha hab) (by rw [h]; exact _root_.lt_irrefl _)

lemma len_memberList_le (s : V) : len (memberList s) ≤ s := len_memberListAux_le s s

/-- A strictly ascending list dominates the index: `m ≤ L.[m]`. -/
lemma le_nth_of_sorted {L : V} (hL : ∀ a < len L, ∀ b < len L, a < b → L.[a] < L.[b]) :
    ∀ m < len L, m ≤ L.[m] := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; exact zero_le
  | succ m ih =>
    intro hm
    have hm' : m < len L := lt_trans (lt_succ_iff_le.mpr le_rfl) hm
    exact lt_iff_succ_le.mp (lt_of_le_of_lt (ih hm') (hL m hm' (m + 1) hm (lt_succ_iff_le.mpr le_rfl)))

/-- At most `‖s‖` members (every member is below the bit length). -/
lemma len_memberList_le_length (s : V) : len (memberList s) ≤ ‖s‖ := by
  by_cases h0 : len (memberList s) = 0
  · rw [h0]; exact zero_le
  · obtain ⟨m, hm⟩ : ∃ m, len (memberList s) = m + 1 := by
      rcases zero_or_succ (len (memberList s)) with h | h
      · exact absurd h h0
      · exact h
    have hmlt : m < len (memberList s) := by rw [hm]; exact lt_succ_iff_le.mpr le_rfl
    have h1 : m ≤ (memberList s).[m] := le_nth_of_sorted (fun a ha b hb hab ↦ memberList_sorted ha hb hab) m hmlt
    have h2 : (memberList s).[m] < ‖s‖ := lt_length_of_mem (nth_memberList_mem hmlt)
    rw [hm]
    exact lt_iff_succ_le.mp (lt_of_le_of_lt h1 h2)

/-! ### 2.3 The exact length: `setLen s = Σ formulaLen (memberList s)` -/

lemma setLenAux_eq_listSum_flenVec (s : V) :
    ∀ i, setLenAux LAct s i = listSum (flenVec (memberListAux s i)) := by
  intro i
  induction i using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => simp
  | succ i ih =>
    rw [setLenAux_succ, memberListAux_succ]
    split_ifs with h
    · rw [flenVec_appendV, listSum_appendV, flenVec_adjoin, flenVec_nil, listSum_adjoin, listSum_nil, add_zero, ih]
    · exact ih

/-- **The distinctness lemma**: the formula lengths of the listed members sum exactly to `setLen s`. -/
theorem setLen_eq_listSum_memberList (s : V) : setLen LAct s = listSum (flenVec (memberList s)) :=
  setLenAux_eq_listSum_flenVec s s

/-- The form the chain's `sLemma` needs: the sum of the walked lengths is bounded by `setLen s`. -/
theorem listSum_flenVec_memberList_le (s : V) : listSum (flenVec (memberList s)) ≤ setLen LAct s :=
  le_of_eq (setLen_eq_listSum_memberList s).symm

/-- A formula set has at most `setLen s` members. -/
theorem len_memberList_le_setLen {s : V} (hs : IsFormulaSet LAct s) : len (memberList s) ≤ setLen LAct s := by
  rw [setLen_eq_listSum_memberList, ← len_flenVec]
  refine len_le_listSum_of_one_le _ fun m hm ↦ ?_
  rw [len_flenVec] at hm
  rw [nth_flenVec _ m hm]
  exact one_le_formulaLen_V (L := LAct) (n := 0) (hs _ (nth_memberList_mem hm))

end memberList

end ArithS
