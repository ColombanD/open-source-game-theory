import ArithS.Tau.ClosedWatch

/-!
# ArithS.Cells.JustEngine — JustBot's Löb cells on the ENGINE's `JustBot`

`Cells/JustBot.lean` and `Cells/JustSlot.lean` prove JustBot's Löb cells on the hand-template twins `Just k`
(a `k`-dependent stored template) and `Just7 k` (the hand seven-variable template `guardTemplateJust7`, route
(c) by hand). Since route (c) was made generic (Phase 2c, `Agents/CodeTermAbs.lean`, `Agents/Code.lean`) the
engine's own `progCode (JustBot k)` stores a CONSTANT template too — `templateCodeAt (phiJ k) k`, the frozen
snapshot `.bot (DupocBot k)` described with its budget abstracted into the slot `#6` (`templateAt_phiJ`:
`templateAt (phiJ k) (some k) = gSnap gDu 0` for every `k`). The hand template and the engine's are different
SENTENCES, and length-bounded provability does not transfer across provably equivalent sentences, so the
argument of each twin cell is RE-RUN here on the engine's codes. This retires the twin-named cells
`outcome_Just_vs_MirrorBot`, `outcome_Just7_vs_Dupoc`, `outcome_Just7_vs_Just7`, `outcome_CIMCIC_vs_Just7`,
`outcome_DIMCID_vs_Just7` of `Outcome/Matrix/` in favour of `outcome_JustBot_vs_MirrorBot`,
`outcome_JustBot_vs_DupocBot`, `outcome_JustBot_vs_JustBot`, `outcome_CIMCIC_vs_JustBot`,
`outcome_DIMCID_vs_JustBot`. The twin theorems themselves are untouched.

What is reused and what is new:

* **Reused**: the `Describes` layer (`Cells/Common/Templates.lean`: `describes_SV`, `describes_botSV`), the simple
  members `SM` and the thirteen-slot instance equation `guardCodeB_plain_eq_instB` of the tau layer
  (`Tau/Entangled/Tower.lean`, `Tau/Watch.lean`, `Tau/Stored.lean`: the stored description of the bot-wrapped
  engine searcher is the constant `DfixSV`, `closedDescAt_botSV`, and denotes `pBot (SV g a k)` in every model,
  `absVal_botSV`), the search clauses `SV_then_V`/`botSV_then_V`, `family_found` at `boundedInnerNec_sixteen`,
  `dimcid_vs_described`.
* **New, generic** (§0–§4): a conjunction family over a LIST of guards (`conjL`, `loebSound_pL_above`,
  `boxes_pL_nat`: slack `(7 n, 8 n)` for `n` guards), the description of an UNWRAPPED simple member
  (`SM.describes`, `SM.then_V`), the stored template `gSnap g a` of "the opponent plays `a` against the frozen
  `pBot (SV g a ·)`" with its truth equation in every model (`eval_gSnap`) and its transposition
  (`lMap_swap_gSnap`), and a WORLD (`World`): the five players of a cell — Just, the frozen snapshot, Dupoc,
  CIMCIC, Mirror — as described players (`DP`), in the standard world `worldC` (the engine's bots) and in its
  transposition `worldD` (Cupod's side). Every cell's semantic core is proved ONCE, for an arbitrary world, and
  instantiated at both (`loebSound_world`): the swapped reading of a family is the standard reading of the
  transposed world's family.
* **One difference from the twins**: the hand template `guardTemplateJust7` made Just's guard against `opp`
  LITERALLY Dupoc's guard in the frame `(pBot (Dupoc k), opp)` (`guardCodeB_guardTemplateJust7`), so the twin
  families used one box for both. On the engine's templates the two sentences are different codes (the general
  thirteen-variable `templateAt` against the six-variable `template`), so each family carries the snapshot's own
  guard as a separate conjunct: Just × Mirror 2 guards, Just × Just 3, Just × Dupoc 4, CIMCIC × Just 4 (each with
  its transposition).

The cells (§5–§9), all for all large `k`, unconditional, three standard axioms: **`loeb_JustBot_vs_MirrorBot`**
`(C, C)`, **`loeb_JustBot_vs_JustBot`** `(C, C)`, **`loeb_JustBot_vs_DupocBot`** `(C, C)`,
**`loeb_CIMCIC_vs_JustBot`** `(C, C)` — each with its box form `_guard`/`_guards` on the engine's consulted
sentence `guardCode (templateCode (phiJ k)) …` — and **`loeb_DIMCID_vs_JustBot_engine`** `(D, D)`, the flip
(`dimcid_vs_described` on the engine JustBot's own description; the bare name `loeb_DIMCID_vs_JustBot` is the
twin theorem's, on `Just7 k`).

Conventions (`Research/Notes/ARITH_TRAPS.md`): every threshold EXISTENTIAL; `simp` never sees a closed quote;
`omega` is never asked about `V`; at `V = ℕ` the V-generic `≤` is bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots
open ArithS.Tau

/-! ### 0. A conjunction family over a list of guards -/

section listFamily

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The right-nested conjunction `q ⋏ (r₁ ⋏ (… ⋏ rₙ))` of a nonempty list of one-variable sentences. -/
noncomputable def conjL : Semisentence LAct 1 → List (Semisentence LAct 1) → Semisentence LAct 1
  | q, [] => q
  | q, r :: rs => q ⋏ conjL r rs

lemma conjL_nil (q : Semisentence LAct 1) : conjL q [] = q := rfl
lemma conjL_cons (q r : Semisentence LAct 1) (rs : List (Semisentence LAct 1)) :
    conjL q (r :: rs) = q ⋏ conjL r rs := rfl

lemma lMap_swap_conjL : ∀ (rs : List (Semisentence LAct 1)) (q : Semisentence LAct 1),
    Semiformula.lMap swap (conjL q rs) = conjL (Semiformula.lMap swap q) (rs.map (Semiformula.lMap swap))
  | [], _ => rfl
  | r :: rs, q => by
    rw [conjL_cons, List.map_cons, conjL_cons, lMap_swap_and, lMap_swap_conjL rs r]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- A conjunction family holds iff every conjunct does. -/
lemma eval_conjL {s : Structure LAct V} (k : V) : ∀ (rs : List (Semisentence LAct 1)) (q : Semisentence LAct 1),
    Semiformula.Eval (s := s) ![k] Empty.elim (conjL q rs) ↔
      ∀ r ∈ q :: rs, Semiformula.Eval (s := s) ![k] Empty.elim r
  | [], q => by
    rw [conjL_nil, List.forall_mem_cons]
    exact ⟨fun h ↦ ⟨h, fun _ hr ↦ absurd hr (List.not_mem_nil)⟩, fun h ↦ h.1⟩
  | r :: rs, q => by
    rw [conjL_cons, List.forall_mem_cons, ← eval_conjL k rs r]
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]

/-- **Every conjunct from a box of the conjunction**, at the budget `a + n (8 z + 7)` (`n` the number of
eliminations, `z` any bound on the family's length): `boxes_of_and`, iterated. -/
theorem boxes_conjL : ∀ (rs : List (Semisentence LAct 1)) (q : Semisentence LAct 1) (k a z : V),
    formulaLen LAct (instB (⌜conjL q rs⌝ : V) k) ≤ z →
    LenBoxUnbounded TAct a (instB (⌜conjL q rs⌝ : V) k) →
    ∀ r ∈ q :: rs, LenBoxUnbounded TAct (a + (rs.length : V) * (8 * z + 7)) (instB (⌜r⌝ : V) k)
  | [], q, k, a, z, _, h => by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    rw [List.length_nil, Nat.cast_zero, zero_mul, add_zero]
    exact h
  | r' :: rs, q, k, a, z, hz, h => by
    rw [conjL_cons] at hz h
    have hsum : formulaLen LAct (instB (⌜q⌝ : V) k) + formulaLen LAct (instB (⌜conjL r' rs⌝ : V) k) ≤ z :=
      le_trans (len_le_of_and_left q (conjL r' rs) k) hz
    obtain ⟨h₁, h₂⟩ := boxes_of_and q (conjL r' rs) k a z hsum h
    have hrest : formulaLen LAct (instB (⌜conjL r' rs⌝ : V) k) ≤ z := le_trans le_add_self hsum
    have ih := boxes_conjL rs r' k (a + 8 * z + 7) z hrest h₂
    have e : a + 8 * z + 7 + (rs.length : V) * (8 * z + 7) = a + ((r' :: rs).length : V) * (8 * z + 7) := by
      rw [List.length_cons]; push_cast; ring
    intro r hr
    rcases List.mem_cons.mp hr with hrq | hr
    · subst hrq
      refine lenBoxUnbounded_mono_V ?_ h₁
      rw [← e]; exact le_self_add
    · rw [← e]; exact ih r hr

/-- **Every conjunct of `pQ (conjL q rs)` and its transposition from a box of the family**, at the budget
`a + (n + 1)(8 z + 7)`. -/
theorem boxes_pL (q : Semisentence LAct 1) (rs : List (Semisentence LAct 1)) (k a z : V)
    (hz : formulaLen LAct (instB (⌜pQ (conjL q rs)⌝ : V) k) ≤ z)
    (h : LenBoxUnbounded TAct a (instB (⌜pQ (conjL q rs)⌝ : V) k)) :
    ∀ r ∈ q :: rs,
      LenBoxUnbounded TAct (a + ((rs.length + 1 : ℕ) : V) * (8 * z + 7)) (instB (⌜r⌝ : V) k) ∧
      LenBoxUnbounded TAct (a + ((rs.length + 1 : ℕ) : V) * (8 * z + 7)) (instB (⌜Semiformula.lMap swap r⌝ : V) k) := by
  rw [pQ_def] at hz h
  have hsum := le_trans (len_le_of_and_left (conjL q rs) (Semiformula.lMap swap (conjL q rs)) k) hz
  obtain ⟨h₁, h₂⟩ := boxes_of_and _ _ k a z hsum h
  have hl : formulaLen LAct (instB (⌜conjL q rs⌝ : V) k) ≤ z := le_trans le_self_add hsum
  have hr' : formulaLen LAct (instB (⌜Semiformula.lMap swap (conjL q rs)⌝ : V) k) ≤ z := le_trans le_add_self hsum
  rw [lMap_swap_conjL] at h₂ hr'
  have b₁ := boxes_conjL rs q k _ z hl h₁
  have b₂ := boxes_conjL (rs.map (Semiformula.lMap swap)) (Semiformula.lMap swap q) k _ z hr' h₂
  have e : a + 8 * z + 7 + (rs.length : V) * (8 * z + 7) = a + ((rs.length + 1 : ℕ) : V) * (8 * z + 7) := by
    push_cast; ring
  intro r hr
  refine ⟨?_, ?_⟩
  · rw [← e]; exact b₁ r hr
  · rw [← e]
    have hm : Semiformula.lMap swap r ∈ Semiformula.lMap swap q :: rs.map (Semiformula.lMap swap) := by
      rw [← List.map_cons]; exact List.mem_map.mpr ⟨r, hr, rfl⟩
    have := b₂ (Semiformula.lMap swap r) hm
    rwa [List.length_map] at this

/-- The slack `(7 (n + 1), 8 (n + 1))` covers the `n + 1` eliminations. -/
lemma slack_pL (n : ℕ) (a z : V) :
    a + ((n + 1 : ℕ) : V) * (8 * z + 7) ≤ a + ((7 * (n + 1) : ℕ) : V) + ((8 * (n + 1) : ℕ) : V) * z := by
  push_cast
  exact le_of_eq (by ring)

/-- **The Löb premise of a list family at slack `(7 (n + 1) + K, 8 (n + 1))`, from one semantic fact above `K`**:
all the instances (and their transpositions) provable within `k` make all of them true in the standard
reading. -/
theorem loebSound_pL_above (q : Semisentence LAct 1) (rs : List (Semisentence LAct 1)) (K : ℕ)
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      (∀ r ∈ q :: rs, LenBox TAct k (instB (⌜r⌝ : V) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : V) k)) →
      ∀ r ∈ q :: rs, Semiformula.Eval (s := stdReading V) ![k] Empty.elim r ∧
        Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap r)) :
    LoebSound (pQ (conjL q rs)) (7 * (rs.length + 1) + K) (8 * (rs.length + 1)) := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk : (K : V) ≤ k :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_left K (7 * (rs.length + 1)))) (le_trans le_add_self (le_trans le_self_add ha))
  have hb := boxes_pL q rs k a _ le_rfl hp
  have hle : a + ((rs.length + 1 : ℕ) : V) * (8 * formulaLen LAct (instB (⌜pQ (conjL q rs)⌝ : V) k) + 7) ≤ k := by
    refine le_trans (le_trans (slack_pL rs.length a _) ?_) ha
    refine add_le_add (add_le_add le_rfl (Nat.cast_le.mpr (Nat.le_add_right _ K))) le_rfl
  have hbox : ∀ r ∈ q :: rs, LenBox TAct k (instB (⌜r⌝ : V) k) ∧
      LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : V) k) :=
    fun r hr ↦ ⟨(lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle (hb r hr).1),
      (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle (hb r hr).2)⟩
  have ht := h V k hk hbox
  have hsw : ∀ r' ∈ Semiformula.lMap swap q :: rs.map (Semiformula.lMap swap),
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim r' := by
    intro r' hr'
    rw [← List.map_cons] at hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    exact (ht r hr).2
  constructor
  · rw [eval_pQ_std, lMap_swap_conjL, eval_conjL, eval_conjL]
    exact ⟨fun r hr ↦ (ht r hr).1, hsw⟩
  · rw [eval_pQ_swap, lMap_swap_conjL, eval_conjL, eval_conjL]
    exact ⟨hsw, fun r hr ↦ (ht r hr).1⟩

/-- **At ℕ: every box of a list family from `family_found`'s witness.** -/
theorem boxes_pL_nat (q : Semisentence LAct 1) (rs : List (Semisentence LAct 1)) (K k a : ℕ)
    (ha : a + (7 * (rs.length + 1) + K) + 8 * (rs.length + 1) * formulaLen LAct (instB (⌜pQ (conjL q rs)⌝ : ℕ) k) ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pQ (conjL q rs)⌝ : ℕ) k)) :
    ∀ r ∈ q :: rs, LenBox TAct k (instB (⌜r⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap r⌝ : ℕ) k) := by
  have hb := boxes_pL (V := ℕ) q rs k a (formulaLen LAct (instB (⌜pQ (conjL q rs)⌝ : ℕ) k)) (le_def.mpr (Or.inl rfl)) h
  have h' : a + 7 * (rs.length + 1) + 8 * (rs.length + 1) * formulaLen LAct (instB (⌜pQ (conjL q rs)⌝ : ℕ) k) ≤ k :=
    le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_add_right _ K) a) _) ha
  have hz := slack_pL (V := ℕ) rs.length a (formulaLen LAct (instB (⌜pQ (conjL q rs)⌝ : ℕ) k))
  simp only [natCast_nat] at hz hb
  have hle := le_def.mpr (le_def_trans (le_def.mp hz) (Nat.eq_or_lt_of_le h'))
  exact fun r hr ↦ ⟨(lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle (hb r hr).1),
    (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle (hb r hr).2)⟩

end listFamily

/-! ### 1. The description of an unwrapped simple member, and its search clauses -/

namespace Tau.SM

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The frame tower of the member `s.code k` itself** (`SM.TB` is the tower of its bot-wrapping). -/
noncomputable def TU (s : SM) : Semiterm LAct Empty 1 := Semiterm.lMap emb s.can.T1

lemma lMap_swap_TU (s : SM) : Semiterm.lMap swap s.TU = s.TU := term_lMap_swap_emb _

theorem val_TU_V (s : SM) (k : V) : s.TU.val (s := stdReadingV V) ![k] Empty.elim = canonical (s.code k) := by
  unfold TU
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_T1_V, canonical_code]

theorem hX_TU (s : SM) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb s.TU : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (s.code k)) := by
  unfold TU
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_T1, canonical_code]

theorem descVal_TU (s : SM) (k : V) : descVal s.TU s.uT s.wT k = s.code k := by
  rw [descVal_def, val_TU_V, canonical_code, revalue_val_uT_wT]

theorem descVal_TU_T (s : SM) (k : V) :
    descVal (Semiterm.lMap swap s.TU) (Semiterm.lMap swap s.uT) (Semiterm.lMap swap s.wT) k = s.tr.code k := by
  rw [descVal_def, lMap_swap_TU, val_TU_V, canonical_code, revalue_val_uT_wT_swap]

/-- **The frame tower describes the simple member in every model.** -/
theorem describes (s : SM) : Describes s.TU s.uT s.wT where
  hX := fun V _ _ k ↦ by rw [descVal_TU]; exact hX_TU s k
  hU := fun V _ _ k ↦ by rw [descVal_TU, revalueU_code]
  hW := fun V _ _ k ↦ by rw [descVal_TU, revalueW_code]
  hT := fun V _ _ k ↦ by rw [descVal_TU_T, descVal_TU, transposeCode_code]

/-- The transposed description of a simple member. -/
theorem describesT (s : SM) :
    Describes (Semiterm.lMap swap s.TU) (Semiterm.lMap swap s.uT) (Semiterm.lMap swap s.wT) where
  hX := fun V _ _ k ↦ by
    rw [descVal_TU_T, lMap_swap_TU, canonical_tr_code, ← canonical_code]
    exact hX_TU s k
  hU := fun V _ _ k ↦ by rw [descVal_TU_T, revalueU_tr_code]
  hW := fun V _ _ k ↦ by rw [descVal_TU_T, revalueW_tr_code]
  hT := fun V _ _ k ↦ by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap, descVal_TU, descVal_TU_T,
      ← transposeCode_code, transposeCode_transposeCode]

/-- **The member's then-clause in ANY frame** (fuel 2): its consulted code found ⇒ the then-action. -/
theorem then_V (s : SM) (k me opp : V)
    (h : LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k)) : EvalGraph 2 me opp (s.code k) (s.a : V) := by
  unfold code
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff]
  exact Or.inl ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩


end Tau.SM

/-! ### 2. The stored template of a guard over the frozen bot-wrapped engine searcher -/

section snapshot

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The opp description, as the `D` of `plAt` (`selfD` is the me description). -/
noncomputable abbrev oppD : Semisentence LAct 14 := descF #1 #5 #6 #7

lemma progGraphAt_opp (k₀ : Option ℕ) : progGraphAt k₀ .opp = oppD := rfl

lemma lMap_swap_oppD : Semiformula.lMap swap oppD = oppD := by
  rw [lMap_swap_descF]; rfl

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma cons_val_five (x : V) (b : Fin 14 → V) : (x :> b) 5 = b 4 := rfl
omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma cons_val_six (x : V) (b : Fin 14 → V) : (x :> b) 6 = b 5 := rfl
omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma cons_val_seven (x : V) (b : Fin 14 → V) : (x :> b) 7 = b 6 := rfl

/-- The opp description in `V`: `b 0 = revalue (b 5) (b 6) (b 4)`. -/
lemma eval_oppD_V (b : Fin 14 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim oppD ↔ b 0 = revalue (b 5) (b 6) (b 4) := by
  unfold oppD descF
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc_V, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar, cons_val_five, cons_val_six,
    cons_val_seven]
  constructor
  · rintro ⟨x, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

/-- **"The opponent plays `a` against the closed watch"** in every model (`eval_plAt_self_closed` with the
opp-triple in place of the me-triple). -/
theorem eval_plAt_opp_closed (K c a : ℕ) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (plAt oppD (closedDescAt (some K) c) a) ↔
      ∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (absVal K c (b 6)) (revalue (b 4) (b 5) (b 3)) (a : V) := by
  unfold plAt
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_oppD_V, eval_closedDescAt_some_V, eval_evalG_V, Function.comp_def,
    Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

variable (g : Semisentence LAct 6) (a : ℕ)

/-- **The stored template of "the opponent plays `a` against the frozen `pBot (SV g a ·)`"**: the snapshot
described at the node budget, its budget in the slot `#6` (`closedDescAt_botSV`: the description is the same
at every budget). `templateAt (phiJ k) (some k) = gSnap gDu 0` (`templateAt_phiJ`). -/
noncomputable def gSnap : Semisentence LAct 13 :=
  plAt oppD (closedDescAt (some 0) (pBot (SV (V := ℕ) g a 0))) a

/-- **The truth of the snapshot template at a frame, in every model**: the program the opp-triple describes
plays `a` against `pBot (SV g a k)`, `k` the value of the budget slot. -/
theorem eval_gSnap (ha : a = 0 ∨ a = 1) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (gSnap g a) ↔
      ∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (pBot (SV g a (b 6))) (revalue (b 4) (b 5) (b 3)) (a : V) := by
  unfold gSnap
  rw [eval_plAt_opp_closed, absVal_botSV g a ha]

/-- τ on the snapshot template: the transposed searcher, the action swapped. -/
theorem lMap_swap_gSnap (ha : a = 0 ∨ a = 1) :
    Semiformula.lMap swap (gSnap g a) = gSnap (Semiformula.lMap swap g) (1 - a) := by
  unfold gSnap
  rw [lMap_swap_plAt, lMap_swap_oppD, lMap_swap_closedDescAt, transposeCode_pBot, transposeCode_SV g a ha]
  rcases ha with rfl | rfl
  · rw [swapAction_zero']
  · rw [swapAction_one']

end snapshot

/-! ### 3. Described players, frame guards, and the two worlds -/

/-- The transposed description of the engine searcher (`describes_botSVT` without the bot). -/
theorem describes_SVT (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) :
    Describes (Semiterm.lMap swap (TS g a)) (Semiterm.lMap swap (uS g a)) (Semiterm.lMap swap (wS g a)) where
  hX := fun V _ _ k ↦ by
    rw [descVal_SV_T g a ha, lMap_swap_TS]
    have hc : canonical (SV (Semiformula.lMap swap g) (1 - a) k) = canonical (SV g a k) := by
      rw [← transposeCode_SV g a ha, canonical_transposeCode]
    rw [hc]; exact hX_SV g a ha k
  hU := fun V _ _ k ↦ by rw [descVal_SV_T g a ha, revalueU_SVT g a ha]
  hW := fun V _ _ k ↦ by rw [descVal_SV_T g a ha, revalueW_SVT g a ha]
  hT := fun V _ _ k ↦ by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap, descVal_SV g a ha, descVal_SV_T g a ha,
      ← transposeCode_SV g a ha, transposeCode_transposeCode]

/-- **A described player**: a description triple with its `Describes` facts in both orientations (the triple
describes `val k` in every model, the transposed triple describes `transposeCode (val k)`). -/
structure DP where
  X : Semiterm LAct Empty 1
  U : ClosedSemiterm LAct 0
  W : ClosedSemiterm LAct 0
  d : Describes X U W
  dT : Describes (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)

namespace DP

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The program the player's triple denotes at the budget `k`. -/
noncomputable def val (p : DP) (k : V) : V := descVal p.X p.U p.W k

/-- The transposed player. -/
noncomputable def tr (p : DP) : DP :=
  ⟨Semiterm.lMap swap p.X, Semiterm.lMap swap p.U, Semiterm.lMap swap p.W, p.dT, by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap]; exact p.d⟩


/-- The engine searcher `SV g a k`. -/
noncomputable def ofSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) : DP :=
  ⟨TS g a, uS g a, wS g a, describes_SV g a ha, describes_SVT g a ha⟩

/-- Its frozen snapshot `pBot (SV g a k)`. -/
noncomputable def ofBotSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) : DP :=
  ⟨TBS g a, uS g a, wS g a, describes_botSV g a ha, describes_botSVT g a ha⟩

/-- A simple member `s.code k` (a searcher on a thirteen-variable stored template). -/
noncomputable def ofSM (s : SM) : DP := ⟨s.TU, s.uT, s.wT, s.describes, s.describesT⟩

/-- Mirror (τ-fixed). -/
noncomputable def mirror : DP :=
  ⟨cl TM, numT 0, numT 1, describes_mirror, by
    rw [lMap_swap_cl, lMap_swap_TM, lMap_swap_numT, lMap_swap_numT]; exact describes_mirror⟩

lemma ofSV_val (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) : (ofSV g a ha).val k = SV g a k :=
  descVal_SV g a ha k
lemma ofSV_tr_val (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    (ofSV g a ha).tr.val k = SV (Semiformula.lMap swap g) (1 - a) k := descVal_SV_T g a ha k
lemma ofBotSV_val (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    (ofBotSV g a ha).val k = pBot (SV g a k) := descVal_botSV g a ha k
lemma ofBotSV_tr_val (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    (ofBotSV g a ha).tr.val k = pBot (SV (Semiformula.lMap swap g) (1 - a) k) := descVal_botSV_T g a ha k
lemma ofSM_val (s : SM) (k : V) : (ofSM s).val k = s.code k := SM.descVal_TU s k
lemma ofSM_tr_val (s : SM) (k : V) : (ofSM s).tr.val k = s.tr.code k := SM.descVal_TU_T s k
lemma mirror_val (k : V) : mirror.val k = MirrorV := desc_mirror k
lemma mirror_tr_val (k : V) : mirror.tr.val k = MirrorV := descT_mirror k

end DP

section frameGuards

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A six-variable template in the frame of two described players. -/
noncomputable def qF (g : Semisentence LAct 6) (me opp : DP) : Semisentence LAct 1 :=
  qT g me.X me.U me.W opp.X opp.U opp.W

/-- A (member-blind) thirteen-variable stored template in the frame of two described players. -/
noncomputable def qF13 (g : Semisentence LAct 13) (me opp : DP) : Semisentence LAct 1 :=
  qPlain g me.X me.U me.W opp.X opp.U opp.W

lemma lMap_swap_qF (g : Semisentence LAct 6) (me opp : DP) :
    Semiformula.lMap swap (qF g me opp) = qF (Semiformula.lMap swap g) me.tr opp.tr := lMap_swap_qT _ _ _ _ _ _ _

lemma lMap_swap_qF13 (g : Semisentence LAct 13) (me opp : DP) :
    Semiformula.lMap swap (qF13 g me opp) = qF13 (Semiformula.lMap swap g) me.tr opp.tr :=
  lMap_swap_qPlain _ _ _ _ _ _ _

/-- **The instance equation of a six-variable guard in a described frame, in every model.** -/
theorem guardCode_qF (g : Semisentence LAct 6) (me opp : DP) (k : V) :
    guardCode (⌜g⌝ : V) (me.val k) (opp.val k) = instB (⌜qF g me opp⌝ : V) k :=
  guardCode_qT_eq_instB g k _ _ _ _ _ _ (me.d.hX V k) (me.d.hU V k) (me.d.hW V k) (opp.d.hX V k) (opp.d.hU V k)
    (opp.d.hW V k)

/-- **The instance equation of a stored thirteen-variable guard in a described frame, in every model.** -/
theorem guardCodeB_qF13 (g : Semisentence LAct 13) (hg : IsSemiformula LAct 7 ((⌜g⌝ : ℕ) : V)) (me opp : DP) (k : V) :
    guardCodeB ((⌜g⌝ : ℕ) : V) (me.val k) (opp.val k) k = instB (⌜qF13 g me opp⌝ : V) k :=
  guardCodeB_plain_eq_instB g hg k _ _ _ _ _ _ (me.d.hX V k) (me.d.hU V k) (me.d.hW V k) (opp.d.hX V k)
    (opp.d.hU V k) (opp.d.hW V k)

/-- The atom guard "the opponent plays `c` against me" in a described frame. -/
theorem eval_qF_plays (c : PD.Action) (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qF (template (.plays .opp .self c)) me opp) ↔
      ∃ n, EvalGraph n (opp.val k) (me.val k) (opp.val k) (actCode c : V) :=
  eval_qT_plays_opp_self c _ _ _ _ _ _ k rfl rfl

/-- The implication guard "if I play `c` against the opponent, it plays `c` against me" in a described frame. -/
theorem eval_qF_impl (c : PD.Action) (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qF (template (.impl (.plays .self .opp c) (.plays .opp .self c))) me opp) ↔
      ((∃ n, EvalGraph n (me.val k) (opp.val k) (me.val k) (actCode c : V)) →
        (∃ n, EvalGraph n (opp.val k) (me.val k) (opp.val k) (actCode c : V))) := by
  unfold qF
  rw [eval_qT_iff, template_impl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_template_plays_self_opp_V, eval_template_plays_opp_self_V, Matrix.cons_val]
  rfl

/-- The snapshot guard "the opponent plays `a` against the frozen `pBot (SV g a k)`" in a described frame. -/
theorem eval_qF13_snap (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qF13 (gSnap g a) me opp) ↔
      ∃ n, EvalGraph n (opp.val k) (pBot (SV g a k)) (opp.val k) (a : V) := by
  unfold qF13
  rw [eval_qPlain_iff, eval_gSnap g a ha]
  simp only [Matrix.cons_val]
  rfl

end frameGuards

/-! ### 4. The two worlds -/

/-- "The opponent plays `c` against me": Dupoc's guard template (`c = C`, `gDu`), Cupod's (`c = D`, `gCu`). -/
noncomputable abbrev gP (c : PD.Action) : Semisentence LAct 6 := template (.plays .opp .self c)

/-- "If I play `c` against the opponent, it plays `c` against me": CIMCIC's guard template (`c = C`, `templateC`)
and its transposition (`c = D`, `templateCT`). -/
noncomputable abbrev gI (c : PD.Action) : Semisentence LAct 6 :=
  template (.impl (.plays .self .opp c) (.plays .opp .self c))

lemma lMap_swap_gP_C : Semiformula.lMap swap (gP .C) = gP .D := lMap_swap_template _ rfl
lemma lMap_swap_gI_C : Semiformula.lMap swap (gI .C) = gI .D := lMap_swap_template _ rfl

/-- **Just as a simple member, in the world `c`**: the searcher on the stored snapshot template, then-action `c`.
`progCode (JustBot k) = (sJc .C).code k` (`progCode_JustBot_sJ`). -/
noncomputable def sJc (c : PD.Action) : SM := ⟨gSnap (gP c) (actCode c), actCode c, actCode_zero_or_one c⟩

/-- Just's guard with the snapshot `CupodBot k` and the action `D`: the transposition of `phiJ k`. -/
def phiJT (k : ℕ) : PD.Formula := .plays .opp (.bot (CupodBot k)) .D

/-- **The engine's stored template of JustBot is the snapshot template, at every budget.** -/
theorem templateAt_phiJ (K : ℕ) : templateAt (phiJ K) (some K) = gSnap (gP .C) (actCode .C) := by
  have e1 := closedDescAt_botSV (gP .C) (actCode .C) (actCode_zero_or_one .C) K
  have e0 := closedDescAt_botSV (gP .C) (actCode .C) (actCode_zero_or_one .C) 0
  unfold phiJ gSnap
  rw [templateAt_plays_eq, progGraphAt_opp,
    progGraphAt_closed (X := .bot (DupocBot K)) _ (by simp) (by simp) rfl, progCode_bot, progCode_DupocBot_SV]
  exact congrArg (fun D ↦ plAt oppD D (actCode .C)) (e1.trans e0.symm)

theorem templateAt_phiJT (K : ℕ) : templateAt (phiJT K) (some K) = gSnap (gP .D) (actCode .D) := by
  have e1 := closedDescAt_botSV (gP .D) (actCode .D) (actCode_zero_or_one .D) K
  have e0 := closedDescAt_botSV (gP .D) (actCode .D) (actCode_zero_or_one .D) 0
  unfold phiJT gSnap
  rw [templateAt_plays_eq, progGraphAt_opp,
    progGraphAt_closed (X := .bot (CupodBot K)) _ (by simp) (by simp) rfl, progCode_bot, progCode_CupodBot_SV]
  exact congrArg (fun D ↦ plAt oppD D (actCode .D)) (e1.trans e0.symm)

theorem isSemiformula7_gSnap_C (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    IsSemiformula LAct 7 ((⌜gSnap (gP .C) (actCode .C)⌝ : ℕ) : V) := by
  rw [← templateAt_phiJ 0]; exact isSemiformula7_cast_templateAt _ 0 rfl V

theorem isSemiformula7_gSnap_D (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    IsSemiformula LAct 7 ((⌜gSnap (gP .D) (actCode .D)⌝ : ℕ) : V) := by
  rw [← templateAt_phiJT 0]; exact isSemiformula7_cast_templateAt _ 0 rfl V

/-- **The engine's `JustBot k` is the simple member `sJc .C` at the budget `k`.** -/
theorem progCode_JustBot_sJ (k : ℕ) : progCode (JustBot k) = (sJc .C).code (V := ℕ) k := by
  rw [progCode_JustBot]
  unfold SM.code templateCodeAt
  rw [templateAt_phiJ]
  simp only [natCast_nat]
  rfl

/-- The transposition of Just in the standard world is Just in the transposed world. -/
lemma sJc_tr_code {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V) : (sJc .C).tr.code k = (sJc .D).code k := by
  unfold SM.code
  rw [SM.tr_g, SM.tr_a]
  show pSearch k ((⌜Semiformula.lMap swap (gSnap (gP .C) (actCode .C))⌝ : ℕ) : V) _ _ =
    pSearch k ((⌜gSnap (gP .D) (actCode .D)⌝ : ℕ) : V) _ _
  rw [lMap_swap_gSnap _ _ (actCode_zero_or_one .C), lMap_swap_gP_C]
  rfl

/-- **A world**: the five players of JustBot's cells — Just, its frozen snapshot, Dupoc, CIMCIC, Mirror — as
described players, with the codes their triples denote in every model: Just is the simple member `sJc c`, the
snapshot `pBot (SV (gP c) c k)`, Dupoc `SV (gP c) c k`, CIMCIC `SV (gI c) c k`. `c = C` is the engine's zoo
(`worldC`), `c = D` its transposition (`worldD`: JustBot's transposition, the frozen Cupod, Cupod, CIMCIC's
transposition, Mirror). -/
structure World where
  c : PD.Action
  J : DP
  B : DP
  D : DP
  I : DP
  M : DP
  hJ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), J.val k = (sJc c).code k
  hB : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), B.val k = pBot (SV (gP c) (actCode c) k)
  hD : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), D.val k = SV (gP c) (actCode c) k
  hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), I.val k = SV (gI c) (actCode c) k
  hM : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), M.val k = MirrorV
  hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    IsSemiformula LAct 7 ((⌜gSnap (gP c) (actCode c)⌝ : ℕ) : V)

/-- **The standard world**: the engine's `JustBot k`, `.bot (DupocBot k)`, `DupocBot k`, `CIMCIC k`, `MirrorBot`. -/
noncomputable def worldC : World where
  c := .C
  J := DP.ofSM (sJc .C)
  B := DP.ofBotSV (gP .C) (actCode .C) (actCode_zero_or_one .C)
  D := DP.ofSV (gP .C) (actCode .C) (actCode_zero_or_one .C)
  I := DP.ofSV (gI .C) (actCode .C) (actCode_zero_or_one .C)
  M := DP.mirror
  hJ := fun _ _ _ k ↦ DP.ofSM_val _ k
  hB := fun _ _ _ k ↦ DP.ofBotSV_val _ _ _ k
  hD := fun _ _ _ k ↦ DP.ofSV_val _ _ _ k
  hI := fun _ _ _ k ↦ DP.ofSV_val _ _ _ k
  hM := fun _ _ _ k ↦ DP.mirror_val k
  hg7 := isSemiformula7_gSnap_C

/-- **The transposed world**: the same five triples, transposed. -/
noncomputable def worldD : World where
  c := .D
  J := (DP.ofSM (sJc .C)).tr
  B := (DP.ofBotSV (gP .C) (actCode .C) (actCode_zero_or_one .C)).tr
  D := (DP.ofSV (gP .C) (actCode .C) (actCode_zero_or_one .C)).tr
  I := (DP.ofSV (gI .C) (actCode .C) (actCode_zero_or_one .C)).tr
  M := DP.mirror.tr
  hJ := fun _ _ _ k ↦ by rw [DP.ofSM_tr_val, sJc_tr_code]
  hB := fun _ _ _ k ↦ by rw [DP.ofBotSV_tr_val, lMap_swap_gP_C]; rfl
  hD := fun _ _ _ k ↦ by rw [DP.ofSV_tr_val, lMap_swap_gP_C]; rfl
  hI := fun _ _ _ k ↦ by rw [DP.ofSV_tr_val, lMap_swap_gI_C]; rfl
  hM := fun _ _ _ k ↦ DP.mirror_tr_val k
  hg7 := isSemiformula7_gSnap_D

namespace World

variable (w : World) {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Just's guard in the frame `(me, opp)`**: "`opp` plays `c` against the frozen snapshot". -/
noncomputable def qJ (me opp : DP) : Semisentence LAct 1 := qF13 (gSnap (gP w.c) (actCode w.c)) me opp
/-- **Dupoc's guard in the frame `(me, opp)`** (also the guard its frozen snapshot consults there): "`opp` plays
`c` against `me`". -/
noncomputable def qP (me opp : DP) : Semisentence LAct 1 := qF (gP w.c) me opp
/-- **CIMCIC's guard in the frame `(me, opp)`**: "if `me` plays `c` against `opp`, `opp` plays `c` against `me`". -/
noncomputable def qI (me opp : DP) : Semisentence LAct 1 := qF (gI w.c) me opp

theorem eval_qJ (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (w.qJ me opp) ↔
      ∃ n, EvalGraph n (opp.val k) (w.B.val k) (opp.val k) (actCode w.c : V) := by
  unfold qJ
  rw [eval_qF13_snap _ _ (actCode_zero_or_one _), w.hB V k]

theorem eval_qP (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (w.qP me opp) ↔
      ∃ n, EvalGraph n (opp.val k) (me.val k) (opp.val k) (actCode w.c : V) :=
  eval_qF_plays w.c me opp k

theorem eval_qI (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (w.qI me opp) ↔
      ((∃ n, EvalGraph n (me.val k) (opp.val k) (me.val k) (actCode w.c : V)) →
        (∃ n, EvalGraph n (opp.val k) (me.val k) (opp.val k) (actCode w.c : V))) :=
  eval_qF_impl w.c me opp k

/-- **Just's search clause**: its guard found in the frame `(me, opp)` ⇒ Just plays `c` there (fuel 2). -/
theorem J_then (me opp : DP) (k : V) (h : LenBox TAct k (instB (⌜w.qJ me opp⌝ : V) k)) :
    EvalGraph 2 (me.val k) (opp.val k) (w.J.val k) (actCode w.c : V) := by
  unfold qJ at h
  rw [← guardCodeB_qF13 _ (w.hg7 V)] at h
  have e := SM.then_V (sJc w.c) k (me.val k) (opp.val k) h
  rw [w.hJ V k]
  exact e

/-- **Dupoc's search clause**: its guard found in the frame `(me, opp)` ⇒ Dupoc plays `c` there (fuel 2). -/
theorem D_then (me opp : DP) (k : V) (h : LenBox TAct k (instB (⌜w.qP me opp⌝ : V) k)) :
    EvalGraph 2 (me.val k) (opp.val k) (w.D.val k) (actCode w.c : V) := by
  unfold qP at h
  rw [← guardCode_qF] at h
  rw [w.hD V k]
  exact SV_then_V (gP w.c) (actCode w.c) k _ _ h

/-- **The frozen snapshot's search clause**: Dupoc's guard found in the frame `(me, opp)` ⇒ the snapshot plays
`c` there (fuel 3). -/
theorem B_then (me opp : DP) (k : V) (h : LenBox TAct k (instB (⌜w.qP me opp⌝ : V) k)) :
    EvalGraph 3 (me.val k) (opp.val k) (w.B.val k) (actCode w.c : V) := by
  unfold qP at h
  rw [← guardCode_qF] at h
  rw [w.hB V k]
  exact botSV_then_V (gP w.c) (actCode w.c) k _ _ h

/-- **CIMCIC's search clause** (fuel 2). -/
theorem I_then (me opp : DP) (k : V) (h : LenBox TAct k (instB (⌜w.qI me opp⌝ : V) k)) :
    EvalGraph 2 (me.val k) (opp.val k) (w.I.val k) (actCode w.c : V) := by
  unfold qI at h
  rw [← guardCode_qF] at h
  rw [w.hI V k]
  exact SV_then_V (gI w.c) (actCode w.c) k _ _ h

/-- Mirror copies a fuel-2 play at fuel 3. -/
theorem M_copies2 {x a : V} (k : V) (h : EvalGraph 2 x (w.M.val k) x a) : EvalGraph 3 (w.M.val k) x (w.M.val k) a := by
  rw [w.hM V k] at h ⊢
  exact mirror_copies2_V x a h

/-- Mirror copies a fuel-3 play at fuel 4. -/
theorem M_copies3 {x a : V} (k : V) (h : EvalGraph 3 x (w.M.val k) x a) : EvalGraph 4 (w.M.val k) x (w.M.val k) a := by
  rw [w.hM V k] at h ⊢
  exact mirror_copies3_V x a h

end World

/-! #### τ between the worlds, and the family assembly -/

lemma swap_qJ (me opp : DP) : Semiformula.lMap swap (worldC.qJ me opp) = worldD.qJ me.tr opp.tr := by
  show Semiformula.lMap swap (qF13 (gSnap (gP .C) (actCode .C)) me opp) = qF13 (gSnap (gP .D) (actCode .D)) me.tr opp.tr
  rw [lMap_swap_qF13, lMap_swap_gSnap _ _ (actCode_zero_or_one .C), lMap_swap_gP_C]
  rfl

lemma swap_qP (me opp : DP) : Semiformula.lMap swap (worldC.qP me opp) = worldD.qP me.tr opp.tr := by
  show Semiformula.lMap swap (qF (gP .C) me opp) = qF (gP .D) me.tr opp.tr
  rw [lMap_swap_qF, lMap_swap_gP_C]

lemma swap_qI (me opp : DP) : Semiformula.lMap swap (worldC.qI me opp) = worldD.qI me.tr opp.tr := by
  show Semiformula.lMap swap (qF (gI .C) me opp) = qF (gI .D) me.tr opp.tr
  rw [lMap_swap_qF, lMap_swap_gI_C]

/-- **The Löb premise of a family stated for an arbitrary world**: if the transposition of the standard world's
guards are the transposed world's guards, and in EVERY world the boxes of the guards make the guards true in the
standard reading, the family of the standard world is Löb-sound — its swapped reading is the standard reading
of the transposed world's family. -/
theorem loebSound_world (q : World → Semisentence LAct 1) (rs : World → List (Semisentence LAct 1))
    (hq : Semiformula.lMap swap (q worldC) = q worldD) (hrs : (rs worldC).map (Semiformula.lMap swap) = rs worldD)
    (core : ∀ (w : World) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (∀ r ∈ q w :: rs w, LenBox TAct k (instB (⌜r⌝ : V) k)) →
      ∀ r ∈ q w :: rs w, Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim r) :
    LoebSound (pQ (conjL (q worldC) (rs worldC))) (7 * ((rs worldC).length + 1) + 0) (8 * ((rs worldC).length + 1)) := by
  refine loebSound_pL_above _ _ 0 fun V _ _ k _ hb r hr ↦ ?_
  have hmap : ∀ r' ∈ q worldD :: rs worldD, LenBox TAct k (instB (⌜r'⌝ : V) k) := by
    intro r' hr'
    rw [← hq, ← hrs, ← List.map_cons] at hr'
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
    exact (hb r₀ hr₀).2
  rw [← stdReadingV_eq_stdReading]
  refine ⟨core worldC V k (fun r hr ↦ (hb r hr).1) r hr, core worldD V k hmap _ ?_⟩
  rw [← hq, ← hrs, ← List.map_cons]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

/-- **Every guard of a world family is FOUND within the budget, for all large `k`** (`family_found` at
`boundedInnerNec_sixteen`, then the ∧-eliminations on codes). -/
theorem found_world (q : World → Semisentence LAct 1) (rs : World → List (Semisentence LAct 1))
    (hq : Semiformula.lMap swap (q worldC) = q worldD) (hrs : (rs worldC).map (Semiformula.lMap swap) = rs worldD)
    (core : ∀ (w : World) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (∀ r ∈ q w :: rs w, LenBox TAct k (instB (⌜r⌝ : V) k)) →
      ∀ r ∈ q w :: rs w, Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim r) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ q worldC :: rs worldC, LenBox TAct k (instB (⌜r⌝ : ℕ) k) := by
  obtain ⟨k₀, hf⟩ := family_found _ boundedInnerNec_sixteen (loebSound_world q rs hq hrs core)
  refine ⟨k₀, fun k hk r hr ↦ ?_⟩
  obtain ⟨a, ha, hbox⟩ := hf k hk
  exact (boxes_pL_nat _ _ 0 k a ha hbox r hr).1

/-! #### The standard world at ℕ: the engine's codes -/

lemma worldC_J_nat (k : ℕ) : worldC.J.val (V := ℕ) k = progCode (JustBot k) := by
  rw [worldC.hJ ℕ k, progCode_JustBot_sJ]; rfl

lemma worldC_D_nat (k : ℕ) : worldC.D.val (V := ℕ) k = progCode (DupocBot k) := by
  rw [worldC.hD ℕ k, progCode_DupocBot_SV]; rfl


lemma worldC_I_nat (k : ℕ) : worldC.I.val (V := ℕ) k = progCode (CIMCIC k) := by
  rw [worldC.hI ℕ k, progCode_CIMCIC, ← CimcicV_nat, CimcicV_eq_SV]; rfl

lemma worldC_M_nat (k : ℕ) : worldC.M.val (V := ℕ) k = progCode MirrorBot := by
  rw [worldC.hM ℕ k, progCode_MirrorBot]; rfl


/-! ### 5. JustBot × MirrorBot `(C, C)` -/

section justMirror

/-- Just's guard against Mirror: "Mirror plays `c` against the frozen snapshot". -/
noncomputable def jmQ (w : World) : Semisentence LAct 1 := w.qJ w.J w.M
/-- The snapshot's own guard against Mirror: "Mirror plays `c` against me" (the same truth, a different code). -/
noncomputable def jmR (w : World) : List (Semisentence LAct 1) := [w.qP w.B w.M]

/-- **The semantic core of Just × Mirror, in any world**: the two boxes make the snapshot play `c` against
Mirror (fuel 3), Mirror copies (fuel 4), so both guards are true; and Just plays `c` against Mirror (fuel 2),
which Mirror copies (fuel 3). -/
theorem jm_core (w : World) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V)
    (hb : ∀ r ∈ jmQ w :: jmR w, LenBox TAct k (instB (⌜r⌝ : V) k)) :
    (EvalGraph 2 (w.J.val k) (w.M.val k) (w.J.val k) (actCode w.c : V) ∧
      EvalGraph 3 (w.M.val k) (w.J.val k) (w.M.val k) (actCode w.c : V)) ∧
    ∀ r ∈ jmQ w :: jmR w, Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim r := by
  have b₁ : LenBox TAct k (instB (⌜w.qJ w.J w.M⌝ : V) k) := hb _ (by simp [jmQ])
  have b₂ : LenBox TAct k (instB (⌜w.qP w.B w.M⌝ : V) k) := hb _ (by simp [jmR])
  have eM := w.M_copies3 k (w.B_then w.B w.M k b₂)
  have eJ := w.J_then w.J w.M k b₁
  refine ⟨⟨eJ, w.M_copies2 k eJ⟩, fun r hr ↦ ?_⟩
  simp only [jmQ, jmR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (w.eval_qJ _ _ k).mpr ⟨_, eM⟩
  · exact (w.eval_qP _ _ k).mpr ⟨_, eM⟩

/-- **Both guards of the Just × Mirror family are found within the budget, for all large `k`** (bounded Löb). -/
theorem jm_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ jmQ worldC :: jmR worldC, LenBox TAct k (instB (⌜r⌝ : ℕ) k) :=
  found_world jmQ jmR (swap_qJ _ _) (by simp only [jmR, List.map_cons, List.map_nil, swap_qP]; rfl)
    (fun w V _ _ k hb ↦ (jm_core w V k hb).2)

/-- **JustBot × MirrorBot is `(C, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes
(the hand-twin forms are `loeb_Just_vs_Mirror`, `loeb_Just7_vs_Mirror`): `JustBot k` finds "Mirror cooperates
with `.bot (DupocBot k)`" and cooperates (fuel 2), Mirror copies (fuel 3). -/
theorem loeb_JustBot_vs_MirrorBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (JustBot k)) (progCode MirrorBot) (progCode (JustBot k)) (actCode .C) ∧
      EvalGraph 3 (progCode MirrorBot) (progCode (JustBot k)) (progCode MirrorBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := jm_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp := (jm_core worldC ℕ k (h k hk)).1
  rw [worldC_J_nat, worldC_M_nat] at hp
  simp only [natCast_nat] at hp
  exact hp


end justMirror

/-! ### 6. JustBot × JustBot `(C, C)` -/

section justSelf

/-- Just's guard against Just: "Just plays `c` against the frozen snapshot". -/
noncomputable def jjQ (w : World) : Semisentence LAct 1 := w.qJ w.J w.J
/-- Just's guard against the snapshot ("the snapshot plays `c` against itself") and the snapshot's guard against
itself (the same truth, Dupoc's template). -/
noncomputable def jjR (w : World) : List (Semisentence LAct 1) := [w.qJ w.J w.B, w.qP w.B w.B]

/-- **The semantic core of Just × Just, in any world**: the snapshot's box makes it play `c` against itself
(fuel 3), so Just's guard against the snapshot is true; its box makes Just play `c` against the snapshot
(fuel 2), so Just's guard against Just is true; its box makes Just play `c` against itself. -/
theorem jj_core (w : World) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V)
    (hb : ∀ r ∈ jjQ w :: jjR w, LenBox TAct k (instB (⌜r⌝ : V) k)) :
    EvalGraph 2 (w.J.val k) (w.J.val k) (w.J.val k) (actCode w.c : V) ∧
    ∀ r ∈ jjQ w :: jjR w, Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim r := by
  have b₁ : LenBox TAct k (instB (⌜w.qJ w.J w.J⌝ : V) k) := hb _ (by simp [jjQ])
  have b₂ : LenBox TAct k (instB (⌜w.qJ w.J w.B⌝ : V) k) := hb _ (by simp [jjR])
  have b₃ : LenBox TAct k (instB (⌜w.qP w.B w.B⌝ : V) k) := hb _ (by simp [jjR])
  have eB := w.B_then w.B w.B k b₃
  have eJB := w.J_then w.J w.B k b₂
  refine ⟨w.J_then w.J w.J k b₁, fun r hr ↦ ?_⟩
  simp only [jjQ, jjR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (w.eval_qJ _ _ k).mpr ⟨_, eJB⟩
  · exact (w.eval_qJ _ _ k).mpr ⟨_, eB⟩
  · exact (w.eval_qP _ _ k).mpr ⟨_, eB⟩

/-- **The three guards of the Just × Just family are found within the budget, for all large `k`** (bounded Löb). -/
theorem jj_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ jjQ worldC :: jjR worldC, LenBox TAct k (instB (⌜r⌝ : ℕ) k) :=
  found_world jjQ jjR (swap_qJ _ _) (by simp only [jjR, List.map_cons, List.map_nil, swap_qP, swap_qJ]; rfl)
    (fun w V _ _ k hb ↦ (jj_core w V k hb).2)

/-- **JustBot × JustBot is `(C, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own code (the
hand-twin form is `loeb_Just7_vs_Just7`): `JustBot k` cooperates with itself at fuel 2. -/
theorem loeb_JustBot_vs_JustBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (JustBot k)) (progCode (JustBot k)) (progCode (JustBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := jj_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp := (jj_core worldC ℕ k (h k hk)).1
  rw [worldC_J_nat] at hp
  simp only [natCast_nat] at hp
  exact hp


end justSelf

/-! ### 7. JustBot × DupocBot `(C, C)` -/

section justDupoc

/-- Just's guard against Dupoc: "Dupoc plays `c` against the frozen snapshot". -/
noncomputable def jdQ (w : World) : Semisentence LAct 1 := w.qJ w.J w.D
/-- Dupoc's guard against the snapshot, the snapshot's guard against Dupoc, Dupoc's guard against Just. -/
noncomputable def jdR (w : World) : List (Semisentence LAct 1) := [w.qP w.D w.B, w.qP w.B w.D, w.qP w.D w.J]

/-- **The semantic core of Just × Dupoc, in any world**: the four guards chase each other — the snapshot's box
makes it play `c` against Dupoc (the truth of Dupoc's guard against it), Dupoc's box makes Dupoc play `c`
against the snapshot (the truth of Just's guard against Dupoc and of the snapshot's against Dupoc), Just's
box makes Just play `c` against Dupoc (the truth of Dupoc's guard against Just), and Dupoc's box against Just
makes Dupoc play `c` against Just. -/
theorem jd_core (w : World) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V)
    (hb : ∀ r ∈ jdQ w :: jdR w, LenBox TAct k (instB (⌜r⌝ : V) k)) :
    (EvalGraph 2 (w.J.val k) (w.D.val k) (w.J.val k) (actCode w.c : V) ∧
      EvalGraph 2 (w.D.val k) (w.J.val k) (w.D.val k) (actCode w.c : V)) ∧
    ∀ r ∈ jdQ w :: jdR w, Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim r := by
  have b₁ : LenBox TAct k (instB (⌜w.qJ w.J w.D⌝ : V) k) := hb _ (by simp [jdQ])
  have b₂ : LenBox TAct k (instB (⌜w.qP w.D w.B⌝ : V) k) := hb _ (by simp [jdR])
  have b₃ : LenBox TAct k (instB (⌜w.qP w.B w.D⌝ : V) k) := hb _ (by simp [jdR])
  have b₄ : LenBox TAct k (instB (⌜w.qP w.D w.J⌝ : V) k) := hb _ (by simp [jdR])
  have eBD := w.B_then w.B w.D k b₃
  have eDB := w.D_then w.D w.B k b₂
  have eJD := w.J_then w.J w.D k b₁
  refine ⟨⟨eJD, w.D_then w.D w.J k b₄⟩, fun r hr ↦ ?_⟩
  simp only [jdQ, jdR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (w.eval_qJ _ _ k).mpr ⟨_, eDB⟩
  · exact (w.eval_qP _ _ k).mpr ⟨_, eBD⟩
  · exact (w.eval_qP _ _ k).mpr ⟨_, eDB⟩
  · exact (w.eval_qP _ _ k).mpr ⟨_, eJD⟩

/-- **The four guards of the Just × Dupoc family are found within the budget, for all large `k`** (bounded Löb). -/
theorem jd_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ jdQ worldC :: jdR worldC, LenBox TAct k (instB (⌜r⌝ : ℕ) k) :=
  found_world jdQ jdR (swap_qJ _ _) (by simp only [jdR, List.map_cons, List.map_nil, swap_qP]; rfl)
    (fun w V _ _ k hb ↦ (jd_core w V k hb).2)

/-- **JustBot × DupocBot is `(C, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes (the
hand-twin form is `loeb_Just7_vs_Dupoc`; the engine's `outcome_JustBot_vs_DupocBot`, the mutual Löb cell): both
cooperate at fuel 2. -/
theorem loeb_JustBot_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (JustBot k)) (progCode (DupocBot k)) (progCode (JustBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode (DupocBot k)) (progCode (JustBot k)) (progCode (DupocBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := jd_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp := (jd_core worldC ℕ k (h k hk)).1
  rw [worldC_J_nat, worldC_D_nat] at hp
  simp only [natCast_nat] at hp
  exact hp


end justDupoc

/-! ### 8. CIMCIC × JustBot `(C, C)` -/

section cimcicJust

/-- CIMCIC's guard against Just: "if I play `c` against Just, Just plays `c` against me". -/
noncomputable def cjQ (w : World) : Semisentence LAct 1 := w.qI w.I w.J
/-- Just's guard against CIMCIC ("CIMCIC plays `c` against the snapshot"), CIMCIC's guard against the snapshot,
the snapshot's guard against CIMCIC. -/
noncomputable def cjR (w : World) : List (Semisentence LAct 1) := [w.qJ w.J w.I, w.qI w.I w.B, w.qP w.B w.I]

/-- **The semantic core of CIMCIC × Just, in any world**: the snapshot's box makes it play `c` against CIMCIC
(the consequent of CIMCIC's guard against it), CIMCIC's box makes CIMCIC play `c` against the snapshot (the truth
of Just's guard against CIMCIC and of the snapshot's), Just's box makes Just play `c` against CIMCIC (the
consequent of CIMCIC's guard against Just), and CIMCIC's box makes CIMCIC play `c` against Just. -/
theorem cj_core (w : World) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V)
    (hb : ∀ r ∈ cjQ w :: cjR w, LenBox TAct k (instB (⌜r⌝ : V) k)) :
    (EvalGraph 2 (w.I.val k) (w.J.val k) (w.I.val k) (actCode w.c : V) ∧
      EvalGraph 2 (w.J.val k) (w.I.val k) (w.J.val k) (actCode w.c : V)) ∧
    ∀ r ∈ cjQ w :: cjR w, Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim r := by
  have b₁ : LenBox TAct k (instB (⌜w.qI w.I w.J⌝ : V) k) := hb _ (by simp [cjQ])
  have b₂ : LenBox TAct k (instB (⌜w.qJ w.J w.I⌝ : V) k) := hb _ (by simp [cjR])
  have b₃ : LenBox TAct k (instB (⌜w.qI w.I w.B⌝ : V) k) := hb _ (by simp [cjR])
  have b₄ : LenBox TAct k (instB (⌜w.qP w.B w.I⌝ : V) k) := hb _ (by simp [cjR])
  have eBI := w.B_then w.B w.I k b₄
  have eIB := w.I_then w.I w.B k b₃
  have eJI := w.J_then w.J w.I k b₂
  refine ⟨⟨w.I_then w.I w.J k b₁, eJI⟩, fun r hr ↦ ?_⟩
  simp only [cjQ, cjR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (w.eval_qI _ _ k).mpr fun _ ↦ ⟨_, eJI⟩
  · exact (w.eval_qJ _ _ k).mpr ⟨_, eIB⟩
  · exact (w.eval_qI _ _ k).mpr fun _ ↦ ⟨_, eBI⟩
  · exact (w.eval_qP _ _ k).mpr ⟨_, eIB⟩

/-- **The four guards of the CIMCIC × Just family are found within the budget, for all large `k`** (bounded Löb). -/
theorem cj_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∀ r ∈ cjQ worldC :: cjR worldC, LenBox TAct k (instB (⌜r⌝ : ℕ) k) :=
  found_world cjQ cjR (swap_qI _ _)
    (by simp only [cjR, List.map_cons, List.map_nil, swap_qP, swap_qJ, swap_qI]; rfl)
    (fun w V _ _ k hb ↦ (cj_core w V k hb).2)

/-- **CIMCIC × JustBot is `(C, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes (the
hand-twin form is `loeb_Cimcic_vs_Just7`; the engine's `llm_outcome_CIMCIC_vs_JustBot`): both cooperate at
fuel 2. -/
theorem loeb_CIMCIC_vs_JustBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CIMCIC k)) (progCode (JustBot k)) (progCode (CIMCIC k)) (actCode .C) ∧
      EvalGraph 2 (progCode (JustBot k)) (progCode (CIMCIC k)) (progCode (JustBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := cj_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hp := (cj_core worldC ℕ k (h k hk)).1
  rw [worldC_J_nat, worldC_I_nat] at hp
  simp only [natCast_nat] at hp
  exact hp


end cimcicJust

/-! ### 9. DIMCID × JustBot `(D, D)` — a FLIP (the engine has `(C, D)`) -/

section dimcidJust

/-- **DIMCID defects against the engine's `JustBot k` and FINDS its guard, for all large `k`**: the engine's
JustBot is a described opponent (`SM.describes`, on its constant stored template), so `dimcid_vs_described`
applies — the twin form is `loeb_DIMCID_vs_Just7`. -/
theorem loeb_DIMCID_vs_JustBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (JustBot k)) (progCode (DIMCID k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiD) (progCode (DIMCID k)) (progCode (JustBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (sJc .C).describes
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [templateCode_eq_quote_template phiD rfl]
  rwa [SM.descVal_TU, ← progCode_JustBot_sJ, ← progCode_DIMCID] at this

/-- **DIMCID × JustBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes (the
twin form, on `Just7 k`, is `loeb_DIMCID_vs_JustBot`). The engine proves `(C, D)` by a floor census
(`llm_outcome_DIMCID_vs_JustBot`); in `S'` DIMCID's guard against the described Just is self-fulfilling and
found, so DIMCID defects; Just's guard "DIMCID plays C against `.bot (DupocBot k)`" is FALSE, never found by
soundness, so Just defects (`snd_JustBot_vs_DIMCID_engine`). -/
theorem loeb_DIMCID_vs_JustBot_engine :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (JustBot k)) (progCode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (progCode (JustBot k)) (progCode (DIMCID k)) (progCode (JustBot k)) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := loeb_DIMCID_vs_JustBot_core
  obtain ⟨k₂, h₂⟩ := snd_JustBot_vs_DIMCID_engine
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨(h₁ k (by omega)).1, h₂ k (by omega)⟩⟩


end dimcidJust

end ArithS
