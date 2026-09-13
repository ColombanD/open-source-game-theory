import ArithS.Necessitation.Steps
import ArithS.Necessitation.RowInst

/-!
# ArithS.Necessitation.Chain — the step language, contexts, and the primitive-recursive chain

`M4_BOUNDED_HBL/BRIEF.md` §10: a fragment of the verification proof is a LIST of steps, each a
code `⟪tag, …⟫` naming a library row by its INDEX in a row table and its witnesses as a vector
of term codes; the derivation code is assembled by a primitive-recursive chain builder
`chainCode` from the end of the list, and its correctness (`chainCode_proof`) and length
(`dlen_chainCode_le`) are proved by `𝗜𝚺₁`-induction on the position — so every producer of the
verification proof is a Σ₁ function returning a step list, never a continuation.

The step constructors of `ArithS.Necessitation.Steps` take Lean-level lists (`es as : List V`);
a Σ₁ `applyStep` needs them on HFS vectors. Part A builds the vector-level twins
(`useHornV`, `useHornAndV`, `introFactV`) by `VecRec`/`PR` constructions and proves them EQUAL to
the list constructors on `vecOf es` (`useHornV_vecOf`, …), so every `_proof`/`dlen_…_le` theorem
of `Steps.lean` transfers verbatim. The one substitution fact behind this: `instOuter es B`
is ONE simultaneous substitution, `subst (vecOf es.reverse) B` (`subst_revV_vecOf`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## Part A — vector-level twins of the step constructors -/

/-! ### A.1 Lean lists as HFS vectors -/

/-- `vecOf [x₀, …, xₙ₋₁] = x₀ ∷ … ∷ xₙ₋₁ ∷ 0`. -/
noncomputable def vecOf : List V → V
  | [] => 0
  | x :: xs => x ∷ vecOf xs

@[simp] lemma vecOf_nil : vecOf ([] : List V) = 0 := rfl
@[simp] lemma vecOf_cons (x : V) (xs : List V) : vecOf (x :: xs) = x ∷ vecOf xs := rfl

@[simp] lemma len_vecOf : ∀ (xs : List V), len (vecOf xs) = (xs.length : V)
  | [] => by simp
  | x :: xs => by simp [len_vecOf xs]

lemma nth_vecOf : ∀ (xs : List V) (i : ℕ) (h : i < xs.length), (vecOf xs).[(i : V)] = xs[i]
  | x :: xs, 0, _ => by simp
  | x :: xs, i + 1, h => by
    rw [vecOf_cons, Nat.cast_succ, nth_adjoin_succ, nth_vecOf xs i (by simpa using h)]
    simp

lemma concat_vecOf : ∀ (xs : List V) (z : V), concat (vecOf xs) z = vecOf (xs ++ [z])
  | [], z => by simp
  | x :: xs, z => by simp [concat_vecOf xs z]

/-! ### A.2 The vector combinators (`VecRec`/`PR` constructions) -/

namespace RevV

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. !concatDef y ih x”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := concat ih x
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end RevV

/-- The reversed vector. -/
noncomputable def revV (v : V) : V := RevV.construction.result ![] v

@[simp] lemma revV_nil : revV (0 : V) = 0 := by simp [revV, RevV.construction]
@[simp] lemma revV_adjoin (x v : V) : revV (x ∷ v) = concat (revV v) x := by
  simp [revV, RevV.construction]

def revVDef : 𝚺₁.Semisentence 2 := RevV.blueprint.resultDef

instance revV_defined : 𝚺₁-Function₁ (revV : V → V) via revVDef := RevV.construction.result_defined
instance revV_definable : 𝚺₁-Function₁ (revV : V → V) := revV_defined.to_definable

lemma revV_vecOf : ∀ (xs : List V), revV (vecOf xs) = vecOf xs.reverse
  | [] => by simp
  | x :: xs => by rw [vecOf_cons, revV_adjoin, revV_vecOf xs, concat_vecOf, List.reverse_cons]

namespace TailIter

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y w. y = w”
  succ := .mkSigma “y ih i w. !sndIdxDef y ih”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ sndIdx ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end TailIter

/-- `tailIter w k` drops the first `k` entries of the vector `w`. -/
noncomputable def tailIter (w k : V) : V := TailIter.construction.result ![w] k

@[simp] lemma tailIter_zero (w : V) : tailIter w 0 = w := by simp [tailIter, TailIter.construction]
@[simp] lemma tailIter_succ (w k : V) : tailIter w (k + 1) = sndIdx (tailIter w k) := by
  simp [tailIter, TailIter.construction]

def tailIterDef : 𝚺₁.Semisentence 3 := TailIter.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance tailIter_defined : 𝚺₁-Function₂ (tailIter : V → V → V) via tailIterDef := .mk
  fun v ↦ by simp [TailIter.construction.result_defined_iff, tailIterDef]; rfl
instance tailIter_definable : 𝚺₁-Function₂ (tailIter : V → V → V) := tailIter_defined.to_definable

lemma tailIter_adjoin_natCast (x v : V) : ∀ k : ℕ, tailIter (x ∷ v) ((k : V) + 1) = tailIter v k
  | 0 => by rw [Nat.cast_zero, zero_add, ← zero_add 1, tailIter_succ, tailIter_zero, sndIdx_adjoin, tailIter_zero]
  | k + 1 => by
    rw [Nat.cast_succ, tailIter_succ, tailIter_adjoin_natCast x v k, tailIter_succ]

lemma tailIter_vecOf : ∀ (xs : List V) (k : ℕ), tailIter (vecOf xs) (k : V) = vecOf (xs.drop k)
  | [], k => by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, tailIter_succ, ih]; simp [sndIdx, pi₂_zero]
  | x :: xs, 0 => by simp
  | x :: xs, k + 1 => by rw [Nat.cast_succ, vecOf_cons, tailIter_adjoin_natCast, tailIter_vecOf xs k]; simp

namespace QVecIterV

variable (L)

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y w. y = w”
  succ := .mkSigma “y ih i w. ∃ s, !(qVecGraph L) s ih ∧ y = s”

noncomputable def construction : PR.Construction V (blueprint L) where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ qVec L ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qVec.defined.iff]

end QVecIterV

variable (L) in
/-- `qVecIterV w k = qVec (… (qVec w))` (`k` times) — the V-indexed `qVecIter`. -/
noncomputable def qVecIterV (w k : V) : V := (QVecIterV.construction L).result ![w] k

@[simp] lemma qVecIterV_zero (w : V) : qVecIterV L w 0 = w := by simp [qVecIterV, QVecIterV.construction]
@[simp] lemma qVecIterV_succ (w k : V) : qVecIterV L w (k + 1) = qVec L (qVecIterV L w k) := by
  simp [qVecIterV, QVecIterV.construction]

variable (L) in
noncomputable def qVecIterVDef : 𝚺₁.Semisentence 3 :=
  (QVecIterV.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qVecIterV_defined : 𝚺₁-Function₂[V] qVecIterV L via qVecIterVDef L := .mk
  fun v ↦ by simp [(QVecIterV.construction L).result_defined_iff, qVecIterVDef]; rfl
instance qVecIterV_definable : 𝚺₁-Function₂[V] qVecIterV L := qVecIterV_defined.to_definable

lemma qVecIterV_natCast (w : V) : ∀ n : ℕ, qVecIterV L w (n : V) = qVecIter L n w
  | 0 => by simp
  | n + 1 => by rw [Nat.cast_succ, qVecIterV_succ, qVecIterV_natCast w n, qVecIter_succ, qVecIter_qVec]

namespace QqExss

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y q. y = q”
  succ := .mkSigma “y ih i q. !qqExsDef y ih”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ ^∃ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqExs]

end QqExss

/-- `qqExss q k = ^∃ … ^∃ q` (`k` existential quantifiers) — the V-indexed `exsIter`. -/
noncomputable def qqExss (q k : V) : V := QqExss.construction.result ![q] k

@[simp] lemma qqExss_zero (q : V) : qqExss q 0 = q := by simp [qqExss, QqExss.construction]
@[simp] lemma qqExss_succ (q k : V) : qqExss q (k + 1) = ^∃ (qqExss q k) := by
  simp [qqExss, QqExss.construction]

def qqExssDef : 𝚺₁.Semisentence 3 := QqExss.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqExss_defined : 𝚺₁-Function₂ (qqExss : V → V → V) via qqExssDef := .mk
  fun v ↦ by simp [QqExss.construction.result_defined_iff, qqExssDef]; rfl
instance qqExss_definable : 𝚺₁-Function₂ (qqExss : V → V → V) := qqExss_defined.to_definable

lemma qqExss_natCast (q : V) : ∀ n : ℕ, qqExss q (n : V) = exsIter n q
  | 0 => by simp
  | n + 1 => by rw [Nat.cast_succ, qqExss_succ, qqExss_natCast q n, exsIter_succ]


/-! ### A.3 Horn matrices, instantiation maps, suffix chains on vectors -/

namespace ImpChainV

variable (L)

noncomputable def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y c. y = c”
  adjoin := .mkSigma “y x xs ih c. ∃ s, !(impGraph L) s x ih ∧ y = s”

noncomputable def construction : VecRec.Construction V (blueprint L) where
  nil v := v 0
  adjoin _ x _ ih := imp L x ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, imp.defined.iff]

end ImpChainV

variable (L) in
/-- `impChainV [a₁, …, a_j] c = a₁ → (… → c)` on vectors (`impChain` on lists). -/
noncomputable def impChainV (as c : V) : V := (ImpChainV.construction L).result ![c] as

@[simp] lemma impChainV_nil (c : V) : impChainV L 0 c = c := by simp [impChainV, ImpChainV.construction]
@[simp] lemma impChainV_adjoin (a as c : V) : impChainV L (a ∷ as) c = imp L a (impChainV L as c) := by
  simp [impChainV, ImpChainV.construction]

variable (L) in
noncomputable def impChainVDef : 𝚺₁.Semisentence 3 := (ImpChainV.blueprint L).resultDef

instance impChainV_defined : 𝚺₁-Function₂[V] impChainV L via impChainVDef L := .mk
  fun v ↦ by simp [(ImpChainV.construction L).eval_resultDef, impChainVDef]; rfl
instance impChainV_definable : 𝚺₁-Function₂[V] impChainV L := impChainV_defined.to_definable

lemma impChainV_vecOf : ∀ (as : List V) (c : V), impChainV L (vecOf as) c = impChain L as c
  | [], c => by simp
  | a :: as, c => by simp [impChainV_vecOf as c]

namespace MapSubst

variable (L)

noncomputable def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y w. y = 0”
  adjoin := .mkSigma “y x xs ih w. ∃ z, !(substsGraph L) z w x ∧ !adjoinDef y z ih”

noncomputable def construction : VecRec.Construction V (blueprint L) where
  nil _ := 0
  adjoin v x _ ih := subst L (v 0) x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, subst.defined.iff]

end MapSubst

variable (L) in
/-- `mapSubst w [a₁, …] = [subst w a₁, …]`. -/
noncomputable def mapSubst (w as : V) : V := (MapSubst.construction L).result ![w] as

@[simp] lemma mapSubst_nil (w : V) : mapSubst L w 0 = 0 := by simp [mapSubst, MapSubst.construction]
@[simp] lemma mapSubst_adjoin (w a as : V) : mapSubst L w (a ∷ as) = subst L w a ∷ mapSubst L w as := by
  simp [mapSubst, MapSubst.construction]

variable (L) in
noncomputable def mapSubstDef : 𝚺₁.Semisentence 3 :=
  (MapSubst.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance mapSubst_defined : 𝚺₁-Function₂[V] mapSubst L via mapSubstDef L := .mk
  fun v ↦ by simp [(MapSubst.construction L).eval_resultDef, mapSubstDef]; rfl
instance mapSubst_definable : 𝚺₁-Function₂[V] mapSubst L := mapSubst_defined.to_definable

lemma mapSubst_vecOf (w : V) : ∀ (as : List V), mapSubst L w (vecOf as) = vecOf (as.map (subst L w))
  | [] => by simp
  | a :: as => by simp [mapSubst_vecOf w as]

namespace MapNeg

variable (L)

noncomputable def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. ∃ z, !(negGraph L) z x ∧ !adjoinDef y z ih”

noncomputable def construction : VecRec.Construction V (blueprint L) where
  nil _ := 0
  adjoin _ x _ ih := neg L x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, neg.defined.iff]

end MapNeg

variable (L) in
/-- `mapNeg [a₁, …] = [neg a₁, …]`. -/
noncomputable def mapNeg (as : V) : V := (MapNeg.construction L).result ![] as

@[simp] lemma mapNeg_nil : mapNeg L (0 : V) = 0 := by simp [mapNeg, MapNeg.construction]
@[simp] lemma mapNeg_adjoin (a as : V) : mapNeg L (a ∷ as) = neg L a ∷ mapNeg L as := by
  simp [mapNeg, MapNeg.construction]

variable (L) in
noncomputable def mapNegDef : 𝚺₁.Semisentence 2 := (MapNeg.blueprint L).resultDef

instance mapNeg_defined : 𝚺₁-Function₁[V] mapNeg L via mapNegDef L := (MapNeg.construction L).result_defined
instance mapNeg_definable : 𝚺₁-Function₁[V] mapNeg L := mapNeg_defined.to_definable

lemma mapNeg_vecOf : ∀ (as : List V), mapNeg L (vecOf as) = vecOf (as.map (neg L))
  | [] => by simp
  | a :: as => by simp [mapNeg_vecOf as]

namespace SufChains

variable (L)

noncomputable def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y c. !mkVec₁Def y c”
  adjoin := .mkSigma “y x xs ih c. ∃ h, !nthDef h ih 0 ∧ ∃ b, !(impGraph L) b x h ∧ !adjoinDef y b ih”

noncomputable def construction : VecRec.Construction V (blueprint L) where
  nil v := ?[v 0]
  adjoin _ x _ ih := imp L x ih.[0] ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, imp.defined.iff]

end SufChains

variable (L) in
/-- `sufChains [a₁, …, a_j] c = [impChain [a₁, …, a_j] c, impChain [a₂, …, a_j] c, …, c]` —
the Horn matrices of all suffixes, index `i` = the chain after `i` antecedents. -/
noncomputable def sufChains (as c : V) : V := (SufChains.construction L).result ![c] as

@[simp] lemma sufChains_nil (c : V) : sufChains L 0 c = ?[c] := by simp [sufChains, SufChains.construction]
@[simp] lemma sufChains_adjoin (a as c : V) :
    sufChains L (a ∷ as) c = imp L a (sufChains L as c).[0] ∷ sufChains L as c := by
  simp [sufChains, SufChains.construction]

variable (L) in
noncomputable def sufChainsDef : 𝚺₁.Semisentence 3 := (SufChains.blueprint L).resultDef

instance sufChains_defined : 𝚺₁-Function₂[V] sufChains L via sufChainsDef L := .mk
  fun v ↦ by simp [(SufChains.construction L).eval_resultDef, sufChainsDef]; rfl
instance sufChains_definable : 𝚺₁-Function₂[V] sufChains L := sufChains_defined.to_definable

lemma sufChains_vecOf : ∀ (as : List V) (c : V),
    sufChains L (vecOf as) c = vecOf ((List.range (as.length + 1)).map fun i ↦ impChain L (as.drop i) c)
  | [], c => by simp
  | a :: as, c => by
    rw [vecOf_cons, sufChains_adjoin, sufChains_vecOf as c]
    simp [List.range_succ_eq_map, Function.comp_def]

lemma nth_sufChains_vecOf (as : List V) (c : V) (i : ℕ) (hi : i ≤ as.length) :
    (sufChains L (vecOf as) c).[(i : V)] = impChain L (as.drop i) c := by
  rw [sufChains_vecOf, nth_vecOf _ i (by simpa using Nat.lt_succ_of_le hi)]
  simp

/-! ### A.4 Context vectors and level formulas -/

namespace CtxChain

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y fv S. !mkVec₁Def y S”
  succ := .mkSigma “y ih i fv S. ∃ f, !nthDef f fv i ∧ ∃ l, !nthDef l ih i ∧ ∃ g, !insertDef g f l ∧ !concatDef y ih g”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ ?[v 1]
  succ := fun v i ih ↦ concat ih (insert (v 0).[i] ih.[i])
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end CtxChain

/-- `ctxChain fv S n = [S, insert fv.[0] S, insert fv.[1] (insert fv.[0] S), …]` (`n + 1` entries). -/
noncomputable def ctxChain (fv S n : V) : V := CtxChain.construction.result ![fv, S] n

@[simp] lemma ctxChain_zero (fv S : V) : ctxChain fv S 0 = ?[S] := by simp [ctxChain, CtxChain.construction]
@[simp] lemma ctxChain_succ (fv S n : V) :
    ctxChain fv S (n + 1) = concat (ctxChain fv S n) (insert fv.[n] (ctxChain fv S n).[n]) := by
  simp [ctxChain, CtxChain.construction]

def ctxChainDef : 𝚺₁.Semisentence 4 := CtxChain.blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance ctxChain_defined : 𝚺₁-Function₃ (ctxChain : V → V → V → V) via ctxChainDef := .mk
  fun v ↦ by simp [CtxChain.construction.result_defined_iff, ctxChainDef]; rfl
instance ctxChain_definable : 𝚺₁-Function₃ (ctxChain : V → V → V → V) := ctxChain_defined.to_definable

/-- The Lean-level context sequence: `ctxL fv S 0 = S`, `ctxL fv S (i + 1) = insert fv.[i] (ctxL fv S i)`. -/
noncomputable def ctxL (fv S : V) : ℕ → V
  | 0 => S
  | i + 1 => insert fv.[(i : V)] (ctxL fv S i)

@[simp] lemma ctxL_zero (fv S : V) : ctxL fv S 0 = S := rfl
@[simp] lemma ctxL_succ (fv S : V) (i : ℕ) : ctxL fv S (i + 1) = insert fv.[(i : V)] (ctxL fv S i) := rfl

lemma len_ctxChain_natCast (fv S : V) : ∀ n : ℕ, len (ctxChain fv S (n : V)) = (n : V) + 1
  | 0 => by simp
  | n + 1 => by rw [Nat.cast_succ, ctxChain_succ, len_concat, len_ctxChain_natCast fv S n]

lemma nth_ctxChain_natCast (fv S : V) : ∀ (n i : ℕ), i ≤ n → (ctxChain fv S (n : V)).[(i : V)] = ctxL fv S i
  | 0, 0, _ => by simp
  | n + 1, i, hi => by
    rw [Nat.cast_succ, ctxChain_succ]
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · rw [concat_nth_lt _ _ (by rw [len_ctxChain_natCast]; exact_mod_cast h)]
      exact nth_ctxChain_natCast fv S n i (Nat.lt_succ_iff.mp h)
    · have hi' : i = n + 1 := le_antisymm hi h
      subst hi'
      rw [concat_nth_len' _ _ (by rw [len_ctxChain_natCast]; push_cast; rfl)]
      rw [nth_ctxChain_natCast fv S n n le_rfl]
      simp

/-- The `k`-th entry from the END: `nthFromEnd v k = v.[len v - k - 1]`. -/
noncomputable def nthFromEnd (v k : V) : V := (takeLast v (k + 1)).[0]

lemma nthFromEnd_eq {v k a : V} (h : len v = a + (k + 1)) : nthFromEnd v k = v.[a] := by
  have hk : k < len v := by rw [h]; exact lt_of_lt_of_le (by simp) le_add_self
  rw [nthFromEnd, takeLast_succ_of_lt hk, nth_adjoin_zero, h, add_tsub_cancel_right]

def nthFromEndDef : 𝚺₁.Semisentence 3 := .mkSigma “y v k. ∃ t, !takeLastDef t v (k + 1) ∧ !nthDef y t 0”

instance nthFromEnd_defined : 𝚺₁-Function₂ (nthFromEnd : V → V → V) via nthFromEndDef := .mk
  fun v ↦ by simp [nthFromEndDef, nthFromEnd]
instance nthFromEnd_definable : 𝚺₁-Function₂ (nthFromEnd : V → V → V) := nthFromEnd_defined.to_definable

namespace LevelF

variable (L)

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w q. ∃ z, !(substsGraph L) z w q ∧ !mkVec₁Def y z”
  succ := .mkSigma “y ih k w q. ∃ t, !tailIterDef t w (k + 1) ∧ ∃ v, !(qVecIterVDef L) v t (k + 1) ∧
    ∃ z, !(substsGraph L) z v q ∧ ∃ f, !qqExssDef f z (k + 1) ∧ !adjoinDef y f ih”

noncomputable def construction : PR.Construction V (blueprint L) where
  zero := fun v ↦ ?[subst L (v 0) (v 1)]
  succ := fun v k ih ↦ qqExss (subst L (qVecIterV L (tailIter (v 0) (k + 1)) (k + 1)) (v 1)) (k + 1) ∷ ih
  zero_defined := .mk fun v ↦ by simp [blueprint, subst.defined.iff]
  succ_defined := .mk fun v ↦ by
    simp [blueprint, subst.defined.iff, tailIter_defined.iff, qVecIterV_defined.iff, qqExss_defined.iff]

end LevelF

variable (L) in
/-- The body at `k` remaining quantifiers: `q[#k ↦ w.[k], …, #(m-1) ↦ w.[m-1]]` (`#0, …, #(k-1)` kept). -/
noncomputable def levelBody (w q k : V) : V := subst L (qVecIterV L (tailIter w k) k) q

variable (L) in
/-- The level formula with `k` remaining quantifiers: `∃^k (levelBody w q k)`. -/
noncomputable def levelFormula (w q k : V) : V := qqExss (levelBody L w q k) k

variable (L) in
/-- `levelF w q m = [levelFormula w q m, …, levelFormula w q 0]` — index `i` has `m - i`
remaining quantifiers. -/
noncomputable def levelF (w q m : V) : V := (LevelF.construction L).result ![w, q] m

@[simp] lemma levelF_zero (w q : V) : levelF L w q 0 = ?[subst L w q] := by
  simp [levelF, LevelF.construction]
@[simp] lemma levelF_succ (w q m : V) : levelF L w q (m + 1) = levelFormula L w q (m + 1) ∷ levelF L w q m := by
  simp [levelF, LevelF.construction, levelFormula, levelBody]

variable (L) in
noncomputable def levelFDef : 𝚺₁.Semisentence 4 :=
  (LevelF.blueprint L).resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance levelF_defined : 𝚺₁-Function₃[V] levelF L via levelFDef L := .mk
  fun v ↦ by simp [(LevelF.construction L).result_defined_iff, levelFDef]; rfl
instance levelF_definable : 𝚺₁-Function₃[V] levelF L := levelF_defined.to_definable

@[simp] lemma levelFormula_zero (w q : V) : levelFormula L w q 0 = subst L w q := by simp [levelFormula, levelBody]

lemma len_levelF_natCast (w q : V) : ∀ m : ℕ, len (levelF L w q (m : V)) = (m : V) + 1
  | 0 => by simp
  | m + 1 => by rw [Nat.cast_succ, levelF_succ, len_adjoin, len_levelF_natCast w q m]

lemma nth_levelF_natCast (w q : V) : ∀ (m i : ℕ), i ≤ m →
    (levelF L w q (m : V)).[(i : V)] = levelFormula L w q ((m - i : ℕ) : V)
  | 0, 0, _ => by simp
  | m + 1, 0, _ => by rw [Nat.cast_succ, levelF_succ, Nat.cast_zero, nth_adjoin_zero]; simp
  | m + 1, i + 1, hi => by
    rw [Nat.cast_succ, levelF_succ, Nat.cast_succ, nth_adjoin_succ,
      nth_levelF_natCast w q m i (Nat.le_of_succ_le_succ hi)]
    simp

/-! ### A.5 `instOuter` is ONE simultaneous substitution -/

/-- The entries of `qVecIter n (e ∷ 0)`: `#i` below `n`, the closed `e` at `n`. -/
lemma nth_qVecIter_single {e : V} (he : IsTerm L e) : ∀ (n : ℕ) (i : V), i < (n : V) + 1 →
    (qVecIter L n (e ∷ (0 : V))).[i] = if i < (n : V) then ^#i else e
  | 0, i, hi => by
    have : i = 0 := by simpa [lt_one_iff_eq_zero] using hi
    subst this; simp
  | n + 1, i, hi => by
    have hv : IsSemitermVec L ((n : V) + 1) (n : V) (qVecIter L n (e ∷ (0 : V))) :=
      isSemitermVec_qVecIter_single he
    rw [qVecIter_succ, qVecIter_qVec]
    rcases eq_zero_or_pos i with rfl | hpos
    · simp [qVec]
    · obtain ⟨j, rfl⟩ := eq_succ_of_pos hpos
      have hj : j < (n : V) + 1 := by
        rw [Nat.cast_succ] at hi; exact lt_of_add_lt_add_right hi
      rw [Nat.cast_succ]
      simp only [qVec, nth_adjoin_succ]
      rw [hv.lh, nth_termBShiftVec hv.isUTerm hj, nth_qVecIter_single he n j hj]
      by_cases h : j < (n : V)
      · simp [h]
      · have : j = (n : V) := by
          rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with h' | h'
          · exact absurd h' h
          · exact h'
        subst this
        simp [termBShift_eq_self_of_closed he]

/-- The entries of `qVecIter k 0`: the identity vector `#0, …, #(k-1)`. -/
lemma nth_qVecIter_nil : ∀ (k : ℕ) (i : V), i < (k : V) → (qVecIter L k (0 : V)).[i] = ^#i
  | 0, i, hi => by simp at hi
  | k + 1, i, hi => by
    have hv : IsSemitermVec L (0 + (k : V)) (0 + (k : V)) (qVecIter L k (0 : V)) :=
      isSemitermVec_qVecIter (IsSemitermVec.nil 0)
    rw [qVecIter_succ, qVecIter_qVec]
    rcases eq_zero_or_pos i with rfl | hpos
    · simp [qVec]
    · obtain ⟨j, rfl⟩ := eq_succ_of_pos hpos
      have hj : j < (k : V) := by
        rw [Nat.cast_succ] at hi; exact lt_of_add_lt_add_right hi
      simp only [qVec, nth_adjoin_succ]
      rw [hv.lh, nth_termBShiftVec hv.isUTerm (by simpa using hj), nth_qVecIter_nil k j hj,
        termBShift_bvar]

/-- The identity substitution: `subst ?[#0, …, #(k-1)] q = q` for a `k`-semiformula. -/
lemma subst_qVecIter_nil {k : ℕ} {q : V} (hq : IsSemiformula L (k : V) q) :
    subst L (qVecIter L k (0 : V)) q = q := by
  have hv : IsSemitermVec L (k : V) (k : V) (qVecIter L k (0 : V)) := by
    have := isSemitermVec_qVecIter (L := L) (n := k) (IsSemitermVec.nil (L := L) (V := V) 0)
    simpa using this
  exact subst_eq_self hq hv (nth_qVecIter_nil k)

/-- **The composition law**: substituting the outermost variable into a `k`-deep vector
instantiation appends the witness: `qVecIter k W ∘ qVecIter (n + k) (e ∷ 0) = qVecIter k (concat W e)`. -/
lemma termSubstVec_qVecIter_single {W e : V} {n : ℕ} (hW : IsSemitermVec L (n : V) 0 W) (he : IsTerm L e) :
    ∀ k : ℕ, termSubstVec L (((n + k : ℕ) : V) + 1) (qVecIter L k W) (qVecIter L (n + k) (e ∷ (0 : V)))
      = qVecIter L k (concat W e)
  | 0 => by
    have hv : IsSemitermVec L ((n : V) + 1) (n : V) (qVecIter L n (e ∷ (0 : V))) :=
      isSemitermVec_qVecIter_single he
    simp only [Nat.add_zero, qVecIter_zero]
    apply nth_ext' ((n : V) + 1)
    · rw [len_termSubstVec hv.isUTerm]
    · rw [len_concat, hW.lh]
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, nth_qVecIter_single he n i hi]
    by_cases h : i < (n : V)
    · rw [if_pos h, termSubst_bvar, concat_nth_lt _ _ (by rw [hW.lh]; exact h)]
    · have : i = (n : V) := by
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with h' | h'
        · exact absurd h' h
        · exact h'
      subst this
      rw [if_neg h, termSubst_eq_self_of_closed he, concat_nth_len' _ _ hW.lh]
  | k + 1 => by
    have hv : IsSemitermVec L (((n + k : ℕ) : V) + 1) ((n + k : ℕ) : V) (qVecIter L (n + k) (e ∷ (0 : V))) :=
      isSemitermVec_qVecIter_single he
    have hw : IsSemitermVec L ((n + k : ℕ) : V) (0 + (k : V)) (qVecIter L k W) := by
      have := isSemitermVec_qVecIter (L := L) (n := k) hW
      rwa [← Nat.cast_add] at this
    rw [show n + (k + 1) = (n + k) + 1 by ring, qVecIter_succ, qVecIter_qVec, qVecIter_succ, qVecIter_qVec]
    have := termSubstVec_qVec_qVec (L := L) hv hw
    rw [show (((n + k + 1 : ℕ) : V) + 1) = (((n + k : ℕ) : V) + 1) + 1 by push_cast; ring, this,
      termSubstVec_qVecIter_single hW he k, qVecIter_succ, qVecIter_qVec]

lemma isSemitermVec_vecOf_closed : ∀ (es : List V), (∀ e ∈ es, IsTerm L e) →
    IsSemitermVec L (es.length : V) 0 (vecOf es)
  | [], _ => by simp
  | e :: es, hes => by
    rw [vecOf_cons, List.length_cons, Nat.cast_succ]
    exact IsSemitermVec.adjoin (isSemitermVec_vecOf_closed es (fun e' h ↦ hes e' (by simp [h]))) (hes e (by simp))

/-- **`instOuterAt k es q` is one simultaneous substitution**: the witnesses reversed (innermost
first) under `k` bound variables. -/
theorem instOuterAt_eq_subst (k : ℕ) : ∀ (es : List V) {q : V},
    IsSemiformula L ((es.length + k : ℕ) : V) q → (∀ e ∈ es, IsTerm L e) →
    instOuterAt L k es q = subst L (qVecIter L k (vecOf es.reverse)) q
  | [], q, hq, _ => by
    rw [instOuterAt_nil, List.reverse_nil, vecOf_nil]
    -- `subst (qVecIter k 0) q = q`: the identity substitution on a `k`-semiformula
    have hq0 : IsSemiformula L (k : V) q := by simpa using hq
    exact (subst_qVecIter_nil hq0).symm
  | e :: es, q, hq, hes => by
    have he : IsTerm L e := hes e (by simp)
    have hes' : ∀ e' ∈ es, IsTerm L e' := fun e' h ↦ hes e' (by simp [h])
    have hq' : IsSemiformula L (((es.length + k : ℕ) : V) + 1) q := by
      rw [show ((es.length + k : ℕ) : V) + 1 = (((e :: es).length + k : ℕ) : V) by
        simp only [List.length_cons]; push_cast; ring]
      exact hq
    rw [instOuterAt_cons, instOuterAt_eq_subst k es (isSemiformula_subOuter hq' he) hes']
    unfold subOuter
    have hW : IsSemitermVec L (es.length : V) 0 (vecOf es.reverse) := by
      have := isSemitermVec_vecOf_closed es.reverse (fun e' h ↦ hes' e' (List.mem_reverse.mp h))
      simpa using this
    have hv : IsSemitermVec L (((es.length + k : ℕ) : V) + 1) ((es.length + k : ℕ) : V)
        (qVecIter L (es.length + k) (e ∷ (0 : V))) := isSemitermVec_qVecIter_single he
    have hw : IsSemitermVec L ((es.length : V) + (k : V)) (0 + (k : V)) (qVecIter L k (vecOf es.reverse)) :=
      isSemitermVec_qVecIter hW
    rw [substs_substs hq' (by simpa [Nat.cast_add] using hw) hv,
      termSubstVec_qVecIter_single hW he k, concat_vecOf, ← List.reverse_cons]


/-! ### A.6 The `exsIntro` chain and the Horn closing chain on vectors -/

namespace ExsBuild

variable (L)

/-- Parameters `w q C d`: `w` the reversed witnesses, `q` the matrix, `C = [Γ₀, …, Γ_m]` the
context vector, `d` the continuation. -/
noncomputable def blueprint : VecRec.Blueprint 4 where
  nil := .mkSigma “y w q C d. ∃ z, !(substsGraph L) z w q ∧ ∃ t, !takeLastDef t C 1 ∧ ∃ g, !nthDef g t 0 ∧
    ∃ s, !insertDef s z g ∧ !wkRuleGraph y s d”
  adjoin := .mkSigma “y x xs ih w q C d. ∃ n, !lenDef n xs ∧ ∃ t, !tailIterDef t w (n + 1) ∧
    ∃ v, !(qVecIterVDef L) v t (n + 1) ∧ ∃ z, !(substsGraph L) z v q ∧ ∃ p, !qqExssDef p z n ∧
    ∃ f, !qqExsDef f p ∧ ∃ tc, !takeLastDef tc C (n + 1 + 1) ∧ ∃ g, !nthDef g tc 0 ∧
    ∃ s, !insertDef s f g ∧ !exsIntroGraph y s p x ih”

noncomputable def construction : VecRec.Construction V (blueprint L) where
  nil v := wkRule (insert (subst L (v 0) (v 1)) (nthFromEnd (v 2) 0)) (v 3)
  adjoin v x xs ih :=
    exsIntro (insert (^∃ (qqExss (levelBody L (v 0) (v 1) (len xs + 1)) (len xs))) (nthFromEnd (v 2) (len xs + 1)))
      (qqExss (levelBody L (v 0) (v 1) (len xs + 1)) (len xs)) x ih
  nil_defined := .mk fun v ↦ by simp [blueprint, nthFromEnd, subst.defined.iff]
  adjoin_defined := .mk fun v ↦ by
    simp [blueprint, nthFromEnd, levelBody, subst.defined.iff, tailIter_defined.iff, qVecIterV_defined.iff,
      qqExss_defined.iff, qqExs]

end ExsBuild

variable (L) in
/-- The chain of `exsIntro`s on vectors: `exsChainV ev q Γ d` with `ev` the witnesses outermost
first (`exsChainCode` on lists, `exsChainV_vecOf`). -/
noncomputable def exsChainV (ev q Γ d : V) : V :=
  (ExsBuild.construction L).result
    ![revV ev, q, ctxChain (levelF L (revV ev) q (len ev)) Γ (len ev), d] ev

namespace HornBuild

variable (L)

/-- Parameters `c C d`: the (instantiated) conclusion, the context vector `[S₀, …, S_j]`, the
continuation. -/
noncomputable def blueprint : VecRec.Blueprint 3 where
  nil := .mkSigma “y c C d. ∃ n, !(negGraph L) n c ∧ ∃ t, !takeLastDef t C 1 ∧ ∃ g, !nthDef g t 0 ∧
    ∃ s, !insertDef s n g ∧ !wkRuleGraph y s d”
  adjoin := .mkSigma “y x xs ih c C d. ∃ n, !lenDef n xs ∧ ∃ t, !takeLastDef t C (n + 1) ∧ ∃ S, !nthDef S t 0 ∧
    ∃ b, !(impChainVDef L) b xs c ∧ ∃ nb, !(negGraph L) nb b ∧ ∃ s, !insertDef s x S ∧
    ∃ l, !axLGraph l s x ∧ !andIntroGraph y S x nb l ih”

noncomputable def construction : VecRec.Construction V (blueprint L) where
  nil v := wkRule (insert (neg L (v 0)) (nthFromEnd (v 1) 0)) (v 2)
  adjoin v x xs ih :=
    andIntro (nthFromEnd (v 1) (len xs)) x (neg L (impChainV L xs (v 0)))
      (axL (insert x (nthFromEnd (v 1) (len xs))) x) ih
  nil_defined := .mk fun v ↦ by simp [blueprint, nthFromEnd, neg.defined.iff]
  adjoin_defined := .mk fun v ↦ by
    simp [blueprint, nthFromEnd, neg.defined.iff, impChainV_defined.iff]

end HornBuild

variable (L) in
/-- The Horn closing chain on vectors (`hornClose` on lists, `hornCloseV_vecOf`). -/
noncomputable def hornCloseV (as c S d : V) : V :=
  (HornBuild.construction L).result ![c, ctxChain (mapNeg L (sufChains L as c)) S (len as), d] as

variable (L) in
/-- `useLemmaCode` on vectors. -/
noncomputable def useLemmaV (Γ ev B dΛ d : V) : V :=
  cutRule Γ (qqAlls B (len ev)) (wkRule (insert (qqAlls B (len ev)) Γ) dΛ) (exsChainV L ev (neg L B) Γ d)

variable (L) in
/-- `useHornCode` on vectors: row antecedents `as`, conclusion `c`, witnesses `ev` (outermost first). -/
noncomputable def useHornV (Γ ev as c dΛ d : V) : V :=
  useLemmaV L Γ ev (impChainV L as c) dΛ
    (hornCloseV L (mapSubst L (revV ev) as) (subst L (revV ev) c) Γ d)

variable (L) in
/-- `useHornAndCode` on vectors (`c₁ ⋏ c₂` the conclusion). -/
noncomputable def useHornAndV (Γ ev as c₁ c₂ dΛ d : V) : V :=
  useHornV L Γ ev as (c₁ ^⋏ c₂) dΛ (splitAndCode L Γ (subst L (revV ev) c₁) (subst L (revV ev) c₂) d)

variable (L) in
/-- `introFactCode` on vectors (`^∃ R` the conclusion). -/
noncomputable def introFactV (Γ ev as R dΛ d : V) : V :=
  elimExistsCode L Γ (subst L (qVec L (revV ev)) R)
    (useHornV L (insert (^∃ (subst L (qVec L (revV ev)) R)) Γ) ev as (^∃ R) dΛ
      (axL (insert (neg L (^∃ (subst L (qVec L (revV ev)) R))) (insert (^∃ (subst L (qVec L (revV ev)) R)) Γ))
        (^∃ (subst L (qVec L (revV ev)) R))))
    d

/-! ### A.7 The vector constructors agree with the list constructors -/

/-- Appending a witness at the END instantiates the outermost remaining variable. -/
lemma instOuterAt_append (k : ℕ) : ∀ (pre : List V) (e q : V),
    instOuterAt L k (pre ++ [e]) q = subOuter L k e (instOuterAt L (k + 1) pre q)
  | [], e, q => by simp
  | p :: pre, e, q => by
    rw [List.cons_append, instOuterAt_cons, instOuterAt_append k pre e, instOuterAt_cons,
      List.length_append, List.length_singleton, show pre.length + 1 + k = pre.length + (k + 1) by omega]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma drop_reverse_append (pre rest : List V) :
    (pre ++ rest).reverse.drop rest.length = pre.reverse := by
  rw [List.reverse_append, List.drop_left' (by simp)]

/-- The `exsIntro` chain, suffix by suffix: at the suffix `rest` of `es = pre ++ rest` the
vector chain is the list chain on `rest` at the partial instance and the context of depth
`pre.length`. -/
lemma exsBuild_vecOf (es : List V) {q : V} (hq : IsSemiformula L (es.length : V) q)
    (hes : ∀ e ∈ es, IsTerm L e) (Γ d : V) : ∀ (rest pre : List V), es = pre ++ rest →
    (ExsBuild.construction L).result
      ![vecOf es.reverse, q, ctxChain (levelF L (vecOf es.reverse) q es.length) Γ es.length, d] (vecOf rest)
      = exsChainCode L rest (instOuterAt L rest.length pre q)
          (ctxL (levelF L (vecOf es.reverse) q es.length) Γ pre.length) d
  | [], pre, hpre => by
    rw [List.append_nil] at hpre
    subst hpre
    rw [vecOf_nil, VecRec.Construction.result_nil, exsChainCode_nil]
    simp only [ExsBuild.construction, Matrix.cons_val, List.length_nil]
    rw [instOuterAt_eq_subst 0 es (by simpa using hq) hes, qVecIter_zero,
      nthFromEnd_eq (a := (es.length : V)) (by rw [len_ctxChain_natCast]; simp),
      nth_ctxChain_natCast _ _ es.length es.length le_rfl]
  | e :: rest, pre, hpre => by
    have hes' : ∀ e' ∈ pre, IsTerm L e' := fun e' h ↦ hes e' (by simp [hpre, h])
    have hlen : es.length = pre.length + (rest.length + 1) := by simp [hpre]
    have hq' : IsSemiformula L ((pre.length + (rest.length + 1) : ℕ) : V) q := by rwa [← hlen]
    have ih := exsBuild_vecOf es hq hes Γ d rest (pre ++ [e]) (by simp [hpre])
    rw [vecOf_cons, VecRec.Construction.result_adjoin, ih, exsChainCode_cons, List.length_append,
      List.length_singleton, instOuterAt_append]
    simp only [ExsBuild.construction, Matrix.cons_val, len_vecOf, levelBody, List.length_cons]
    -- the partial instance at depth `pre.length`
    have hz : subst L (qVecIterV L (tailIter (vecOf es.reverse) ((rest.length : V) + 1)) ((rest.length : V) + 1)) q
        = instOuterAt L (rest.length + 1) pre q := by
      have hd : (pre ++ e :: rest).reverse.drop (rest.length + 1) = pre.reverse := by
        simpa using drop_reverse_append pre (e :: rest)
      rw [instOuterAt_eq_subst (rest.length + 1) pre hq' hes', ← Nat.cast_add_one, tailIter_vecOf,
        qVecIterV_natCast, hpre, hd]
    -- the level formula at index `pre.length`
    have hF : (levelF L (vecOf es.reverse) q (es.length : V)).[(pre.length : V)]
        = ^∃ (qqExss (instOuterAt L (rest.length + 1) pre q) (rest.length : V)) := by
      rw [nth_levelF_natCast _ _ es.length pre.length (by omega),
        show es.length - pre.length = rest.length + 1 by omega, levelFormula, levelBody, Nat.cast_succ,
        qqExss_succ, hz]
    -- the context at depth `pre.length`
    have hC : nthFromEnd (ctxChain (levelF L (vecOf es.reverse) q (es.length : V)) Γ (es.length : V))
        ((rest.length : V) + 1) = ctxL (levelF L (vecOf es.reverse) q (es.length : V)) Γ pre.length := by
      rw [nthFromEnd_eq (a := (pre.length : V)) (by rw [len_ctxChain_natCast, hlen]; push_cast; ring),
        nth_ctxChain_natCast _ _ es.length pre.length (by omega)]
    rw [hz, hC, ctxL_succ, hF, qqExss_natCast, ← exsIter_succ]

/-- **The `exsIntro` chain on vectors is the list chain.** -/
theorem exsChainV_vecOf (es : List V) {q : V} (hq : IsSemiformula L (es.length : V) q)
    (hes : ∀ e ∈ es, IsTerm L e) (Γ d : V) :
    exsChainV L (vecOf es) q Γ d = exsChainCode L es q Γ d := by
  unfold exsChainV
  rw [revV_vecOf, len_vecOf]
  have := exsBuild_vecOf es hq hes Γ d es [] rfl
  rw [List.length_nil, ctxL_zero, instOuterAt_nil] at this
  exact this

/-- The Horn closing chain, suffix by suffix. -/
lemma hornBuild_vecOf (as : List V) (c S d : V) : ∀ (rest pre : List V), as = pre ++ rest →
    (HornBuild.construction L).result
      ![c, ctxChain (mapNeg L (sufChains L (vecOf as) c)) S as.length, d] (vecOf rest)
      = hornClose L rest c (ctxL (mapNeg L (sufChains L (vecOf as) c)) S pre.length) d
  | [], pre, hpre => by
    rw [List.append_nil] at hpre
    subst hpre
    rw [vecOf_nil, VecRec.Construction.result_nil, hornClose_nil]
    simp only [HornBuild.construction, Matrix.cons_val]
    rw [nthFromEnd_eq (a := (as.length : V)) (by rw [len_ctxChain_natCast]; simp),
      nth_ctxChain_natCast _ _ as.length as.length le_rfl]
  | a :: rest, pre, hpre => by
    have hlen : as.length = pre.length + (rest.length + 1) := by simp [hpre]
    have ih := hornBuild_vecOf as c S d rest (pre ++ [a]) (by simp [hpre])
    rw [vecOf_cons, VecRec.Construction.result_adjoin, ih, hornClose_cons, List.length_append,
      List.length_singleton]
    simp only [HornBuild.construction, Matrix.cons_val, len_vecOf, impChainV_vecOf]
    have hN : (mapNeg L (sufChains L (vecOf as) c)).[(pre.length : V)] = neg L (impChain L (a :: rest) c) := by
      rw [sufChains_vecOf, mapNeg_vecOf, List.map_map, nth_vecOf _ pre.length (by simp; omega)]
      simp [hpre]
    have hC : nthFromEnd (ctxChain (mapNeg L (sufChains L (vecOf as) c)) S (as.length : V)) (rest.length : V)
        = ctxL (mapNeg L (sufChains L (vecOf as) c)) S (pre.length + 1) := by
      rw [nthFromEnd_eq (a := ((pre.length + 1 : ℕ) : V)) (by rw [len_ctxChain_natCast, hlen]; push_cast; ring),
        nth_ctxChain_natCast _ _ as.length (pre.length + 1) (by omega)]
    rw [hC, ctxL_succ, hN]

/-- **The Horn closing chain on vectors is the list chain.** -/
theorem hornCloseV_vecOf (as : List V) (c S d : V) :
    hornCloseV L (vecOf as) c S d = hornClose L as c S d := by
  unfold hornCloseV
  rw [len_vecOf]
  have := hornBuild_vecOf (L := L) as c S d as [] rfl
  rw [List.length_nil, ctxL_zero] at this
  exact this

theorem useLemmaV_vecOf (Γ : V) (es : List V) {B : V} (hB : IsSemiformula L (es.length : V) B)
    (hes : ∀ e ∈ es, IsTerm L e) (dΛ d : V) :
    useLemmaV L Γ (vecOf es) B dΛ d = useLemmaCode L Γ es B dΛ d := by
  unfold useLemmaV useLemmaCode
  rw [len_vecOf, qqAlls_natCast, exsChainV_vecOf es hB.neg hes]

/-- `subst (revV (vecOf es)) = instOuter es` on `es.length`-semiformulas. -/
lemma subst_revV_vecOf (es : List V) {q : V} (hq : IsSemiformula L (es.length : V) q)
    (hes : ∀ e ∈ es, IsTerm L e) : subst L (revV (vecOf es)) q = instOuter L es q := by
  rw [revV_vecOf, ← instOuterAt_zero, instOuterAt_eq_subst 0 es (by simpa using hq) hes, qVecIter_zero]

/-- `subst (qVec (revV (vecOf es))) = instOuterAt 1 es` on `(es.length + 1)`-semiformulas. -/
lemma subst_qVec_revV_vecOf (es : List V) {R : V} (hR : IsSemiformula L ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsTerm L e) : subst L (qVec L (revV (vecOf es))) R = instOuterAt L 1 es R := by
  rw [revV_vecOf, instOuterAt_eq_subst 1 es (by simpa [Nat.cast_succ] using hR) hes]
  rfl

theorem useHornV_vecOf (Γ : V) (es as : List V) {c : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a) (hc : IsSemiformula L (es.length : V) c)
    (hes : ∀ e ∈ es, IsTerm L e) (dΛ d : V) :
    useHornV L Γ (vecOf es) (vecOf as) c dΛ d = useHornCode L Γ es as c dΛ d := by
  unfold useHornV useHornCode
  rw [impChainV_vecOf, mapSubst_vecOf, subst_revV_vecOf es hc hes, hornCloseV_vecOf,
    useLemmaV_vecOf Γ es (isSemiformula_impChain has hc) hes]
  have hmap : as.map (subst L (revV (vecOf es))) = as.map (instOuter L es) :=
    List.map_congr_left fun a ha ↦ subst_revV_vecOf es (has a ha) hes
  rw [hmap]

theorem useHornAndV_vecOf (Γ : V) (es as : List V) {c₁ c₂ : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a)
    (hc₁ : IsSemiformula L (es.length : V) c₁) (hc₂ : IsSemiformula L (es.length : V) c₂)
    (hes : ∀ e ∈ es, IsTerm L e) (dΛ d : V) :
    useHornAndV L Γ (vecOf es) (vecOf as) c₁ c₂ dΛ d = useHornAndCode L Γ es as c₁ c₂ dΛ d := by
  unfold useHornAndV useHornAndCode
  rw [subst_revV_vecOf es hc₁ hes, subst_revV_vecOf es hc₂ hes,
    useHornV_vecOf Γ es as has (by simp [hc₁, hc₂]) hes]

theorem introFactV_vecOf (Γ : V) (es as : List V) {R : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a) (hR : IsSemiformula L ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsTerm L e) (dΛ d : V) :
    introFactV L Γ (vecOf es) (vecOf as) R dΛ d = introFactCode L Γ es as R dΛ d := by
  unfold introFactV introFactCode
  rw [subst_qVec_revV_vecOf es hR hes, useHornV_vecOf _ es as has (by simp [hR]) hes]

/-! ## Part B — the step language, contexts, and the primitive-recursive chain -/

/-! ### B.1 Named Σ₁ graphs of the vector constructors (cited by name in the blueprints below) -/

variable (L) in
noncomputable def exsChainVDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y ev q Γ d. ∃ r, !revVDef r ev ∧ ∃ n, !lenDef n ev ∧ ∃ f, !(levelFDef L) f r q n ∧
    ∃ C, !ctxChainDef C f Γ n ∧ !(ExsBuild.blueprint L).resultDef y ev r q C d”

instance exsChainV_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ exsChainV L (v 0) (v 1) (v 2) (v 3)) (exsChainVDef L) := .mk
  fun v ↦ by
    simp [exsChainVDef, revV_defined.iff, levelF_defined.iff, ctxChain_defined.iff,
      (ExsBuild.construction L).eval_resultDef]
    rfl

variable (L) in
noncomputable def hornCloseVDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y as c S d. ∃ n, !lenDef n as ∧ ∃ sc, !(sufChainsDef L) sc as c ∧ ∃ m, !(mapNegDef L) m sc ∧
    ∃ C, !ctxChainDef C m S n ∧ !(HornBuild.blueprint L).resultDef y as c C d”

instance hornCloseV_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ hornCloseV L (v 0) (v 1) (v 2) (v 3)) (hornCloseVDef L) := .mk
  fun v ↦ by
    simp [hornCloseVDef, sufChains_defined.iff, mapNeg_defined.iff, ctxChain_defined.iff,
      (HornBuild.construction L).eval_resultDef]
    rfl

variable (L) in
noncomputable def useLemmaVDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y Γ ev B dΛ d. ∃ n, !lenDef n ev ∧ ∃ A, !qqAllsDef A B n ∧ ∃ i, !insertDef i A Γ ∧
    ∃ w, !wkRuleGraph w i dΛ ∧ ∃ nb, !(negGraph L) nb B ∧ ∃ e, !(exsChainVDef L) e ev nb Γ d ∧
    !cutRuleGraph y Γ A w e”

instance useLemmaV_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ useLemmaV L (v 0) (v 1) (v 2) (v 3) (v 4)) (useLemmaVDef L) := .mk
  fun v ↦ by
    simp [useLemmaVDef, qqAlls_defined.iff, neg.defined.iff, exsChainV_defined.iff, useLemmaV]

variable (L) in
noncomputable def useHornVDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Γ ev as c dΛ d. ∃ r, !revVDef r ev ∧ ∃ B, !(impChainVDef L) B as c ∧ ∃ ms, !(mapSubstDef L) ms r as ∧
    ∃ sc, !(substsGraph L) sc r c ∧ ∃ h, !(hornCloseVDef L) h ms sc Γ d ∧ !(useLemmaVDef L) y Γ ev B dΛ h”

instance useHornV_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ useHornV L (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) (useHornVDef L) := .mk
  fun v ↦ by
    simp [useHornVDef, revV_defined.iff, impChainV_defined.iff, mapSubst_defined.iff, subst.defined.iff,
      hornCloseV_defined.iff, useLemmaV_defined.iff, useHornV]

variable (L) in
noncomputable def splitAndCodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y Γ p q d. ∃ np, !(negGraph L) np p ∧ ∃ nq, !(negGraph L) nq q ∧ ∃ o, !qqOrDef o np nq ∧
    ∃ i, !insertDef i o Γ ∧ ∃ i₂, !insertDef i₂ nq i ∧ ∃ i₁, !insertDef i₁ np i₂ ∧
    ∃ w, !wkRuleGraph w i₁ d ∧ !orIntroGraph y i np nq w”

instance splitAndCode_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ splitAndCode L (v 0) (v 1) (v 2) (v 3)) (splitAndCodeDef L) := .mk
  fun v ↦ by simp [splitAndCodeDef, neg.defined.iff, splitAndCode]

variable (L) in
noncomputable def useHornAndVDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y Γ ev as c₁ c₂ dΛ d. ∃ r, !revVDef r ev ∧ ∃ s₁, !(substsGraph L) s₁ r c₁ ∧ ∃ s₂, !(substsGraph L) s₂ r c₂ ∧
    ∃ sp, !(splitAndCodeDef L) sp Γ s₁ s₂ d ∧ ∃ c, !qqAndDef c c₁ c₂ ∧ !(useHornVDef L) y Γ ev as c dΛ sp”

instance useHornAndV_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ useHornAndV L (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      (useHornAndVDef L) := .mk
  fun v ↦ by
    simp [useHornAndVDef, revV_defined.iff, subst.defined.iff, splitAndCode_defined.iff, useHornV_defined.iff,
      useHornAndV]

variable (L) in
noncomputable def elimExistsCodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y Γ P D d. ∃ eP, !qqExsDef eP P ∧ ∃ i, !insertDef i eP Γ ∧ ∃ w₁, !wkRuleGraph w₁ i D ∧
    ∃ nP, !(negGraph L) nP P ∧ ∃ aP, !qqAllDef aP nP ∧ ∃ j, !insertDef j aP Γ ∧ ∃ sh, !(setShiftGraph L) sh j ∧
    ∃ f, !(freeGraph L) f nP ∧ ∃ k, !insertDef k f sh ∧ ∃ w₂, !wkRuleGraph w₂ k d ∧ ∃ a, !allIntroGraph a j nP w₂ ∧
    !cutRuleGraph y Γ eP w₁ a”

instance elimExistsCode_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ elimExistsCode L (v 0) (v 1) (v 2) (v 3)) (elimExistsCodeDef L) := .mk
  fun v ↦ by
    simp [elimExistsCodeDef, neg.defined.iff, setShift.defined.iff, free.defined.iff, elimExistsCode]

variable (L) in
noncomputable def introFactVDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Γ ev as R dΛ d. ∃ r, !revVDef r ev ∧ ∃ qr, !(qVecGraph L) qr r ∧ ∃ P, !(substsGraph L) P qr R ∧
    ∃ eP, !qqExsDef eP P ∧ ∃ i, !insertDef i eP Γ ∧ ∃ nP, !(negGraph L) nP eP ∧ ∃ j, !insertDef j nP i ∧
    ∃ ax, !axLGraph ax j eP ∧ ∃ eR, !qqExsDef eR R ∧ ∃ u, !(useHornVDef L) u i ev as eR dΛ ax ∧
    !(elimExistsCodeDef L) y Γ P u d”

instance introFactV_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ introFactV L (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) (introFactVDef L) := .mk
  fun v ↦ by
    simp [introFactVDef, revV_defined.iff, qVec.defined.iff, subst.defined.iff, neg.defined.iff,
      useHornV_defined.iff, elimExistsCode_defined.iff, introFactV]

/-! ## Part C — tags 6 and 7: the goal-closing leaf `sGoal` and the lemma cut `sLemma`

`DESIGN_fragments.md` §2: a child's fragment is spliced FLAT into its parent's list, so when the
parent needs the child's goal `G_child = ∃ d n, derivation d ∧ fstIdx s d ∧ dlenGraph d n ∧ n ≤ ū`
all four conjuncts are already facts in context, and the only missing move is to package them
and make `G_child` a hypothesis — a `cutRule` whose LEFT premise is a LEAF of constant shape
(`goalLeafCode`: two `exsIntro`s + three `andIntro`s + four `axL`s + one `wkRule`, ten nodes).
Closed numeral facts enter by `sLemma A dA` — a `cutRule` on `A` whose left premise is the
supplied Γ-independent derivation `dA` of `{A}`, weakened; `StepOK` checks `DerivationOf dA {A}`
(Δ₁ through `derivationOf`'s instance — `derivation` is never unfolded).

### C.1 The four predicate codes and the canonical fact codes

`Pderiv = ⌜derivation TAct⌝` (`.sigma`), `PfstIdx = ⌜fstIdxDef⌝`, `Pdlen = ⌜(dlenGraphDef LAct).sigma⌝`,
`Ple = ⌜≤⌝` (the operator's sentence, as `RowInst.Plt`), each embedded along `emb`; the facts are
`subst ?[witnesses] P` in the predicate's own variable order (`RowInst` §2). The goal fact is
`goalFact s ū = ^∃ ^∃ goalBody s ū` with `d = #1` (the outer quantifier) and `n = #0`:
`goalBody s ū = derFact #1 ⋏ (fstIdxFact s #1 ⋏ (dlenFact #1 #0 ⋏ leFact #0 ū))`, and
`instOuter [e, n] (goalBody s ū) = goalInst e n s ū` (`instOuter_goalBody`).
Every Σ₁ graph embeds its predicate as a Gödel numeral `!!(⌜τ⌝)` through the GENERIC
`fact1Def τ`/`fact2Def τ` (proved for a VARIABLE `τ`, never unfolding a closed quote). -/

section partC

open LAct
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

noncomputable def derivS : Semisentence LAct 1 := Semiformula.lMap emb (↑(derivation TAct).sigma : ArithmeticSemisentence 1)
noncomputable def fstIdxS : Semisentence LAct 2 := Semiformula.lMap emb (↑fstIdxDef : ArithmeticSemisentence 2)
noncomputable def dlenS : Semisentence LAct 2 := Semiformula.lMap emb (↑(dlenGraphDef LAct).sigma : ArithmeticSemisentence 2)
noncomputable def leS : Semisentence LAct 2 :=
  Semiformula.lMap emb (Rewriting.emb (Semiformula.Operator.LE.le : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)
noncomputable def Pderiv : V := ⌜derivS⌝
noncomputable def PfstIdx : V := ⌜fstIdxS⌝
noncomputable def Pdlen : V := ⌜dlenS⌝
noncomputable def Ple : V := ⌜leS⌝
lemma isSemiformula_Pderiv : IsSemiformula LAct ((1 : ℕ) : V) Pderiv := Sentence.quote_isSemiformula _
lemma isSemiformula_PfstIdx : IsSemiformula LAct ((2 : ℕ) : V) PfstIdx := Sentence.quote_isSemiformula _
lemma isSemiformula_Pdlen : IsSemiformula LAct ((2 : ℕ) : V) Pdlen := Sentence.quote_isSemiformula _
lemma isSemiformula_Ple : IsSemiformula LAct ((2 : ℕ) : V) Ple := Sentence.quote_isSemiformula _
noncomputable def derFact (e : V) : V := subst LAct (listToVec [e]) Pderiv
noncomputable def fstIdxFact (s e : V) : V := subst LAct (listToVec [s, e]) PfstIdx
noncomputable def dlenFact (e n : V) : V := subst LAct (listToVec [e, n]) Pdlen
noncomputable def leFact (n u : V) : V := subst LAct (listToVec [n, u]) Ple
noncomputable def fact1Def (τ : Semisentence LAct 1) : 𝚺₁.Semisentence 2 := .mkSigma
  “y a. ∃ w, !adjoinDef w a 0 ∧ !(substsGraph LAct) y w !!(⌜τ⌝)”
noncomputable def fact2Def (τ : Semisentence LAct 2) : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ v, !adjoinDef v b 0 ∧ ∃ w, !adjoinDef w a v ∧ !(substsGraph LAct) y w !!(⌜τ⌝)”

lemma fact1_defined (τ : Semisentence LAct 1) :
    𝚺₁-Function₁ (fun a : V ↦ subst LAct (listToVec [a]) (⌜τ⌝ : V)) via fact1Def τ := .mk
  fun v ↦ by simp [fact1Def, subst.defined.iff]
lemma fact2_defined (τ : Semisentence LAct 2) :
    𝚺₁-Function₂ (fun a b : V ↦ subst LAct (listToVec [a, b]) (⌜τ⌝ : V)) via fact2Def τ := .mk
  fun v ↦ by simp [fact2Def, subst.defined.iff]

noncomputable def derFactDef : 𝚺₁.Semisentence 2 := fact1Def derivS
noncomputable def fstIdxFactDef : 𝚺₁.Semisentence 3 := fact2Def fstIdxS
noncomputable def dlenFactDef : 𝚺₁.Semisentence 3 := fact2Def dlenS
noncomputable def leFactDef : 𝚺₁.Semisentence 3 := fact2Def leS

instance derFact_defined : 𝚺₁-Function₁ (derFact : V → V) via derFactDef := fact1_defined derivS
instance fstIdxFact_defined : 𝚺₁-Function₂ (fstIdxFact : V → V → V) via fstIdxFactDef := fact2_defined fstIdxS
instance dlenFact_defined : 𝚺₁-Function₂ (dlenFact : V → V → V) via dlenFactDef := fact2_defined dlenS
instance leFact_defined : 𝚺₁-Function₂ (leFact : V → V → V) via leFactDef := fact2_defined leS
instance derFact_definable : 𝚺₁-Function₁ (derFact : V → V) := derFact_defined.to_definable
instance fstIdxFact_definable : 𝚺₁-Function₂ (fstIdxFact : V → V → V) := fstIdxFact_defined.to_definable
instance dlenFact_definable : 𝚺₁-Function₂ (dlenFact : V → V → V) := dlenFact_defined.to_definable
instance leFact_definable : 𝚺₁-Function₂ (leFact : V → V → V) := leFact_defined.to_definable

/-! ### C.2 The goal fact, its instance, and the leaf `goalLeafCode` -/

noncomputable def goalBody (s u : V) : V :=
  derFact (bv 1) ^⋏ (fstIdxFact s (bv 1) ^⋏ (dlenFact (bv 1) (bv 0) ^⋏ leFact (bv 0) u))
noncomputable def goalFact (s u : V) : V := ^∃ ^∃ goalBody s u
noncomputable def goalInst (e n s u : V) : V :=
  derFact e ^⋏ (fstIdxFact s e ^⋏ (dlenFact e n ^⋏ leFact n u))
noncomputable def goalBodyDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s u. ∃ b1, !qqBvarDef b1 1 ∧ ∃ b0, !qqBvarDef b0 0 ∧ ∃ f1, !derFactDef f1 b1 ∧ ∃ f2, !fstIdxFactDef f2 s b1 ∧
    ∃ f3, !dlenFactDef f3 b1 b0 ∧ ∃ f4, !leFactDef f4 b0 u ∧ ∃ c3, !qqAndDef c3 f3 f4 ∧ ∃ c2, !qqAndDef c2 f2 c3 ∧
    !qqAndDef y f1 c2”
instance goalBody_defined : 𝚺₁-Function₂ (goalBody : V → V → V) via goalBodyDef := .mk
  fun v ↦ by
    simp [goalBodyDef, derFact_defined.iff, fstIdxFact_defined.iff, dlenFact_defined.iff, leFact_defined.iff, goalBody, bv]
instance goalBody_definable : 𝚺₁-Function₂ (goalBody : V → V → V) := goalBody_defined.to_definable

noncomputable def goalFactDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s u. ∃ b, !goalBodyDef b s u ∧ ∃ e1, !qqExsDef e1 b ∧ !qqExsDef y e1”
instance goalFact_defined : 𝚺₁-Function₂ (goalFact : V → V → V) via goalFactDef := .mk
  fun v ↦ by simp [goalFactDef, goalBody_defined.iff, goalFact]
instance goalFact_definable : 𝚺₁-Function₂ (goalFact : V → V → V) := goalFact_defined.to_definable

noncomputable def goalInstDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y e n s u. ∃ f1, !derFactDef f1 e ∧ ∃ f2, !fstIdxFactDef f2 s e ∧ ∃ f3, !dlenFactDef f3 e n ∧
    ∃ f4, !leFactDef f4 n u ∧ ∃ c3, !qqAndDef c3 f3 f4 ∧ ∃ c2, !qqAndDef c2 f2 c3 ∧ !qqAndDef y f1 c2”
instance goalInst_defined : 𝚺₁-Function₄ (goalInst : V → V → V → V → V) via goalInstDef := .mk
  fun v ↦ by
    simp [goalInstDef, derFact_defined.iff, fstIdxFact_defined.iff, dlenFact_defined.iff, leFact_defined.iff, goalInst]

noncomputable def conj4Code (S A₁ A₂ A₃ A₄ : V) : V :=
  andIntro S A₁ (A₂ ^⋏ (A₃ ^⋏ A₄)) (axLFactCode S A₁)
    (andIntro (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S) A₂ (A₃ ^⋏ A₄) (axLFactCode (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S) A₂)
      (andIntro (insert (A₃ ^⋏ A₄) (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S)) A₃ A₄
        (axLFactCode (insert (A₃ ^⋏ A₄) (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S)) A₃)
        (axLFactCode (insert (A₃ ^⋏ A₄) (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S)) A₄)))
noncomputable def conj4CodeDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y S A₁ A₂ A₃ A₄. ∃ r₃, !qqAndDef r₃ A₃ A₄ ∧ ∃ r₂, !qqAndDef r₂ A₂ r₃ ∧ ∃ S₂, !insertDef S₂ r₂ S ∧
    ∃ S₃, !insertDef S₃ r₃ S₂ ∧ ∃ i₁, !insertDef i₁ A₁ S ∧ ∃ x₁, !axLGraph x₁ i₁ A₁ ∧
    ∃ i₂, !insertDef i₂ A₂ S₂ ∧ ∃ x₂, !axLGraph x₂ i₂ A₂ ∧ ∃ i₃, !insertDef i₃ A₃ S₃ ∧ ∃ x₃, !axLGraph x₃ i₃ A₃ ∧
    ∃ i₄, !insertDef i₄ A₄ S₃ ∧ ∃ x₄, !axLGraph x₄ i₄ A₄ ∧ ∃ d₃, !andIntroGraph d₃ S₃ A₃ A₄ x₃ x₄ ∧
    ∃ d₂, !andIntroGraph d₂ S₂ A₂ r₃ x₂ d₃ ∧ !andIntroGraph y S A₁ r₂ x₁ d₂”
instance conj4Code_defined : 𝚺₁-Function₅ (conj4Code : V → V → V → V → V → V) via conj4CodeDef := .mk
  fun v ↦ by simp [conj4CodeDef, conj4Code, axLFactCode]

noncomputable def goalLeafCode (Γ e n s u : V) : V :=
  exsChainV LAct (e ∷ n ∷ 0) (goalBody s u) Γ
    (conj4Code (insert (goalInst e n s u) Γ) (derFact e) (fstIdxFact s e) (dlenFact e n) (leFact n u))

noncomputable def goalLeafCodeDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y Γ e n s u. ∃ B, !goalBodyDef B s u ∧ ∃ M, !goalInstDef M e n s u ∧ ∃ S, !insertDef S M Γ ∧
    ∃ f₁, !derFactDef f₁ e ∧ ∃ f₂, !fstIdxFactDef f₂ s e ∧ ∃ f₃, !dlenFactDef f₃ e n ∧ ∃ f₄, !leFactDef f₄ n u ∧
    ∃ d, !conj4CodeDef d S f₁ f₂ f₃ f₄ ∧ ∃ v, !adjoinDef v n 0 ∧ ∃ ev, !adjoinDef ev e v ∧
    !(exsChainVDef LAct) y ev B Γ d”
instance goalLeafCode_defined : 𝚺₁-Function₅ (goalLeafCode : V → V → V → V → V → V) via goalLeafCodeDef := .mk
  fun v ↦ by
    simp [goalLeafCodeDef, goalBody_defined.iff, goalInst_defined.iff, derFact_defined.iff, fstIdxFact_defined.iff,
      dlenFact_defined.iff, leFact_defined.iff, conj4Code_defined.iff, exsChainV_defined.iff, goalLeafCode]

/-- The cost of a `sGoal` step (`dlen_goalLeafCode_le` + the cut): `11G + 27·|goalFact|·E + 2E + 42`. -/
noncomputable def goalCost (G Q E : V) : V := 11 * G + 27 * (Q * E) + 2 * E + 42
def goalCostDef : 𝚺₀.Semisentence 4 := .mkSigma “y G Q E. y = 11 * G + 27 * (Q * E) + 2 * E + 42”
instance goalCost_defined : 𝚺₀-Function₃ (goalCost : V → V → V → V) via goalCostDef := .mk
  fun v ↦ by simp [goalCostDef, goalCost, numeral_eq_natCast]

/-! ### C.3 The leaf theorems: `goalLeafCode` derives `insert (goalFact s ū) Γ`, its length; the lemma cut -/

lemma isSemiterm_bv_two (i : ℕ) (h : i < 2) : IsSemiterm LAct (2 : V) (bv i) :=
  IsSemiterm.bvar.mpr (by exact_mod_cast h)

lemma isFormula_derFact {e : V} (he : IsSemiterm LAct 0 e) : IsFormula LAct (derFact e) :=
  isFormula_fact isSemiformula_Pderiv [e] rfl (by simp [he])
lemma isFormula_fstIdxFact {s e : V} (hs : IsSemiterm LAct 0 s) (he : IsSemiterm LAct 0 e) :
    IsFormula LAct (fstIdxFact s e) :=
  isFormula_fact isSemiformula_PfstIdx [s, e] rfl (by simp [hs, he])
lemma isFormula_dlenFact {e n : V} (he : IsSemiterm LAct 0 e) (hn : IsSemiterm LAct 0 n) :
    IsFormula LAct (dlenFact e n) :=
  isFormula_fact isSemiformula_Pdlen [e, n] rfl (by simp [he, hn])
lemma isFormula_leFact {n u : V} (hn : IsSemiterm LAct 0 n) (hu : IsSemiterm LAct 0 u) :
    IsFormula LAct (leFact n u) :=
  isFormula_fact isSemiformula_Ple [n, u] rfl (by simp [hn, hu])

lemma isSemiformula_goalBody {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    IsSemiformula LAct ((2 : ℕ) : V) (goalBody s u) := by
  have hs2 : IsSemiterm LAct (2 : V) s := isSemiterm_of_le hs zero_le
  have hu2 : IsSemiterm LAct (2 : V) u := isSemiterm_of_le hu zero_le
  have hb : ∀ i : ℕ, i < 2 → IsSemiterm LAct (2 : V) (bv i) := isSemiterm_bv_two
  unfold goalBody derFact fstIdxFact dlenFact leFact
  simp only [IsSemiformula.and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isSemiformula_substRow isSemiformula_Pderiv [bv 1] rfl (by simp [hb 1 (by norm_num)])
  · exact isSemiformula_substRow isSemiformula_PfstIdx [s, bv 1] rfl (by simp [hs2, hb 1 (by norm_num)])
  · exact isSemiformula_substRow isSemiformula_Pdlen [bv 1, bv 0] rfl
      (by simp [hb 1 (by norm_num), hb 0 (by norm_num)])
  · exact isSemiformula_substRow isSemiformula_Ple [bv 0, u] rfl (by simp [hu2, hb 0 (by norm_num)])

lemma isFormula_goalFact {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    IsFormula LAct (goalFact s u) :=
  isFormula_exsIter (k := 2) (isSemiformula_goalBody hs hu)

lemma isFormula_goalInst {e n s u : V} (he : IsSemiterm LAct 0 e) (hn : IsSemiterm LAct 0 n)
    (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) : IsFormula LAct (goalInst e n s u) := by
  unfold goalInst
  simp [isFormula_derFact he, isFormula_fstIdxFact hs he, isFormula_dlenFact he hn, isFormula_leFact hn hu]

lemma formulaLen_goalFact {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    formulaLen LAct (goalFact s u) = formulaLen LAct (goalBody s u) + 2 := by
  have := formulaLen_exsIter (n := 2) (isSemiformula_goalBody hs hu).isUFormula
  rw [show goalFact s u = exsIter 2 (goalBody s u) from rfl, this]
  simp

lemma instOuter_goalBody {e n s u : V} (he : IsSemiterm LAct 0 e) (hn : IsSemiterm LAct 0 n)
    (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    instOuter LAct [e, n] (goalBody s u) = goalInst e n s u := by
  have hs2 : IsSemiterm LAct ((2 : ℕ) : V) s := isSemiterm_of_le hs zero_le
  have hu2 : IsSemiterm LAct ((2 : ℕ) : V) u := isSemiterm_of_le hu zero_le
  have hb1 : IsSemiterm LAct ((2 : ℕ) : V) (bv 1) := isSemiterm_bv (by norm_num)
  have hb0 : IsSemiterm LAct ((2 : ℕ) : V) (bv 0) := isSemiterm_bv (by norm_num)
  have hes : ∀ x ∈ [e, n], IsSemiterm LAct 0 x := List.forall_mem_cons.mpr ⟨he, List.forall_mem_singleton.mpr hn⟩
  have t1 : ∀ t ∈ [bv 1], IsSemiterm LAct ((2 : ℕ) : V) t := List.forall_mem_singleton.mpr hb1
  have t2 : ∀ t ∈ [s, bv 1], IsSemiterm LAct ((2 : ℕ) : V) t :=
    List.forall_mem_cons.mpr ⟨hs2, List.forall_mem_singleton.mpr hb1⟩
  have t3 : ∀ t ∈ [bv 1, bv 0], IsSemiterm LAct ((2 : ℕ) : V) t :=
    List.forall_mem_cons.mpr ⟨hb1, List.forall_mem_singleton.mpr hb0⟩
  have t4 : ∀ t ∈ [bv 0, u], IsSemiterm LAct ((2 : ℕ) : V) t :=
    List.forall_mem_cons.mpr ⟨hb0, List.forall_mem_singleton.mpr hu2⟩
  have h1 := isSemiformula_substRow (n := 2) isSemiformula_Pderiv [bv 1] rfl t1
  have h2 := isSemiformula_substRow (n := 2) isSemiformula_PfstIdx [s, bv 1] rfl t2
  have h3 := isSemiformula_substRow (n := 2) isSemiformula_Pdlen [bv 1, bv 0] rfl t3
  have h4 := isSemiformula_substRow (n := 2) isSemiformula_Ple [bv 0, u] rfl t4
  have hes2 : ((([e, n] : List V).length + 0 : ℕ) : V) = ((2 : ℕ) : V) := by simp
  unfold goalBody goalInst derFact fstIdxFact dlenFact leFact
  rw [← instOuterAt_zero,
    instOuterAt_and 0 [e, n] (by rw [hes2]; exact h1)
      (by rw [hes2]; exact IsSemiformula.and.mpr ⟨h2, IsSemiformula.and.mpr ⟨h3, h4⟩⟩) hes,
    instOuterAt_and 0 [e, n] (by rw [hes2]; exact h2) (by rw [hes2]; exact IsSemiformula.and.mpr ⟨h3, h4⟩) hes,
    instOuterAt_and 0 [e, n] (by rw [hes2]; exact h3) (by rw [hes2]; exact h4) hes,
    instOuterAt_subst_listToVec 0 [bv 1] isSemiformula_Pderiv rfl [e, n] hes (by rw [hes2]; exact t1),
    instOuterAt_subst_listToVec 0 [s, bv 1] isSemiformula_PfstIdx rfl [e, n] hes (by rw [hes2]; exact t2),
    instOuterAt_subst_listToVec 0 [bv 1, bv 0] isSemiformula_Pdlen rfl [e, n] hes (by rw [hes2]; exact t3),
    instOuterAt_subst_listToVec 0 [bv 0, u] isSemiformula_Ple rfl [e, n] hes (by rw [hes2]; exact t4)]
  row_entries_simp
  rw [termSubst_eq_self_of_closed hs, termSubst_eq_self_of_closed hu]

theorem conj4Code_proof {S A₁ A₂ A₃ A₄ : V} (hS : IsFormulaSet LAct S)
    (h₁ : IsFormula LAct A₁) (h₂ : IsFormula LAct A₂) (h₃ : IsFormula LAct A₃) (h₄ : IsFormula LAct A₄)
    (hmem : A₁ ^⋏ (A₂ ^⋏ (A₃ ^⋏ A₄)) ∈ S)
    (hn₁ : neg LAct A₁ ∈ S) (hn₂ : neg LAct A₂ ∈ S) (hn₃ : neg LAct A₃ ∈ S) (hn₄ : neg LAct A₄ ∈ S) :
    DerivationOf TAct (conj4Code S A₁ A₂ A₃ A₄) S := by
  have hS₂ : IsFormulaSet LAct (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S) := by simp [hS, h₂, h₃, h₄]
  have hS₃ : IsFormulaSet LAct (insert (A₃ ^⋏ A₄) (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S)) := by simp [hS, h₂, h₃, h₄]
  refine ⟨by simp [conj4Code], Derivation.andIntro hmem (axLFactCode_proof h₁ hS hn₁) ?_⟩
  refine ⟨by simp, Derivation.andIntro (by simp) (axLFactCode_proof h₂ hS₂ (by simp [hn₂])) ?_⟩
  refine ⟨by simp, Derivation.andIntro (by simp) (axLFactCode_proof h₃ hS₃ (by simp [hn₃]))
    (axLFactCode_proof h₄ hS₃ (by simp [hn₄]))⟩

theorem dlen_conj4Code_le {S A₁ A₂ A₃ A₄ : V} (hS : IsFormulaSet LAct S)
    (h₁ : IsFormula LAct A₁) (h₂ : IsFormula LAct A₂) (h₃ : IsFormula LAct A₃) (h₄ : IsFormula LAct A₄)
    (hmem : A₁ ^⋏ (A₂ ^⋏ (A₃ ^⋏ A₄)) ∈ S)
    (hn₁ : neg LAct A₁ ∈ S) (hn₂ : neg LAct A₂ ∈ S) (hn₃ : neg LAct A₃ ∈ S) (hn₄ : neg LAct A₄ ∈ S) :
    dlen TAct (conj4Code S A₁ A₂ A₃ A₄) ≤
      7 * setLen LAct S + 11 * (formulaLen LAct A₁ + formulaLen LAct A₂ + formulaLen LAct A₃ + formulaLen LAct A₄) + 20 := by
  have hS₂ : IsFormulaSet LAct (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S) := by simp [hS, h₂, h₃, h₄]
  have hS₃ : IsFormulaSet LAct (insert (A₃ ^⋏ A₄) (insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S)) := by simp [hS, h₂, h₃, h₄]
  set S₂ := insert (A₂ ^⋏ (A₃ ^⋏ A₄)) S with hS₂def
  set S₃ := insert (A₃ ^⋏ A₄) S₂ with hS₃def
  have hx₁ := axLFactCode_proof (T := TAct) h₁ hS hn₁
  have hx₂ := axLFactCode_proof (T := TAct) h₂ hS₂ (by simp [S₂, hn₂])
  have hx₃ := axLFactCode_proof (T := TAct) h₃ hS₃ (by simp [S₃, S₂, hn₃])
  have hx₄ := axLFactCode_proof (T := TAct) h₄ hS₃ (by simp [S₃, S₂, hn₄])
  have hd₃ : DerivationOf TAct (andIntro S₃ A₃ A₄ (axLFactCode S₃ A₃) (axLFactCode S₃ A₄)) S₃ :=
    ⟨by simp, Derivation.andIntro (by simp [S₃]) hx₃ hx₄⟩
  have hd₂ : DerivationOf TAct (andIntro S₂ A₂ (A₃ ^⋏ A₄) (axLFactCode S₂ A₂)
      (andIntro S₃ A₃ A₄ (axLFactCode S₃ A₃) (axLFactCode S₃ A₄))) S₂ :=
    ⟨by simp, Derivation.andIntro (by simp [S₂]) hx₂ hd₃⟩
  have l₁ := dlen_axLFactCode (T := TAct) h₁ hS hn₁
  have l₂ := dlen_axLFactCode (T := TAct) h₂ hS₂ (by simp [S₂, hn₂])
  have l₃ := dlen_axLFactCode (T := TAct) h₃ hS₃ (by simp [S₃, S₂, hn₃])
  have l₄ := dlen_axLFactCode (T := TAct) h₄ hS₃ (by simp [S₃, S₂, hn₄])
  have e₃ : dlen TAct (andIntro S₃ A₃ A₄ (axLFactCode S₃ A₃) (axLFactCode S₃ A₄)) =
      setLen LAct S₃ + dlen TAct (axLFactCode S₃ A₃) + dlen TAct (axLFactCode S₃ A₄) + 1 :=
    dlen_eq_of_graph hd₃.2 (DlenGraph.andIntro_iff.mpr ⟨_, _, dlen_graph hx₃.2, dlen_graph hx₄.2, rfl⟩)
  have e₂ : dlen TAct (andIntro S₂ A₂ (A₃ ^⋏ A₄) (axLFactCode S₂ A₂)
      (andIntro S₃ A₃ A₄ (axLFactCode S₃ A₃) (axLFactCode S₃ A₄))) =
      setLen LAct S₂ + dlen TAct (axLFactCode S₂ A₂)
        + dlen TAct (andIntro S₃ A₃ A₄ (axLFactCode S₃ A₃) (axLFactCode S₃ A₄)) + 1 :=
    dlen_eq_of_graph hd₂.2 (DlenGraph.andIntro_iff.mpr ⟨_, _, dlen_graph hx₂.2, dlen_graph hd₃.2, rfl⟩)
  have hpf := conj4Code_proof hS h₁ h₂ h₃ h₄ hmem hn₁ hn₂ hn₃ hn₄
  have e₁ : dlen TAct (conj4Code S A₁ A₂ A₃ A₄) =
      setLen LAct S + dlen TAct (axLFactCode S A₁) + dlen TAct (andIntro S₂ A₂ (A₃ ^⋏ A₄) (axLFactCode S₂ A₂)
      (andIntro S₃ A₃ A₄ (axLFactCode S₃ A₃) (axLFactCode S₃ A₄))) + 1 :=
    dlen_eq_of_graph hpf.2 (DlenGraph.andIntro_iff.mpr ⟨_, _, dlen_graph hx₁.2, dlen_graph hd₂.2, rfl⟩)
  have i₁ : setLen LAct (insert A₁ S) ≤ setLen LAct S + formulaLen LAct A₁ := setLen_insert_le _ _
  have i₂ : setLen LAct (insert A₂ S₂) ≤ setLen LAct S₂ + formulaLen LAct A₂ := setLen_insert_le _ _
  have i₃ : setLen LAct (insert A₃ S₃) ≤ setLen LAct S₃ + formulaLen LAct A₃ := setLen_insert_le _ _
  have i₄ : setLen LAct (insert A₄ S₃) ≤ setLen LAct S₃ + formulaLen LAct A₄ := setLen_insert_le _ _
  have j₂ : setLen LAct S₂ ≤
      setLen LAct S + (formulaLen LAct A₂ + (formulaLen LAct A₃ + formulaLen LAct A₄ + 1) + 1) := by
    have := setLen_insert_le (L := LAct) (A₂ ^⋏ (A₃ ^⋏ A₄)) S
    rwa [formulaLen_and h₂.isUFormula (IsUFormula.and.mpr ⟨h₃.isUFormula, h₄.isUFormula⟩),
      formulaLen_and h₃.isUFormula h₄.isUFormula] at this
  have j₃ : setLen LAct S₃ ≤ setLen LAct S₂ + (formulaLen LAct A₃ + formulaLen LAct A₄ + 1) := by
    have := setLen_insert_le (L := LAct) (A₃ ^⋏ A₄) S₂
    rwa [formulaLen_and h₃.isUFormula h₄.isUFormula] at this
  rw [e₁, e₂, e₃, l₁, l₂, l₃, l₄]
  calc setLen LAct S + (setLen LAct (insert A₁ S) + 1) + (setLen LAct S₂ + (setLen LAct (insert A₂ S₂) + 1)
        + (setLen LAct S₃ + (setLen LAct (insert A₃ S₃) + 1) + (setLen LAct (insert A₄ S₃) + 1) + 1) + 1) + 1
      ≤ setLen LAct S + (setLen LAct S + formulaLen LAct A₁ + 1) + (setLen LAct S₂ + (setLen LAct S₂ + formulaLen LAct A₂ + 1)
        + (setLen LAct S₃ + (setLen LAct S₃ + formulaLen LAct A₃ + 1) + (setLen LAct S₃ + formulaLen LAct A₄ + 1) + 1) + 1) + 1 := by
        gcongr
    _ = 2 * setLen LAct S + 2 * setLen LAct S₂ + 3 * setLen LAct S₃
        + (formulaLen LAct A₁ + formulaLen LAct A₂ + formulaLen LAct A₃ + formulaLen LAct A₄) + 7 := by ring
    _ ≤ 2 * setLen LAct S + 2 * (setLen LAct S + (formulaLen LAct A₂ + (formulaLen LAct A₃ + formulaLen LAct A₄ + 1) + 1))
        + 3 * (setLen LAct S + (formulaLen LAct A₂ + (formulaLen LAct A₃ + formulaLen LAct A₄ + 1) + 1)
          + (formulaLen LAct A₃ + formulaLen LAct A₄ + 1))
        + (formulaLen LAct A₁ + formulaLen LAct A₂ + formulaLen LAct A₃ + formulaLen LAct A₄) + 7 := by
        gcongr
        exact le_trans j₃ (add_le_add j₂ le_rfl)
    _ = 7 * setLen LAct S + (formulaLen LAct A₁ + 6 * formulaLen LAct A₂ + 9 * formulaLen LAct A₃
          + 9 * formulaLen LAct A₄) + 20 := by ring
    _ ≤ 7 * setLen LAct S
        + 11 * (formulaLen LAct A₁ + formulaLen LAct A₂ + formulaLen LAct A₃ + formulaLen LAct A₄) + 20 := by
        gcongr
        have : 11 * (formulaLen LAct A₁ + formulaLen LAct A₂ + formulaLen LAct A₃ + formulaLen LAct A₄) =
            (formulaLen LAct A₁ + 6 * formulaLen LAct A₂ + 9 * formulaLen LAct A₃ + 9 * formulaLen LAct A₄)
            + (10 * formulaLen LAct A₁ + 5 * formulaLen LAct A₂ + 2 * formulaLen LAct A₃ + 2 * formulaLen LAct A₄) := by
          ring
        rw [this]; exact le_self_add

theorem goalLeafCode_proof {Γ e n s u : V} (he : IsSemiterm LAct 0 e) (hn : IsSemiterm LAct 0 n)
    (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) (hΓ : IsFormulaSet LAct Γ)
    (h₁ : neg LAct (derFact e) ∈ Γ) (h₂ : neg LAct (fstIdxFact s e) ∈ Γ) (h₃ : neg LAct (dlenFact e n) ∈ Γ)
    (h₄ : neg LAct (leFact n u) ∈ Γ) :
    DerivationOf TAct (goalLeafCode Γ e n s u) (insert (goalFact s u) Γ) := by
  have hB : IsSemiformula LAct ((([e, n] : List V).length : ℕ) : V) (goalBody s u) := isSemiformula_goalBody hs hu
  have hes : ∀ x ∈ [e, n], IsTerm LAct x := by simp [he, hn]
  have hM : IsFormula LAct (goalInst e n s u) := isFormula_goalInst he hn hs hu
  have hd := conj4Code_proof (S := insert (goalInst e n s u) Γ) (by simp [hM, hΓ]) (isFormula_derFact he)
    (isFormula_fstIdxFact hs he) (isFormula_dlenFact he hn) (isFormula_leFact hn hu) (by simp [goalInst])
    (by simp [h₁]) (by simp [h₂]) (by simp [h₃]) (by simp [h₄])
  unfold goalLeafCode
  rw [show (e ∷ n ∷ 0 : V) = vecOf [e, n] from rfl, exsChainV_vecOf [e, n] hB hes]
  have := exsChainCode_proof (T := TAct) [e, n] hB hes hΓ (subset_refl Γ)
    (by rw [instOuter_goalBody he hn hs hu]; exact hd)
  exact this

theorem dlen_goalLeafCode_le {E Γ e n s u : V} (hE : 1 ≤ E)
    (he : IsSemiterm LAct 0 e) (hel : termLen LAct e ≤ E) (hn : IsSemiterm LAct 0 n) (hnl : termLen LAct n ≤ E)
    (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) (hΓ : IsFormulaSet LAct Γ)
    (h₁ : neg LAct (derFact e) ∈ Γ) (h₂ : neg LAct (fstIdxFact s e) ∈ Γ) (h₃ : neg LAct (dlenFact e n) ∈ Γ)
    (h₄ : neg LAct (leFact n u) ∈ Γ) :
    dlen TAct (goalLeafCode Γ e n s u) ≤
      10 * setLen LAct Γ + 27 * (formulaLen LAct (goalBody s u) * E) + 2 * E + 41 := by
  have hB : IsSemiformula LAct ((([e, n] : List V).length : ℕ) : V) (goalBody s u) := isSemiformula_goalBody hs hu
  have hB2 : IsSemiformula LAct ((2 : ℕ) : V) (goalBody s u) := isSemiformula_goalBody hs hu
  have hes : ∀ x ∈ [e, n], IsTerm LAct x := by simp [he, hn]
  have hes' : ∀ x ∈ [e, n], IsTerm LAct x ∧ termLen LAct x ≤ E := by simp [he, hn, hel, hnl]
  have hM : IsFormula LAct (goalInst e n s u) := isFormula_goalInst he hn hs hu
  have hS : IsFormulaSet LAct (insert (goalInst e n s u) Γ) := by simp [hM, hΓ]
  have hd := conj4Code_proof (S := insert (goalInst e n s u) Γ) hS (isFormula_derFact he)
    (isFormula_fstIdxFact hs he) (isFormula_dlenFact he hn) (isFormula_leFact hn hu) (by simp [goalInst])
    (by simp [h₁]) (by simp [h₂]) (by simp [h₃]) (by simp [h₄])
  have hd' : DerivationOf TAct (conj4Code (insert (goalInst e n s u) Γ) (derFact e) (fstIdxFact s e) (dlenFact e n)
      (leFact n u)) (insert (instOuter LAct [e, n] (goalBody s u)) Γ) := by
    rw [instOuter_goalBody he hn hs hu]; exact hd
  have hcost := dlen_conj4Code_le (S := insert (goalInst e n s u) Γ) hS (isFormula_derFact he)
    (isFormula_fstIdxFact hs he) (isFormula_dlenFact he hn) (isFormula_leFact hn hu) (by simp [goalInst])
    (by simp [h₁]) (by simp [h₂]) (by simp [h₃]) (by simp [h₄])
  have hinst : formulaLen LAct (goalInst e n s u) ≤ formulaLen LAct (goalBody s u) * E := by
    rw [← instOuter_goalBody he hn hs hu]
    exact formulaLen_instOuter_le hE [e, n] hB hes'
  have hF₄ : formulaLen LAct (derFact e) + formulaLen LAct (fstIdxFact s e) + formulaLen LAct (dlenFact e n)
      + formulaLen LAct (leFact n u) ≤ formulaLen LAct (goalBody s u) * E := by
    refine le_trans ?_ hinst
    unfold goalInst
    rw [formulaLen_and (isFormula_derFact he).isUFormula (by simp [(isFormula_fstIdxFact hs he).isUFormula,
        (isFormula_dlenFact he hn).isUFormula, (isFormula_leFact hn hu).isUFormula]),
      formulaLen_and (isFormula_fstIdxFact hs he).isUFormula (by simp [(isFormula_dlenFact he hn).isUFormula,
        (isFormula_leFact hn hu).isUFormula]),
      formulaLen_and (isFormula_dlenFact he hn).isUFormula (isFormula_leFact hn hu).isUFormula]
    have hh : formulaLen LAct (derFact e) + formulaLen LAct (fstIdxFact s e) + formulaLen LAct (dlenFact e n)
        + formulaLen LAct (leFact n u) + 3 =
        formulaLen LAct (derFact e) + (formulaLen LAct (fstIdxFact s e)
          + (formulaLen LAct (dlenFact e n) + formulaLen LAct (leFact n u) + 1) + 1) + 1 := by ring
    rw [← hh]; exact le_self_add
  have hSlen : setLen LAct (insert (goalInst e n s u) Γ) ≤ setLen LAct Γ + formulaLen LAct (goalBody s u) * E :=
    le_trans (setLen_insert_le _ _) (add_le_add le_rfl hinst)
  have hchain := dlen_exsChainCode_le (T := TAct) (E := E) (F := formulaLen LAct (goalBody s u) * E + 2) hE hB2 [e, n]
    hB hes' hΓ (subset_refl Γ) hd' (isInstOf_self E 2 (goalBody s u)) (by simp) le_rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.cast_ofNat] at hchain
  unfold goalLeafCode
  rw [show (e ∷ n ∷ 0 : V) = vecOf [e, n] from rfl, exsChainV_vecOf [e, n] hB hes]
  refine le_trans hchain ?_
  calc dlen TAct (conj4Code (insert (goalInst e n s u) Γ) (derFact e) (fstIdxFact s e) (dlenFact e n) (leFact n u))
        + (2 + 1) * (setLen LAct Γ + 1) + (2 + 1) * (2 + 1) * (formulaLen LAct (goalBody s u) * E + 2) + 2 * E
      ≤ (7 * (setLen LAct Γ + formulaLen LAct (goalBody s u) * E) + 11 * (formulaLen LAct (goalBody s u) * E) + 20)
        + (2 + 1) * (setLen LAct Γ + 1) + (2 + 1) * (2 + 1) * (formulaLen LAct (goalBody s u) * E + 2) + 2 * E := by
        gcongr
        exact le_trans hcost (by gcongr)
    _ = _ := by ring


/-- `{A} ⊆ insert A Γ`. -/
lemma singleton_subset_insert (A Γ : V) : insert A (0 : V) ⊆ insert A Γ := by
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | h
  · simp
  · simp at h

theorem lemmaCut_proof {Γ A dA e : V} (hΓ : IsFormulaSet LAct Γ) (hA : IsFormula LAct A)
    (hdA : DerivationOf TAct dA (insert A 0)) (he : DerivationOf TAct e (insert (neg LAct A) Γ)) :
    DerivationOf TAct (cutRule Γ A (wkToCode (insert A Γ) dA) e) Γ :=
  ⟨by simp, Derivation.cutRule (wkToCode_proof (by simp [hA, hΓ]) (singleton_subset_insert A Γ) hdA) he⟩

theorem dlen_lemmaCut_le {Γ A dA e : V} (hΓ : IsFormulaSet LAct Γ) (hA : IsFormula LAct A)
    (hdA : DerivationOf TAct dA (insert A 0)) (he : DerivationOf TAct e (insert (neg LAct A) Γ)) :
    dlen TAct (cutRule Γ A (wkToCode (insert A Γ) dA) e) ≤
      dlen TAct e + (dlen TAct dA + 2 * setLen LAct Γ + 2 * formulaLen LAct A + 2) := by
  have hw := wkToCode_proof (T := TAct) (Γ := insert A Γ) (by simp [hA, hΓ]) (singleton_subset_insert A Γ) hdA
  have hl := dlen_wkToCode (T := TAct) (Γ := insert A Γ) (by simp [hA, hΓ]) (singleton_subset_insert A Γ) hdA
  have hpf := lemmaCut_proof hΓ hA hdA he
  have hc : dlen TAct (cutRule Γ A (wkToCode (insert A Γ) dA) e) =
      setLen LAct Γ + dlen TAct (wkToCode (insert A Γ) dA) + dlen TAct e + 1 :=
    dlen_eq_of_graph hpf.2 (DlenGraph.cutRule_iff.mpr ⟨_, _, dlen_graph hw.2, dlen_graph he.2, rfl⟩)
  rw [hc, hl]
  have hi : setLen LAct (insert A Γ) ≤ setLen LAct Γ + formulaLen LAct A := setLen_insert_le _ _
  calc setLen LAct Γ + (setLen LAct (insert A Γ) + dlen TAct dA + 1) + dlen TAct e + 1
      ≤ setLen LAct Γ + (setLen LAct Γ + formulaLen LAct A + dlen TAct dA + 1) + dlen TAct e + 1 := by gcongr
    _ ≤ dlen TAct e + (dlen TAct dA + 2 * setLen LAct Γ + 2 * formulaLen LAct A + 2) := by
        have : dlen TAct e + (dlen TAct dA + 2 * setLen LAct Γ + 2 * formulaLen LAct A + 2) =
          (setLen LAct Γ + (setLen LAct Γ + formulaLen LAct A + dlen TAct dA + 1) + dlen TAct e + 1) + formulaLen LAct A := by ring
        rw [this]; exact le_self_add


end partC

/-! ### B.2 Rows, steps, `applyStep`, `ctxAfter`, `stepCost`, `StepOK`

A ROW of the table is `⟪dΛ, m, B⟫`: the stored proof code of `qqAlls B m`, the arity, the matrix.
A STEP is `⟪tag, …⟫`; the Horn steps CARRY their own decomposition of the row matrix (the
antecedent vector `as` and the conclusion piece), which `StepOK` checks syntactically
(`rowB = impChainV as c`) — so no Σ₁ Horn-decomposition of a code is ever needed:

| tag | code | `applyStep tbl Γ s e` | `ctxAfter Γ s` |
|---|---|---|---|
| 0 | `sUseHorn i ev as c` | `useHornV Γ ev as c dΛᵢ e` | `insert (neg c') Γ` |
| 1 | `sUseHornAnd i ev as c₁ c₂` | `useHornAndV Γ ev as c₁ c₂ dΛᵢ e` | `insert (neg c₁') (insert (neg c₂') Γ)` |
| 2 | `sIntroFact i ev as R` | `introFactV Γ ev as R dΛᵢ e` | `insert (neg (free R')) (setShift Γ)` |
| 3 | `sElimExs P` | `elimExistsCode Γ P (axLFactCode Γ (^∃ P)) e` | `insert (neg (free P)) (setShift Γ)` |
| 4 | `sSplit p q` | `splitAndCode Γ p q e` | `insert (neg p) (insert (neg q) Γ)` |
| 5 | `sWkDrop Γ'` | `wkDropCode Γ e` | `Γ'` |
| 6 | `sGoal e n s ū` | `cutRule Γ (goalFact s ū) (goalLeafCode Γ e n s ū) e` | `insert (neg (goalFact s ū)) Γ` |
| 7 | `sLemma A dA` | `cutRule Γ A (wkToCode (insert A Γ) dA) e` | `insert (neg A) Γ` |

with `c' = subst (revV ev) c` and `R' = subst (qVec (revV ev)) R` (the `instOuter`/`instOuterAt 1`
instances, `subst_revV_vecOf`/`subst_qVec_revV_vecOf`). `axLFactCode` is a LEAF: it never
appears as a step — a chain ends in an explicit continuation `d`, and a leaf is that `d`. -/

section stepLanguage

open LAct

/-- A row of the table: `⟪dΛ, m, B⟫`. -/
noncomputable def mkRow (dΛ m B : V) : V := ⟪dΛ, m, B⟫
noncomputable def rowD (r : V) : V := π₁ r
noncomputable def rowM (r : V) : V := π₁ (π₂ r)
noncomputable def rowB (r : V) : V := π₂ (π₂ r)

@[simp] lemma rowD_mkRow (dΛ m B : V) : rowD (mkRow dΛ m B) = dΛ := by simp [rowD, mkRow]
@[simp] lemma rowM_mkRow (dΛ m B : V) : rowM (mkRow dΛ m B) = m := by simp [rowM, mkRow]
@[simp] lemma rowB_mkRow (dΛ m B : V) : rowB (mkRow dΛ m B) = B := by simp [rowB, mkRow]

/-- **The row table is sound** with the uniform length bound `N`: every entry `⟪dΛ, m, B⟫` has
an `m`-semiformula matrix, a `TAct`-proof code `dΛ` of `qqAlls B m`, and `dlen dΛ ≤ N`
(what `Lib.univ_code` delivers, row by row). -/
def TableOK (tbl N : V) : Prop :=
  ∀ i < len tbl, IsSemiformula LAct (rowM tbl.[i]) (rowB tbl.[i]) ∧
    Proof TAct (rowD tbl.[i]) (qqAlls (rowB tbl.[i]) (rowM tbl.[i])) ∧ dlen TAct (rowD tbl.[i]) ≤ N

/-- The step codes. -/
noncomputable def sUseHorn (i ev as c : V) : V := ⟪0, i, ev, as, c⟫
noncomputable def sUseHornAnd (i ev as c₁ c₂ : V) : V := ⟪1, i, ev, as, c₁, c₂⟫
noncomputable def sIntroFact (i ev as R : V) : V := ⟪2, i, ev, as, R⟫
noncomputable def sElimExs (P : V) : V := ⟪3, P⟫
noncomputable def sSplit (p q : V) : V := ⟪4, p, q⟫
noncomputable def sWkDrop (Γ' : V) : V := ⟪5, Γ'⟫
/-- Part C: the goal-closing cut `⟪6, e, n, s, ū⟫` and the lemma cut `⟪7, A, dA⟫`. -/
noncomputable def sGoal (e n s u : V) : V := ⟪6, e, n, s, u⟫
noncomputable def sLemma (A dA : V) : V := ⟪7, A, dA⟫

/-- The fields of a step: `sTag`; for the Horn tags `sRow`, `sEv`, `sAs`, `sC` (for tag 1 `sC s =
⟪c₁, c₂⟫`, for tag 2 `sC s = R`); for tag 3 `π₂ s = P`; tag 4 `π₁ (π₂ s) = p`, `π₂ (π₂ s) = q`;
tag 5 `π₂ s = Γ'`. -/
noncomputable def sTag (s : V) : V := π₁ s
noncomputable def sRow (s : V) : V := π₁ (π₂ s)
noncomputable def sEv (s : V) : V := π₁ (π₂ (π₂ s))
noncomputable def sAs (s : V) : V := π₁ (π₂ (π₂ (π₂ s)))
noncomputable def sC (s : V) : V := π₂ (π₂ (π₂ (π₂ s)))
/-- The fields of the Part-C steps: tag 6 `sGoalE/sGoalN/sGoalS/sGoalU` (= `sRow/sEv/sAs/sC`),
tag 7 `sLemA = π₁ (π₂ s)`, `sLemD = π₂ (π₂ s)`. -/
noncomputable def sGoalE (s : V) : V := π₁ (π₂ s)
noncomputable def sGoalN (s : V) : V := π₁ (π₂ (π₂ s))
noncomputable def sGoalS (s : V) : V := π₁ (π₂ (π₂ (π₂ s)))
noncomputable def sGoalU (s : V) : V := π₂ (π₂ (π₂ (π₂ s)))
noncomputable def sLemA (s : V) : V := π₁ (π₂ s)
noncomputable def sLemD (s : V) : V := π₂ (π₂ s)

@[simp] lemma sTag_sUseHorn (i ev as c : V) : sTag (sUseHorn i ev as c) = 0 := by simp [sTag, sUseHorn]
@[simp] lemma sRow_sUseHorn (i ev as c : V) : sRow (sUseHorn i ev as c) = i := by simp [sRow, sUseHorn]
@[simp] lemma sEv_sUseHorn (i ev as c : V) : sEv (sUseHorn i ev as c) = ev := by simp [sEv, sUseHorn]
@[simp] lemma sAs_sUseHorn (i ev as c : V) : sAs (sUseHorn i ev as c) = as := by simp [sAs, sUseHorn]
@[simp] lemma sC_sUseHorn (i ev as c : V) : sC (sUseHorn i ev as c) = c := by simp [sC, sUseHorn]
@[simp] lemma sTag_sUseHornAnd (i ev as c₁ c₂ : V) : sTag (sUseHornAnd i ev as c₁ c₂) = 1 := by
  simp [sTag, sUseHornAnd]
@[simp] lemma sRow_sUseHornAnd (i ev as c₁ c₂ : V) : sRow (sUseHornAnd i ev as c₁ c₂) = i := by
  simp [sRow, sUseHornAnd]
@[simp] lemma sEv_sUseHornAnd (i ev as c₁ c₂ : V) : sEv (sUseHornAnd i ev as c₁ c₂) = ev := by
  simp [sEv, sUseHornAnd]
@[simp] lemma sAs_sUseHornAnd (i ev as c₁ c₂ : V) : sAs (sUseHornAnd i ev as c₁ c₂) = as := by
  simp [sAs, sUseHornAnd]
@[simp] lemma sC_sUseHornAnd (i ev as c₁ c₂ : V) : sC (sUseHornAnd i ev as c₁ c₂) = ⟪c₁, c₂⟫ := by
  simp [sC, sUseHornAnd]
@[simp] lemma sTag_sIntroFact (i ev as R : V) : sTag (sIntroFact i ev as R) = 2 := by simp [sTag, sIntroFact]
@[simp] lemma sRow_sIntroFact (i ev as R : V) : sRow (sIntroFact i ev as R) = i := by simp [sRow, sIntroFact]
@[simp] lemma sEv_sIntroFact (i ev as R : V) : sEv (sIntroFact i ev as R) = ev := by simp [sEv, sIntroFact]
@[simp] lemma sAs_sIntroFact (i ev as R : V) : sAs (sIntroFact i ev as R) = as := by simp [sAs, sIntroFact]
@[simp] lemma sC_sIntroFact (i ev as R : V) : sC (sIntroFact i ev as R) = R := by simp [sC, sIntroFact]
@[simp] lemma sTag_sElimExs (P : V) : sTag (sElimExs P) = 3 := by simp [sTag, sElimExs]
@[simp] lemma pi₂_sElimExs (P : V) : π₂ (sElimExs P) = P := by simp [sElimExs]
@[simp] lemma sTag_sSplit (p q : V) : sTag (sSplit p q) = 4 := by simp [sTag, sSplit]
@[simp] lemma pi₂_sSplit (p q : V) : π₂ (sSplit p q) = ⟪p, q⟫ := by simp [sSplit]
@[simp] lemma sTag_sWkDrop (Γ' : V) : sTag (sWkDrop Γ') = 5 := by simp [sTag, sWkDrop]
@[simp] lemma pi₂_sWkDrop (Γ' : V) : π₂ (sWkDrop Γ') = Γ' := by simp [sWkDrop]
@[simp] lemma sTag_sGoal (e n s u : V) : sTag (sGoal e n s u) = 6 := by simp [sTag, sGoal]
@[simp] lemma sGoalE_sGoal (e n s u : V) : sGoalE (sGoal e n s u) = e := by simp [sGoalE, sGoal]
@[simp] lemma sGoalN_sGoal (e n s u : V) : sGoalN (sGoal e n s u) = n := by simp [sGoalN, sGoal]
@[simp] lemma sGoalS_sGoal (e n s u : V) : sGoalS (sGoal e n s u) = s := by simp [sGoalS, sGoal]
@[simp] lemma sGoalU_sGoal (e n s u : V) : sGoalU (sGoal e n s u) = u := by simp [sGoalU, sGoal]
@[simp] lemma sTag_sLemma (A dA : V) : sTag (sLemma A dA) = 7 := by simp [sTag, sLemma]
@[simp] lemma sLemA_sLemma (A dA : V) : sLemA (sLemma A dA) = A := by simp [sLemA, sLemma]
@[simp] lemma sLemD_sLemma (A dA : V) : sLemD (sLemma A dA) = dA := by simp [sLemD, sLemma]

/-- **Apply one step** at the context `Γ` to the continuation `e` (the derivation code of
`ctxAfter Γ s`): the Part-A vector constructor of the tag. Unknown tags act as `wkDrop`. -/
noncomputable def applyStep (tbl Γ s e : V) : V :=
  if sTag s = 0 then useHornV LAct Γ (sEv s) (sAs s) (sC s) (rowD tbl.[sRow s]) e
  else if sTag s = 1 then
    useHornAndV LAct Γ (sEv s) (sAs s) (π₁ (sC s)) (π₂ (sC s)) (rowD tbl.[sRow s]) e
  else if sTag s = 2 then introFactV LAct Γ (sEv s) (sAs s) (sC s) (rowD tbl.[sRow s]) e
  else if sTag s = 3 then elimExistsCode LAct Γ (π₂ s) (axLFactCode Γ (^∃ (π₂ s))) e
  else if sTag s = 4 then splitAndCode LAct Γ (π₁ (π₂ s)) (π₂ (π₂ s)) e
  else if sTag s = 6 then
    cutRule Γ (goalFact (sGoalS s) (sGoalU s)) (goalLeafCode Γ (sGoalE s) (sGoalN s) (sGoalS s) (sGoalU s)) e
  else if sTag s = 7 then cutRule Γ (sLemA s) (wkToCode (insert (sLemA s) Γ) (sLemD s)) e
  else wkDropCode Γ e

noncomputable def applyStepDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y tbl Γ s e. ∃ t, !pi₁Def t s ∧ ∃ p, !pi₂Def p s ∧ ∃ i, !pi₁Def i p ∧ ∃ p₂, !pi₂Def p₂ p ∧
    ∃ ev, !pi₁Def ev p₂ ∧ ∃ p₃, !pi₂Def p₃ p₂ ∧ ∃ as, !pi₁Def as p₃ ∧ ∃ c, !pi₂Def c p₃ ∧
    ∃ r, !nthDef r tbl i ∧ ∃ dΛ, !pi₁Def dΛ r ∧ ∃ c₁, !pi₁Def c₁ c ∧ ∃ c₂, !pi₂Def c₂ c ∧
    (t = 0 → !(useHornVDef LAct) y Γ ev as c dΛ e) ∧
    (t = 1 → !(useHornAndVDef LAct) y Γ ev as c₁ c₂ dΛ e) ∧
    (t = 2 → !(introFactVDef LAct) y Γ ev as c dΛ e) ∧
    (t = 3 → ∃ eP, !qqExsDef eP p ∧ ∃ j, !insertDef j eP Γ ∧ ∃ ax, !axLGraph ax j eP ∧
      !(elimExistsCodeDef LAct) y Γ p ax e) ∧
    (t = 4 → !(splitAndCodeDef LAct) y Γ i p₂ e) ∧
    (t = 6 → ∃ g, !goalFactDef g as c ∧ ∃ l, !goalLeafCodeDef l Γ i ev as c ∧ !cutRuleGraph y Γ g l e) ∧
    (t = 7 → ∃ j, !insertDef j i Γ ∧ ∃ w, !wkRuleGraph w j p₂ ∧ !cutRuleGraph y Γ i w e) ∧
    (t ≠ 0 → t ≠ 1 → t ≠ 2 → t ≠ 3 → t ≠ 4 → t ≠ 6 → t ≠ 7 → !wkRuleGraph y Γ e)”

instance applyStep_defined : 𝚺₁-Function₄ (applyStep : V → V → V → V → V) via applyStepDef := .mk
  fun v ↦ by
    simp [applyStepDef, useHornV_defined.iff, useHornAndV_defined.iff, introFactV_defined.iff,
      elimExistsCode_defined.iff, splitAndCode_defined.iff, goalFact_defined.iff, goalLeafCode_defined.iff,
      numeral_eq_natCast]
    unfold applyStep sTag sRow sEv sAs sC rowD axLFactCode wkDropCode sGoalE sGoalN sGoalS sGoalU sLemA sLemD wkToCode
    by_cases h0 : π₁ (v 3) = 0
    · simp [h0]
    by_cases h1 : π₁ (v 3) = 1
    · simp [h1]
    by_cases h2 : π₁ (v 3) = 2
    · simp [h2]
    by_cases h3 : π₁ (v 3) = 3
    · simp [h3]
    by_cases h4 : π₁ (v 3) = 4
    · simp [h4]
    by_cases h6 : π₁ (v 3) = 6
    · simp [h6]
    by_cases h7 : π₁ (v 3) = 7
    · simp [h7]
    · simp [h0, h1, h2, h3, h4, h6, h7]

instance applyStep_definable : 𝚺₁-Function₄ (applyStep : V → V → V → V → V) := applyStep_defined.to_definable

/-- **The context after a step** — the sequent the continuation must derive (the `hd` of the
corresponding `_proof` theorem of `Steps.lean`). -/
noncomputable def ctxAfter (Γ s : V) : V :=
  if sTag s = 0 then insert (neg LAct (subst LAct (revV (sEv s)) (sC s))) Γ
  else if sTag s = 1 then
    insert (neg LAct (subst LAct (revV (sEv s)) (π₁ (sC s))))
      (insert (neg LAct (subst LAct (revV (sEv s)) (π₂ (sC s)))) Γ)
  else if sTag s = 2 then
    insert (neg LAct (free LAct (subst LAct (qVec LAct (revV (sEv s))) (sC s)))) (setShift LAct Γ)
  else if sTag s = 3 then insert (neg LAct (free LAct (π₂ s))) (setShift LAct Γ)
  else if sTag s = 4 then insert (neg LAct (π₁ (π₂ s))) (insert (neg LAct (π₂ (π₂ s))) Γ)
  else if sTag s = 6 then insert (neg LAct (goalFact (sGoalS s) (sGoalU s))) Γ
  else if sTag s = 7 then insert (neg LAct (sLemA s)) Γ
  else π₂ s

noncomputable def ctxAfterDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y Γ s. ∃ t, !pi₁Def t s ∧ ∃ p, !pi₂Def p s ∧ ∃ i, !pi₁Def i p ∧ ∃ p₂, !pi₂Def p₂ p ∧
    ∃ ev, !pi₁Def ev p₂ ∧ ∃ p₃, !pi₂Def p₃ p₂ ∧ ∃ as, !pi₁Def as p₃ ∧ ∃ c, !pi₂Def c p₃ ∧
    ∃ c₁, !pi₁Def c₁ c ∧ ∃ c₂, !pi₂Def c₂ c ∧ ∃ r, !revVDef r ev ∧
    (t = 0 → ∃ z, !(substsGraph LAct) z r c ∧ ∃ nz, !(negGraph LAct) nz z ∧ !insertDef y nz Γ) ∧
    (t = 1 → ∃ z₁, !(substsGraph LAct) z₁ r c₁ ∧ ∃ n₁, !(negGraph LAct) n₁ z₁ ∧
      ∃ z₂, !(substsGraph LAct) z₂ r c₂ ∧ ∃ n₂, !(negGraph LAct) n₂ z₂ ∧
      ∃ g, !insertDef g n₂ Γ ∧ !insertDef y n₁ g) ∧
    (t = 2 → ∃ qr, !(qVecGraph LAct) qr r ∧ ∃ z, !(substsGraph LAct) z qr c ∧ ∃ f, !(freeGraph LAct) f z ∧
      ∃ nf, !(negGraph LAct) nf f ∧ ∃ sh, !(setShiftGraph LAct) sh Γ ∧ !insertDef y nf sh) ∧
    (t = 3 → ∃ f, !(freeGraph LAct) f p ∧ ∃ nf, !(negGraph LAct) nf f ∧ ∃ sh, !(setShiftGraph LAct) sh Γ ∧
      !insertDef y nf sh) ∧
    (t = 4 → ∃ n₁, !(negGraph LAct) n₁ i ∧ ∃ n₂, !(negGraph LAct) n₂ p₂ ∧ ∃ g, !insertDef g n₂ Γ ∧
      !insertDef y n₁ g) ∧
    (t = 6 → ∃ g, !goalFactDef g as c ∧ ∃ ng, !(negGraph LAct) ng g ∧ !insertDef y ng Γ) ∧
    (t = 7 → ∃ na, !(negGraph LAct) na i ∧ !insertDef y na Γ) ∧
    (t ≠ 0 → t ≠ 1 → t ≠ 2 → t ≠ 3 → t ≠ 4 → t ≠ 6 → t ≠ 7 → y = p)”

instance ctxAfter_defined : 𝚺₁-Function₂ (ctxAfter : V → V → V) via ctxAfterDef := .mk
  fun v ↦ by
    simp [ctxAfterDef, revV_defined.iff, subst.defined.iff, neg.defined.iff, qVec.defined.iff,
      free.defined.iff, setShift.defined.iff, goalFact_defined.iff, numeral_eq_natCast]
    unfold ctxAfter sTag sEv sC sGoalS sGoalU sLemA
    by_cases h0 : π₁ (v 2) = 0
    · simp [h0]
    by_cases h1 : π₁ (v 2) = 1
    · simp [h1]
    by_cases h2 : π₁ (v 2) = 2
    · simp [h2]
    by_cases h3 : π₁ (v 2) = 3
    · simp [h3]
    by_cases h4 : π₁ (v 2) = 4
    · simp [h4]
    by_cases h6 : π₁ (v 2) = 6
    · simp [h6]
    by_cases h7 : π₁ (v 2) = 7
    · simp [h7]
    · simp [h0, h1, h2, h3, h4, h6, h7]

instance ctxAfter_definable : 𝚺₁-Function₂ (ctxAfter : V → V → V) := ctxAfter_defined.to_definable

/-- The cost of a Horn use (`dlen_useHornCode_le` with `F := B·E` and `dlen dΛ ≤ N`):
`N + (m+3)G + (m+1)²(BE + m) + B + mE + 2m + 3 + (2j+1)(G + (j+1)BE + 1)`. -/
noncomputable def hornCost (N E G m j B : V) : V :=
  N + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
    + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)

/-- The cost of a totality-row use (`dlen_introFactCode_le`):
`N + (m + 2j + 10)G + (m+11)BE + (m+1)²(BE + m) + B + mE + 2m + (2j+1)((j+2)BE + 1) + 12`. -/
noncomputable def introCost (N E G m j B : V) : V :=
  N + (m + 2 * j + 10) * G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
    + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12

def hornCostDef : 𝚺₀.Semisentence 7 := .mkSigma
  “y N E G m j B. y = N + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
    + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)”

def introCostDef : 𝚺₀.Semisentence 7 := .mkSigma
  “y N E G m j B. y = N + (m + 2 * j + 10) * G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m)
    + B + m * E + 2 * m + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12”

instance hornCost_defined :
    𝚺₀.DefinedFunction (fun v : Fin 6 → V ↦ hornCost (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) hornCostDef := .mk
  fun v ↦ by simp [hornCostDef, hornCost]

instance introCost_defined :
    𝚺₀.DefinedFunction (fun v : Fin 6 → V ↦ introCost (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) introCostDef := .mk
  fun v ↦ by simp [introCostDef, introCost, numeral_eq_natCast]

/-- **The `dlen` increment of a step** (`G = |Γ|`, `m = len ev`, `j = len as`, `B = |B_ρ|`, `E`
the witness bound, `N ≥ dlen dΛ`), read off the `dlen_…_le` theorems:
tag 0 `hornCost`; tag 1 `hornCost + 2G + 6BE + 4`; tag 2 `introCost`;
tag 3 `4G + |setShift Γ| + 7|P| + 10` (`elimExistsCode` on an `axLFactCode` leaf);
tag 4 `2G + 3|p| + 3|q| + 4`; tag 5 `G + 1`;
tag 6 `goalCost G |goalFact s ū| E = 11G + 27·|goalFact s ū|·E + 2E + 42`;
tag 7 `dlen dA + 2G + 2|A| + 2`. -/
noncomputable def stepCost (N E Γ s : V) : V :=
  if sTag s = 0 then
    hornCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s)) (formulaLen LAct (impChainV LAct (sAs s) (sC s)))
  else if sTag s = 1 then
    hornCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s))
        (formulaLen LAct (impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))))
      + 2 * setLen LAct Γ + 6 * (formulaLen LAct (impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))) * E) + 4
  else if sTag s = 2 then
    introCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s)) (formulaLen LAct (impChainV LAct (sAs s) (^∃ (sC s))))
  else if sTag s = 3 then
    4 * setLen LAct Γ + setLen LAct (setShift LAct Γ) + 7 * formulaLen LAct (π₂ s) + 10
  else if sTag s = 4 then
    2 * setLen LAct Γ + 3 * formulaLen LAct (π₁ (π₂ s)) + 3 * formulaLen LAct (π₂ (π₂ s)) + 4
  else if sTag s = 6 then goalCost (setLen LAct Γ) (formulaLen LAct (goalFact (sGoalS s) (sGoalU s))) E
  else if sTag s = 7 then dlen TAct (sLemD s) + 2 * setLen LAct Γ + 2 * formulaLen LAct (sLemA s) + 2
  else setLen LAct Γ + 1

noncomputable def stepCostDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y N E Γ s. ∃ t, !pi₁Def t s ∧ ∃ p, !pi₂Def p s ∧ ∃ i, !pi₁Def i p ∧ ∃ p₂, !pi₂Def p₂ p ∧
    ∃ ev, !pi₁Def ev p₂ ∧ ∃ p₃, !pi₂Def p₃ p₂ ∧ ∃ as, !pi₁Def as p₃ ∧ ∃ c, !pi₂Def c p₃ ∧
    ∃ c₁, !pi₁Def c₁ c ∧ ∃ c₂, !pi₂Def c₂ c ∧ ∃ G, !(setLenDef LAct) G Γ ∧ ∃ m, !lenDef m ev ∧ ∃ j, !lenDef j as ∧
    (t = 0 → ∃ B₀, !(impChainVDef LAct) B₀ as c ∧ ∃ B, !(formulaLenGraph LAct) B B₀ ∧ !hornCostDef y N E G m j B) ∧
    (t = 1 → ∃ ca, !qqAndDef ca c₁ c₂ ∧ ∃ B₀, !(impChainVDef LAct) B₀ as ca ∧ ∃ B, !(formulaLenGraph LAct) B B₀ ∧
      ∃ h, !hornCostDef h N E G m j B ∧ y = h + 2 * G + 6 * (B * E) + 4) ∧
    (t = 2 → ∃ ce, !qqExsDef ce c ∧ ∃ B₀, !(impChainVDef LAct) B₀ as ce ∧ ∃ B, !(formulaLenGraph LAct) B B₀ ∧
      !introCostDef y N E G m j B) ∧
    (t = 3 → ∃ sh, !(setShiftGraph LAct) sh Γ ∧ ∃ Gs, !(setLenDef LAct) Gs sh ∧ ∃ P, !(formulaLenGraph LAct) P p ∧
      y = 4 * G + Gs + 7 * P + 10) ∧
    (t = 4 → ∃ P, !(formulaLenGraph LAct) P i ∧ ∃ Q, !(formulaLenGraph LAct) Q p₂ ∧ y = 2 * G + 3 * P + 3 * Q + 4) ∧
    (t = 6 → ∃ g, !goalFactDef g as c ∧ ∃ Q, !(formulaLenGraph LAct) Q g ∧ !goalCostDef y G Q E) ∧
    (t = 7 → ∃ dl, !(dlenDef TAct) dl p₂ ∧ ∃ A, !(formulaLenGraph LAct) A i ∧ y = dl + 2 * G + 2 * A + 2) ∧
    (t ≠ 0 → t ≠ 1 → t ≠ 2 → t ≠ 3 → t ≠ 4 → t ≠ 6 → t ≠ 7 → y = G + 1)”

instance stepCost_defined : 𝚺₁-Function₄ (stepCost : V → V → V → V → V) via stepCostDef := .mk
  fun v ↦ by
    simp [stepCostDef, setLen_defined.iff, impChainV_defined.iff, formulaLen.defined.iff, hornCost_defined.iff,
      introCost_defined.iff, setShift.defined.iff, goalFact_defined.iff, goalCost_defined.iff,
      (dlen_defined (T := TAct)).iff, numeral_eq_natCast]
    unfold stepCost sTag sEv sAs sC sGoalS sGoalU sLemA sLemD
    by_cases h0 : π₁ (v 4) = 0
    · simp [h0]
    by_cases h1 : π₁ (v 4) = 1
    · simp [h1]
    by_cases h2 : π₁ (v 4) = 2
    · simp [h2]
    by_cases h3 : π₁ (v 4) = 3
    · simp [h3]
    by_cases h4 : π₁ (v 4) = 4
    · simp [h4]
    by_cases h6 : π₁ (v 4) = 6
    · simp [h6]
    by_cases h7 : π₁ (v 4) = 7
    · simp [h7]
    · simp [h0, h1, h2, h3, h4, h6, h7]

instance stepCost_definable : 𝚺₁-Function₄ (stepCost : V → V → V → V → V) := stepCost_defined.to_definable

/-- The common hypotheses of the three Horn tags: a row index in range whose arity is the
witness count, both vectors of length `≤ M` (the standardness cap that lets the list theorems
of `Steps.lean` apply), closed witnesses of length `≤ E`, and every instantiated antecedent in
context. -/
def HornOK (tbl E M Γ s : V) : Prop :=
  sRow s < len tbl ∧ rowM tbl.[sRow s] = len (sEv s) ∧ len (sEv s) ≤ M ∧ len (sAs s) ≤ M ∧
  (∀ k < len (sEv s), IsSemiterm LAct 0 (sEv s).[k] ∧ termLen LAct (sEv s).[k] ≤ E) ∧
  (∀ k < len (sAs s), neg LAct (subst LAct (revV (sEv s)) (sAs s).[k]) ∈ Γ)

/-- The hypotheses of a `sGoal` step (Part C): closed witnesses of length `≤ E` and the four
negated facts in context. -/
def GoalOK (E Γ s : V) : Prop :=
  IsSemiterm LAct 0 (sGoalE s) ∧ termLen LAct (sGoalE s) ≤ E ∧
  IsSemiterm LAct 0 (sGoalN s) ∧ termLen LAct (sGoalN s) ≤ E ∧
  IsSemiterm LAct 0 (sGoalS s) ∧ termLen LAct (sGoalS s) ≤ E ∧
  IsSemiterm LAct 0 (sGoalU s) ∧ termLen LAct (sGoalU s) ≤ E ∧
  neg LAct (derFact (sGoalE s)) ∈ Γ ∧ neg LAct (fstIdxFact (sGoalS s) (sGoalE s)) ∈ Γ ∧
  neg LAct (dlenFact (sGoalE s) (sGoalN s)) ∈ Γ ∧ neg LAct (leFact (sGoalN s) (sGoalU s)) ∈ Γ

/-- The hypotheses of a `sLemma` step (Part C): a closed formula `A` with a supplied derivation
of `{A}` (`DerivationOf` is Δ₁ through `derivationOf`'s instance — `derivation` is never unfolded). -/
def LemmaOK (s : V) : Prop :=
  IsFormula LAct (sLemA s) ∧ DerivationOf TAct (sLemD s) (insert (sLemA s) 0)

instance goalOK_definable : 𝚫₁-Relation₃ (GoalOK : V → V → V → Prop) := by
  unfold GoalOK sGoalE sGoalN sGoalS sGoalU; definability

instance lemmaOK_definable : 𝚫₁-Predicate (LemmaOK : V → Prop) := by
  unfold LemmaOK sLemA sLemD; definability

/-- **A step is applicable** at `Γ` — exactly the hypotheses of the `_proof` theorems, per tag. -/
def StepOK (tbl E M Γ s : V) : Prop :=
  IsFormulaSet LAct Γ ∧
  ((sTag s = 0 ∧ HornOK tbl E M Γ s ∧ rowB tbl.[sRow s] = impChainV LAct (sAs s) (sC s)) ∨
   (sTag s = 1 ∧ HornOK tbl E M Γ s ∧ rowB tbl.[sRow s] = impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))) ∨
   (sTag s = 2 ∧ HornOK tbl E M Γ s ∧ rowB tbl.[sRow s] = impChainV LAct (sAs s) (^∃ (sC s))) ∨
   (sTag s = 3 ∧ IsSemiformula LAct 1 (π₂ s) ∧ neg LAct (^∃ (π₂ s)) ∈ Γ) ∨
   (sTag s = 4 ∧ IsFormula LAct (π₁ (π₂ s)) ∧ IsFormula LAct (π₂ (π₂ s)) ∧
      neg LAct ((π₁ (π₂ s)) ^⋏ (π₂ (π₂ s))) ∈ Γ) ∨
   (sTag s = 5 ∧ π₂ s ⊆ Γ) ∨
   (sTag s = 6 ∧ GoalOK E Γ s) ∨
   (sTag s = 7 ∧ LemmaOK s))

instance hornOK_definable : 𝚫₁-Relation₅ (HornOK : V → V → V → V → V → Prop) := by
  unfold HornOK sRow sEv sAs rowM; definability

instance stepOK_definable : 𝚫₁-Relation₅ (StepOK : V → V → V → V → V → Prop) := by
  unfold StepOK sTag sRow sAs sC rowB; definability

end stepLanguage

/-! ### B.3 The context vector and the chain builder (primitive recursion) -/

section chain

open LAct

namespace CtxVec

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y Γ₀ S. !mkVec₁Def y Γ₀”
  succ := .mkSigma “y ih i Γ₀ S. ∃ l, !nthDef l ih i ∧ ∃ s, !nthDef s S i ∧ ∃ g, !ctxAfterDef g l s ∧ !concatDef y ih g”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ ?[v 0]
  succ := fun v i ih ↦ concat ih (ctxAfter ih.[i] (v 1).[i])
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, ctxAfter_defined.iff]

end CtxVec

/-- `ctxVecAux Γ₀ S n = [Γ₀, ctxAfter Γ₀ S.[0], ctxAfter (…) S.[1], …]` (`n + 1` entries). -/
noncomputable def ctxVecAux (Γ₀ S n : V) : V := CtxVec.construction.result ![Γ₀, S] n

/-- **The context vector** of a step list: `ctxVec Γ₀ S = ctxVecAux Γ₀ S (len S)`, `len = len S + 1`,
entry `i` the context BEFORE step `i`, entry `len S` the final context. -/
noncomputable def ctxVec (Γ₀ S : V) : V := ctxVecAux Γ₀ S (len S)

@[simp] lemma ctxVecAux_zero (Γ₀ S : V) : ctxVecAux Γ₀ S 0 = ?[Γ₀] := by simp [ctxVecAux, CtxVec.construction]
@[simp] lemma ctxVecAux_succ (Γ₀ S n : V) :
    ctxVecAux Γ₀ S (n + 1) = concat (ctxVecAux Γ₀ S n) (ctxAfter (ctxVecAux Γ₀ S n).[n] S.[n]) := by
  simp [ctxVecAux, CtxVec.construction]

noncomputable def ctxVecAuxDef : 𝚺₁.Semisentence 4 := CtxVec.blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance ctxVecAux_defined : 𝚺₁-Function₃ (ctxVecAux : V → V → V → V) via ctxVecAuxDef := .mk
  fun v ↦ by simp [CtxVec.construction.result_defined_iff, ctxVecAuxDef]; rfl
instance ctxVecAux_definable : 𝚺₁-Function₃ (ctxVecAux : V → V → V → V) := ctxVecAux_defined.to_definable

noncomputable def ctxVecDef : 𝚺₁.Semisentence 3 := .mkSigma “y Γ₀ S. ∃ n, !lenDef n S ∧ !ctxVecAuxDef y Γ₀ S n”

instance ctxVec_defined : 𝚺₁-Function₂ (ctxVec : V → V → V) via ctxVecDef := .mk
  fun v ↦ by simp [ctxVecDef, ctxVecAux_defined.iff, ctxVec]
instance ctxVec_definable : 𝚺₁-Function₂ (ctxVec : V → V → V) := ctxVec_defined.to_definable

lemma len_ctxVecAux (Γ₀ S : V) : ∀ n : V, len (ctxVecAux Γ₀ S n) = n + 1 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ n ih => rw [ctxVecAux_succ, len_concat, ih]

@[simp] lemma len_ctxVec (Γ₀ S : V) : len (ctxVec Γ₀ S) = len S + 1 := len_ctxVecAux Γ₀ S (len S)

/-- Entries are stable under extension: `(ctxVecAux (n + k)).[i] = (ctxVecAux n).[i]` for `i ≤ n`. -/
lemma nth_ctxVecAux_add (Γ₀ S : V) : ∀ k : V, ∀ n i : V, i ≤ n →
    (ctxVecAux Γ₀ S (n + k)).[i] = (ctxVecAux Γ₀ S n).[i] := by
  intro k
  induction k using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro n i _; simp
  | succ k ih =>
    intro n i hi
    rw [← add_assoc, ctxVecAux_succ,
      concat_nth_lt _ _ (by rw [len_ctxVecAux]; exact lt_of_le_of_lt hi (lt_of_le_of_lt le_self_add (lt_add_one _))),
      ih n i hi]

@[simp] lemma nth_ctxVecAux_zero (Γ₀ S n : V) : (ctxVecAux Γ₀ S n).[0] = Γ₀ := by
  have := nth_ctxVecAux_add Γ₀ S n 0 0 le_rfl
  rw [zero_add] at this
  rw [this]; simp

/-- **The successor law**: the context after step `i` is `ctxAfter` of the context before it. -/
lemma nth_ctxVecAux_succ (Γ₀ S : V) {n i : V} (hi : i < n) :
    (ctxVecAux Γ₀ S n).[i + 1] = ctxAfter (ctxVecAux Γ₀ S n).[i] S.[i] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = (i + 1) + k := ⟨n - (i + 1), by rw [add_tsub_cancel_of_le (lt_iff_succ_le.mp hi)]⟩
  rw [nth_ctxVecAux_add Γ₀ S k (i + 1) (i + 1) le_rfl, nth_ctxVecAux_add Γ₀ S k (i + 1) i le_self_add,
    ctxVecAux_succ, concat_nth_len' _ _ (len_ctxVecAux Γ₀ S i), concat_nth_lt _ _ (by rw [len_ctxVecAux]; simp)]

@[simp] lemma nth_ctxVec_zero (Γ₀ S : V) : (ctxVec Γ₀ S).[0] = Γ₀ := nth_ctxVecAux_zero Γ₀ S _

lemma nth_ctxVec_succ (Γ₀ S : V) {i : V} (hi : i < len S) :
    (ctxVec Γ₀ S).[i + 1] = ctxAfter (ctxVec Γ₀ S).[i] S.[i] := nth_ctxVecAux_succ Γ₀ S hi

namespace ChainCode

noncomputable def blueprint : PR.Blueprint 4 where
  zero := .mkSigma “y tbl C S d. y = d”
  succ := .mkSigma “y ih j tbl C S d. ∃ Γ, !nthFromEndDef Γ C (j + 1) ∧ ∃ s, !nthFromEndDef s S j ∧
    ∃ r, !applyStepDef r tbl Γ s ih ∧ y = r”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ v 3
  succ := fun v j ih ↦ applyStep (v 0) (nthFromEnd (v 1) (j + 1)) (nthFromEnd (v 2) j) ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, nthFromEnd_defined.iff, applyStep_defined.iff]

end ChainCode

/-- `chainAux tbl C S d j`: the last `j` steps applied (from the end) to `d`, with `C` the context
vector: `g 0 = d`, `g (j + 1) = applyStep tbl C.[n − j − 1] S.[n − j − 1] (g j)`. -/
noncomputable def chainAux (tbl C S d j : V) : V := ChainCode.construction.result ![tbl, C, S, d] j

/-- **The chain builder**: `chainCode tbl Γ₀ S d = chainAux tbl (ctxVec Γ₀ S) S d (len S)`. -/
noncomputable def chainCode (tbl Γ₀ S d : V) : V := chainAux tbl (ctxVec Γ₀ S) S d (len S)

@[simp] lemma chainAux_zero (tbl C S d : V) : chainAux tbl C S d 0 = d := by simp [chainAux, ChainCode.construction]
@[simp] lemma chainAux_succ (tbl C S d j : V) :
    chainAux tbl C S d (j + 1) = applyStep tbl (nthFromEnd C (j + 1)) (nthFromEnd S j) (chainAux tbl C S d j) := by
  simp [chainAux, ChainCode.construction]

noncomputable def chainAuxDef : 𝚺₁.Semisentence 6 :=
  ChainCode.blueprint.resultDef |>.rew (Rew.subst ![#0, #5, #1, #2, #3, #4])

instance chainAux_defined : 𝚺₁-Function₅ (chainAux : V → V → V → V → V → V) via chainAuxDef := .mk
  fun v ↦ by simp [ChainCode.construction.result_defined_iff, chainAuxDef]; rfl
instance chainAux_definable : 𝚺₁.DefinableFunction₅ (chainAux : V → V → V → V → V → V) :=
  chainAux_defined.to_definable

noncomputable def chainCodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y tbl Γ₀ S d. ∃ C, !ctxVecDef C Γ₀ S ∧ ∃ n, !lenDef n S ∧ !chainAuxDef y tbl C S d n”

instance chainCode_defined : 𝚺₁-Function₄ (chainCode : V → V → V → V → V) via chainCodeDef := .mk
  fun v ↦ by simp [chainCodeDef, ctxVec_defined.iff, chainAux_defined.iff, chainCode]
instance chainCode_definable : 𝚺₁-Function₄ (chainCode : V → V → V → V → V) := chainCode_defined.to_definable

namespace CostSum

noncomputable def blueprint : PR.Blueprint 4 where
  zero := .mkSigma “y N E C S. y = 0”
  succ := .mkSigma “y ih j N E C S. ∃ Γ, !nthFromEndDef Γ C (j + 1) ∧ ∃ s, !nthFromEndDef s S j ∧
    ∃ c, !stepCostDef c N E Γ s ∧ y = ih + c”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v j ih ↦ ih + stepCost (v 0) (v 1) (nthFromEnd (v 2) (j + 1)) (nthFromEnd (v 3) j)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, nthFromEnd_defined.iff, stepCost_defined.iff]

end CostSum

/-- `costAux N E C S j`: the summed `stepCost` of the last `j` steps (from the end, like `chainAux`). -/
noncomputable def costAux (N E C S j : V) : V := CostSum.construction.result ![N, E, C, S] j

/-- **The total cost** of a step list: `costSum N E Γ₀ S = costAux N E (ctxVec Γ₀ S) S (len S)`. -/
noncomputable def costSum (N E Γ₀ S : V) : V := costAux N E (ctxVec Γ₀ S) S (len S)

@[simp] lemma costAux_zero (N E C S : V) : costAux N E C S 0 = 0 := by simp [costAux, CostSum.construction]
@[simp] lemma costAux_succ (N E C S j : V) :
    costAux N E C S (j + 1) = costAux N E C S j + stepCost N E (nthFromEnd C (j + 1)) (nthFromEnd S j) := by
  simp [costAux, CostSum.construction]

noncomputable def costAuxDef : 𝚺₁.Semisentence 6 :=
  CostSum.blueprint.resultDef |>.rew (Rew.subst ![#0, #5, #1, #2, #3, #4])

instance costAux_defined : 𝚺₁-Function₅ (costAux : V → V → V → V → V → V) via costAuxDef := .mk
  fun v ↦ by simp [CostSum.construction.result_defined_iff, costAuxDef]; rfl
instance costAux_definable : 𝚺₁.DefinableFunction₅ (costAux : V → V → V → V → V → V) :=
  costAux_defined.to_definable

noncomputable def costSumDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y N E Γ₀ S. ∃ C, !ctxVecDef C Γ₀ S ∧ ∃ n, !lenDef n S ∧ !costAuxDef y N E C S n”

instance costSum_defined : 𝚺₁-Function₄ (costSum : V → V → V → V → V) via costSumDef := .mk
  fun v ↦ by simp [costSumDef, ctxVec_defined.iff, costAux_defined.iff, costSum]
instance costSum_definable : 𝚺₁-Function₄ (costSum : V → V → V → V → V) := costSum_defined.to_definable

end chain

/-! ### B.4 The per-step theorems: `applyStep` derives `Γ` and costs `stepCost` -/

/-- Inversion of `isSemiformula_impChain`. -/
lemma isSemiformula_of_impChain {n : V} : ∀ {as : List V} {c : V}, IsSemiformula L n (impChain L as c) →
    (∀ a ∈ as, IsSemiformula L n a) ∧ IsSemiformula L n c
  | [], _, h => ⟨by simp, h⟩
  | a :: as, c, h => by
    rw [impChain_cons, IsSemiformula.imp] at h
    obtain ⟨ih₁, ih₂⟩ := isSemiformula_of_impChain h.2
    refine ⟨fun a' ha' ↦ ?_, ih₂⟩
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact h.1
    · exact ih₁ a' ha'

/-- **The standardness bridge**: a vector of length `≤ M` (`M` a standard numeral) is `vecOf` of
a Lean list — so the list theorems of `Steps.lean` apply to it. -/
lemma exists_list_of_len_le : ∀ (M : ℕ) (v : V), len v ≤ (M : V) → ∃ l : List V, v = vecOf l
  | 0, v, h => ⟨[], by
      rw [vecOf_nil]
      exact len_zero_iff_eq_nil.mp (le_antisymm (by simpa using h) zero_le)⟩
  | M + 1, v, h => by
    rcases nil_or_adjoin v with rfl | ⟨x, v', rfl⟩
    · exact ⟨[], rfl⟩
    · obtain ⟨l, rfl⟩ := exists_list_of_len_le M v'
        (by rw [len_adjoin, Nat.cast_succ] at h; exact le_of_add_le_add_right h)
      exact ⟨x :: l, rfl⟩

section perStep

open LAct

lemma applyStep_tag0 {tbl Γ s e : V} (h : sTag s = 0) :
    applyStep tbl Γ s e = useHornV LAct Γ (sEv s) (sAs s) (sC s) (rowD tbl.[sRow s]) e := by simp [applyStep, h]
lemma applyStep_tag1 {tbl Γ s e : V} (h : sTag s = 1) :
    applyStep tbl Γ s e = useHornAndV LAct Γ (sEv s) (sAs s) (π₁ (sC s)) (π₂ (sC s)) (rowD tbl.[sRow s]) e := by
  simp [applyStep, h]
lemma applyStep_tag2 {tbl Γ s e : V} (h : sTag s = 2) :
    applyStep tbl Γ s e = introFactV LAct Γ (sEv s) (sAs s) (sC s) (rowD tbl.[sRow s]) e := by simp [applyStep, h]
lemma applyStep_tag3 {tbl Γ s e : V} (h : sTag s = 3) :
    applyStep tbl Γ s e = elimExistsCode LAct Γ (π₂ s) (axLFactCode Γ (^∃ (π₂ s))) e := by simp [applyStep, h]
lemma applyStep_tag4 {tbl Γ s e : V} (h : sTag s = 4) :
    applyStep tbl Γ s e = splitAndCode LAct Γ (π₁ (π₂ s)) (π₂ (π₂ s)) e := by simp [applyStep, h]
lemma applyStep_tag5 {tbl Γ s e : V} (h : sTag s = 5) : applyStep tbl Γ s e = wkDropCode Γ e := by
  simp [applyStep, h]
lemma applyStep_tag6 {tbl Γ s e : V} (h : sTag s = 6) :
    applyStep tbl Γ s e =
      cutRule Γ (goalFact (sGoalS s) (sGoalU s)) (goalLeafCode Γ (sGoalE s) (sGoalN s) (sGoalS s) (sGoalU s)) e := by
  simp [applyStep, h]
lemma applyStep_tag7 {tbl Γ s e : V} (h : sTag s = 7) :
    applyStep tbl Γ s e = cutRule Γ (sLemA s) (wkToCode (insert (sLemA s) Γ) (sLemD s)) e := by
  simp [applyStep, h]

lemma ctxAfter_tag0 {Γ s : V} (h : sTag s = 0) :
    ctxAfter Γ s = insert (neg LAct (subst LAct (revV (sEv s)) (sC s))) Γ := by simp [ctxAfter, h]
lemma ctxAfter_tag1 {Γ s : V} (h : sTag s = 1) :
    ctxAfter Γ s = insert (neg LAct (subst LAct (revV (sEv s)) (π₁ (sC s))))
      (insert (neg LAct (subst LAct (revV (sEv s)) (π₂ (sC s)))) Γ) := by simp [ctxAfter, h]
lemma ctxAfter_tag2 {Γ s : V} (h : sTag s = 2) :
    ctxAfter Γ s = insert (neg LAct (free LAct (subst LAct (qVec LAct (revV (sEv s))) (sC s)))) (setShift LAct Γ) := by
  simp [ctxAfter, h]
lemma ctxAfter_tag3 {Γ s : V} (h : sTag s = 3) :
    ctxAfter Γ s = insert (neg LAct (free LAct (π₂ s))) (setShift LAct Γ) := by simp [ctxAfter, h]
lemma ctxAfter_tag4 {Γ s : V} (h : sTag s = 4) :
    ctxAfter Γ s = insert (neg LAct (π₁ (π₂ s))) (insert (neg LAct (π₂ (π₂ s))) Γ) := by simp [ctxAfter, h]
lemma ctxAfter_tag5 {Γ s : V} (h : sTag s = 5) : ctxAfter Γ s = π₂ s := by simp [ctxAfter, h]
lemma ctxAfter_tag6 {Γ s : V} (h : sTag s = 6) :
    ctxAfter Γ s = insert (neg LAct (goalFact (sGoalS s) (sGoalU s))) Γ := by simp [ctxAfter, h]
lemma ctxAfter_tag7 {Γ s : V} (h : sTag s = 7) : ctxAfter Γ s = insert (neg LAct (sLemA s)) Γ := by
  simp [ctxAfter, h]

lemma stepCost_tag0 {N E Γ s : V} (h : sTag s = 0) :
    stepCost N E Γ s = hornCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s))
      (formulaLen LAct (impChainV LAct (sAs s) (sC s))) := by simp [stepCost, h]
lemma stepCost_tag1 {N E Γ s : V} (h : sTag s = 1) :
    stepCost N E Γ s = hornCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s))
        (formulaLen LAct (impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))))
      + 2 * setLen LAct Γ + 6 * (formulaLen LAct (impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))) * E) + 4 := by
  simp [stepCost, h]
lemma stepCost_tag2 {N E Γ s : V} (h : sTag s = 2) :
    stepCost N E Γ s = introCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s))
      (formulaLen LAct (impChainV LAct (sAs s) (^∃ (sC s)))) := by simp [stepCost, h]
lemma stepCost_tag3 {N E Γ s : V} (h : sTag s = 3) :
    stepCost N E Γ s = 4 * setLen LAct Γ + setLen LAct (setShift LAct Γ) + 7 * formulaLen LAct (π₂ s) + 10 := by
  simp [stepCost, h]
lemma stepCost_tag4 {N E Γ s : V} (h : sTag s = 4) :
    stepCost N E Γ s = 2 * setLen LAct Γ + 3 * formulaLen LAct (π₁ (π₂ s)) + 3 * formulaLen LAct (π₂ (π₂ s)) + 4 := by
  simp [stepCost, h]
lemma stepCost_tag5 {N E Γ s : V} (h : sTag s = 5) : stepCost N E Γ s = setLen LAct Γ + 1 := by simp [stepCost, h]
lemma stepCost_tag6 {N E Γ s : V} (h : sTag s = 6) :
    stepCost N E Γ s = goalCost (setLen LAct Γ) (formulaLen LAct (goalFact (sGoalS s) (sGoalU s))) E := by
  simp [stepCost, h]
lemma stepCost_tag7 {N E Γ s : V} (h : sTag s = 7) :
    stepCost N E Γ s = dlen TAct (sLemD s) + 2 * setLen LAct Γ + 2 * formulaLen LAct (sLemA s) + 2 := by
  simp [stepCost, h]

/-- The Horn hypotheses in list form (through the standardness bridge). -/
lemma HornOK.lists (M : ℕ) {tbl E Γ s : V} (h : HornOK tbl E (M : V) Γ s) :
    ∃ (es l : List V), sEv s = vecOf es ∧ sAs s = vecOf l ∧ rowM tbl.[sRow s] = (es.length : V) ∧
      (∀ e ∈ es, IsTerm LAct e ∧ termLen LAct e ≤ E) ∧
      (∀ a ∈ l, neg LAct (subst LAct (revV (vecOf es)) a) ∈ Γ) := by
  obtain ⟨hi, hm, hM₁, hM₂, hes, hneg⟩ := h
  obtain ⟨es, hes_eq⟩ := exists_list_of_len_le M (sEv s) hM₁
  obtain ⟨l, hl_eq⟩ := exists_list_of_len_le M (sAs s) hM₂
  refine ⟨es, l, hes_eq, hl_eq, by rw [hm, hes_eq, len_vecOf], fun e he ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have := hes (k : V) (by rw [hes_eq, len_vecOf]; exact_mod_cast hk)
    rwa [hes_eq, nth_vecOf es k hk] at this
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    have := hneg (k : V) (by rw [hl_eq, len_vecOf]; exact_mod_cast hk)
    rwa [hl_eq, hes_eq, nth_vecOf l k hk] at this

/-- **One step derives its context** from a derivation of `ctxAfter`. -/
theorem applyStep_proof (M : ℕ) {tbl N E Γ s e : V} (htbl : TableOK tbl N) (hok : StepOK tbl E (M : V) Γ s)
    (he : DerivationOf TAct e (ctxAfter Γ s)) : DerivationOf TAct (applyStep tbl Γ s e) Γ := by
  obtain ⟨hΓ, h⟩ := hok
  rcases h with ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hP, hmem⟩ | ⟨ht, hp, hq, hmem⟩ | ⟨ht, hsub⟩ |
    ⟨ht, he₁, hel₁, hn₁, hnl₁, hs₁, hsl₁, hu₁, hul₁, hm₁, hm₂, hm₃, hm₄⟩ | ⟨ht, hA, hdA⟩
  · -- sUseHorn
    obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag0 ht, hes_eq, subst_revV_vecOf es hc hes] at he
    rw [applyStep_tag0 ht, hes_eq, hl_eq, useHornV_vecOf Γ es l has hc hes]
    exact useHornCode_proof has hc hes hΓ (subset_refl Γ) hneg hΛ he
  · -- sUseHornAnd
    obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    obtain ⟨hc₁, hc₂⟩ := IsSemiformula.and.mp hc
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag1 ht, hes_eq, subst_revV_vecOf es hc₁ hes, subst_revV_vecOf es hc₂ hes] at he
    rw [applyStep_tag1 ht, hes_eq, hl_eq, useHornAndV_vecOf Γ es l has hc₁ hc₂ hes]
    exact useHornAndCode_proof has hc₁ hc₂ hes hΓ (subset_refl Γ) hneg hΛ he
  · -- sIntroFact
    obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    have hR : IsSemiformula LAct ((es.length : V) + 1) (sC s) := IsSemiformula.exs.mp hc
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag2 ht, hes_eq, subst_qVec_revV_vecOf es hR hes] at he
    rw [applyStep_tag2 ht, hes_eq, hl_eq, introFactV_vecOf Γ es l has hR hes]
    exact introFactCode_proof has hR hes hΓ hneg hΛ he
  · -- sElimExs
    rw [ctxAfter_tag3 ht] at he
    rw [applyStep_tag3 ht]
    have hE : IsFormula LAct (^∃ (π₂ s)) := by simp [hP]
    exact elimExistsCode_proof hP hΓ (subset_refl Γ) (axLFactCode_proof hE hΓ hmem) he
  · -- sSplit
    rw [ctxAfter_tag4 ht] at he
    rw [applyStep_tag4 ht]
    have := splitAndCode_proof hp hq hΓ (subset_refl Γ) he
    rwa [insert_eq_self_of_mem hmem] at this
  · -- sWkDrop
    rw [ctxAfter_tag5 ht] at he
    rw [applyStep_tag5 ht]
    exact wkDropCode_proof hΓ hsub he
  · -- sGoal
    rw [ctxAfter_tag6 ht] at he
    rw [applyStep_tag6 ht]
    exact ⟨by simp, Derivation.cutRule (goalLeafCode_proof he₁ hn₁ hs₁ hu₁ hΓ hm₁ hm₂ hm₃ hm₄) he⟩
  · -- sLemma
    rw [ctxAfter_tag7 ht] at he
    rw [applyStep_tag7 ht]
    exact lemmaCut_proof hΓ hA hdA he

/-- The context after an applicable step is a formula set. -/
lemma isFormulaSet_ctxAfter (M : ℕ) {tbl N E Γ s : V} (htbl : TableOK tbl N) (hok : StepOK tbl E (M : V) Γ s) :
    IsFormulaSet LAct (ctxAfter Γ s) := by
  obtain ⟨hΓ, h⟩ := hok
  rcases h with ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hP, hmem⟩ | ⟨ht, hp, hq, hmem⟩ | ⟨ht, hsub⟩ |
    ⟨ht, he₁, hel₁, hn₁, hnl₁, hs₁, hsl₁, hu₁, hul₁, hm₁, hm₂, hm₃, hm₄⟩ | ⟨ht, hA, hdA⟩
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    rw [ctxAfter_tag0 ht, hes_eq, subst_revV_vecOf es hc hes]
    simp [hΓ, isFormula_instOuter es hc hes]
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    obtain ⟨hc₁, hc₂⟩ := IsSemiformula.and.mp hc
    rw [ctxAfter_tag1 ht, hes_eq, subst_revV_vecOf es hc₁ hes, subst_revV_vecOf es hc₂ hes]
    simp [hΓ, isFormula_instOuter es hc₁ hes, isFormula_instOuter es hc₂ hes]
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    have hR : IsSemiformula LAct ((es.length : V) + 1) (sC s) := IsSemiformula.exs.mp hc
    rw [ctxAfter_tag2 ht, hes_eq, subst_qVec_revV_vecOf es hR hes]
    simp [hΓ, isSemiformula_one_instOuterAt es hR hes]
  · rw [ctxAfter_tag3 ht]; simp [hΓ, hP]
  · rw [ctxAfter_tag4 ht]; simp [hΓ, hp, hq]
  · rw [ctxAfter_tag5 ht]
    exact fun p hp ↦ hΓ p (subset_iff.mp hsub p hp)
  · rw [ctxAfter_tag6 ht]; simp [hΓ, isFormula_goalFact hs₁ hu₁]
  · rw [ctxAfter_tag7 ht]; simp [hΓ, hA]

/-- **Persistence** (DESIGN §3.4): a fact in `Γ` survives a non-shifting step … -/
lemma mem_ctxAfter_of_noShift {Γ s x : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 4) (hx : x ∈ Γ) :
    x ∈ ctxAfter Γ s := by
  rcases h with h | h | h
  · rw [ctxAfter_tag0 h]; simp [hx]
  · rw [ctxAfter_tag1 h]; simp [hx]
  · rw [ctxAfter_tag4 h]; simp [hx]

/-- Part C: the two cuts do not shift either. -/
lemma mem_ctxAfter_tag6 {Γ s x : V} (h : sTag s = 6) (hx : x ∈ Γ) : x ∈ ctxAfter Γ s := by
  rw [ctxAfter_tag6 h]; simp [hx]
lemma mem_ctxAfter_tag7 {Γ s x : V} (h : sTag s = 7) (hx : x ∈ Γ) : x ∈ ctxAfter Γ s := by
  rw [ctxAfter_tag7 h]; simp [hx]
/-- `mem_ctxAfter_of_noShift` over all five non-shifting tags (0, 1, 4, 6, 7). -/
lemma mem_ctxAfter_of_noShift' {Γ s x : V}
    (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7) (hx : x ∈ Γ) :
    x ∈ ctxAfter Γ s := by
  rcases h with h | h | h | h | h
  · exact mem_ctxAfter_of_noShift (Or.inl h) hx
  · exact mem_ctxAfter_of_noShift (Or.inr (Or.inl h)) hx
  · exact mem_ctxAfter_of_noShift (Or.inr (Or.inr h)) hx
  · exact mem_ctxAfter_tag6 h hx
  · exact mem_ctxAfter_tag7 h hx

/-- … and reappears SHIFTED after an eigenvariable step. -/
lemma mem_ctxAfter_of_shift {Γ s x : V} (h : sTag s = 2 ∨ sTag s = 3) (hx : x ∈ Γ) :
    shift LAct x ∈ ctxAfter Γ s := by
  rcases h with h | h
  · rw [ctxAfter_tag2 h]; simp [mem_setShift_iff]; exact Or.inr ⟨x, hx, rfl⟩
  · rw [ctxAfter_tag3 h]; simp [mem_setShift_iff]; exact Or.inr ⟨x, hx, rfl⟩

lemma hornCost_bound {a N d G m j B E : V} (h : a ≤ N) :
    a + d + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
        + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)
      ≤ d + hornCost N E G m j B := by
  unfold hornCost
  calc a + d + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
          + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)
      = a + (d + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
          + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)) := by ring
    _ ≤ N + (d + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
          + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)) := add_le_add h le_rfl
    _ = _ := by ring

lemma hornAndCost_bound {a N d G m j B E : V} (h : a ≤ N) :
    a + (d + 2 * G + 6 * (B * E) + 4) + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
        + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)
      ≤ d + (hornCost N E G m j B + 2 * G + 6 * (B * E) + 4) := by
  unfold hornCost
  calc a + (d + 2 * G + 6 * (B * E) + 4) + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
          + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)
      = a + (d + 2 * G + 6 * (B * E) + 4 + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
          + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)) := by ring
    _ ≤ N + (d + 2 * G + 6 * (B * E) + 4 + (m + 3) * G + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m + 3
          + (2 * j + 1) * (G + (j + 1) * (B * E) + 1)) := add_le_add h le_rfl
    _ = _ := by ring

lemma introCost_bound {a N d G m j B E : V} (h : a ≤ N) :
    a + d + (m + 2 * j + 10) * G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
        + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12
      ≤ d + introCost N E G m j B := by
  unfold introCost
  calc a + d + (m + 2 * j + 10) * G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
          + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12
      = a + (d + (m + 2 * j + 10) * G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
          + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12) := by ring
    _ ≤ N + (d + (m + 2 * j + 10) * G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
          + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12) := add_le_add h le_rfl
    _ = _ := by ring

/-- **One step costs at most `stepCost`.** -/
theorem dlen_applyStep_le (M : ℕ) {tbl N E Γ s e : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hok : StepOK tbl E (M : V) Γ s) (he : DerivationOf TAct e (ctxAfter Γ s)) :
    dlen TAct (applyStep tbl Γ s e) ≤ dlen TAct e + stepCost N E Γ s := by
  obtain ⟨hΓ, h⟩ := hok
  rcases h with ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hP, hmem⟩ | ⟨ht, hp, hq, hmem⟩ | ⟨ht, hsub⟩ |
    ⟨ht, he₁, hel₁, hn₁, hnl₁, hs₁, hsl₁, hu₁, hul₁, hm₁, hm₂, hm₃, hm₄⟩ | ⟨ht, hA, hdA⟩
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag0 ht, hes_eq, subst_revV_vecOf es hc hes] at he
    rw [applyStep_tag0 ht, stepCost_tag0 ht, hes_eq, hl_eq, len_vecOf, len_vecOf, impChainV_vecOf,
      useHornV_vecOf Γ es l has hc hes]
    exact le_trans (dlen_useHornCode_le hE has hc hes' hΓ (subset_refl Γ) hneg hΛ he le_rfl)
      (hornCost_bound hrow.2.2)
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    obtain ⟨hc₁, hc₂⟩ := IsSemiformula.and.mp hc
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag1 ht, hes_eq, subst_revV_vecOf es hc₁ hes, subst_revV_vecOf es hc₂ hes] at he
    rw [applyStep_tag1 ht, stepCost_tag1 ht, hes_eq, hl_eq, len_vecOf, len_vecOf, impChainV_vecOf,
      useHornAndV_vecOf Γ es l has hc₁ hc₂ hes]
    exact le_trans (dlen_useHornAndCode_le hE has hc₁ hc₂ hes' hΓ (subset_refl Γ) hneg hΛ he le_rfl)
      (hornAndCost_bound hrow.2.2)
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    have hR : IsSemiformula LAct ((es.length : V) + 1) (sC s) := IsSemiformula.exs.mp hc
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag2 ht, hes_eq, subst_qVec_revV_vecOf es hR hes] at he
    rw [applyStep_tag2 ht, stepCost_tag2 ht, hes_eq, hl_eq, len_vecOf, len_vecOf, impChainV_vecOf,
      introFactV_vecOf Γ es l has hR hes]
    exact le_trans (dlen_introFactCode_le hE has hR hes' hΓ hneg hΛ he le_rfl) (introCost_bound hrow.2.2)
  · rw [ctxAfter_tag3 ht] at he
    rw [applyStep_tag3 ht, stepCost_tag3 ht]
    have hE' : IsFormula LAct (^∃ (π₂ s)) := by simp [hP]
    have hD := axLFactCode_proof (T := TAct) hE' hΓ hmem
    have hDl := dlen_axLFactCode_le (T := TAct) hE' hΓ hmem
    rw [formulaLen_exs hP.isUFormula] at hDl
    calc dlen TAct (elimExistsCode LAct Γ (π₂ s) (axLFactCode Γ (^∃ (π₂ s))) e)
        ≤ dlen TAct (axLFactCode Γ (^∃ (π₂ s))) + dlen TAct e + 3 * setLen LAct Γ + setLen LAct (setShift LAct Γ)
            + 6 * formulaLen LAct (π₂ s) + 8 := dlen_elimExistsCode_le hP hΓ (subset_refl Γ) hD he
      _ ≤ (setLen LAct Γ + (formulaLen LAct (π₂ s) + 1) + 1) + dlen TAct e + 3 * setLen LAct Γ
            + setLen LAct (setShift LAct Γ) + 6 * formulaLen LAct (π₂ s) + 8 := by gcongr
      _ = _ := by ring
  · rw [ctxAfter_tag4 ht] at he
    rw [applyStep_tag4 ht, stepCost_tag4 ht]
    exact le_trans (dlen_splitAndCode_le hp hq hΓ (subset_refl Γ) he) (le_of_eq (by ring))
  · rw [ctxAfter_tag5 ht] at he
    rw [applyStep_tag5 ht, stepCost_tag5 ht, ← add_assoc]
    exact dlen_wkDropCode_le hΓ hsub he
  · rw [ctxAfter_tag6 ht] at he
    rw [applyStep_tag6 ht, stepCost_tag6 ht]
    have hleaf := goalLeafCode_proof he₁ hn₁ hs₁ hu₁ hΓ hm₁ hm₂ hm₃ hm₄
    have hpf : DerivationOf TAct (cutRule Γ (goalFact (sGoalS s) (sGoalU s))
        (goalLeafCode Γ (sGoalE s) (sGoalN s) (sGoalS s) (sGoalU s)) e) Γ :=
      ⟨by simp, Derivation.cutRule hleaf he⟩
    have hc : dlen TAct (cutRule Γ (goalFact (sGoalS s) (sGoalU s))
        (goalLeafCode Γ (sGoalE s) (sGoalN s) (sGoalS s) (sGoalU s)) e) =
        setLen LAct Γ + dlen TAct (goalLeafCode Γ (sGoalE s) (sGoalN s) (sGoalS s) (sGoalU s)) + dlen TAct e + 1 :=
      dlen_eq_of_graph hpf.2 (DlenGraph.cutRule_iff.mpr ⟨_, _, dlen_graph hleaf.2, dlen_graph he.2, rfl⟩)
    have hl := dlen_goalLeafCode_le hE he₁ hel₁ hn₁ hnl₁ hs₁ hu₁ hΓ hm₁ hm₂ hm₃ hm₄
    have hQ : formulaLen LAct (goalBody (sGoalS s) (sGoalU s)) ≤ formulaLen LAct (goalFact (sGoalS s) (sGoalU s)) := by
      rw [formulaLen_goalFact hs₁ hu₁]; exact le_self_add
    rw [hc]
    unfold goalCost
    calc setLen LAct Γ + dlen TAct (goalLeafCode Γ (sGoalE s) (sGoalN s) (sGoalS s) (sGoalU s)) + dlen TAct e + 1
        ≤ setLen LAct Γ + (10 * setLen LAct Γ + 27 * (formulaLen LAct (goalFact (sGoalS s) (sGoalU s)) * E)
            + 2 * E + 41) + dlen TAct e + 1 := by
          gcongr
          exact le_trans hl (by gcongr)
      _ = _ := by ring
  · rw [ctxAfter_tag7 ht] at he
    rw [applyStep_tag7 ht, stepCost_tag7 ht]
    exact dlen_lemmaCut_le hΓ hA hdA he

end perStep

/-! ### B.5 The chain theorems: `chainCode` derives `Γ₀` and costs `costSum` -/

section chainTheorems

open LAct

/-- **The invariant from the end**: the last `j` steps applied to `d` derive the context `C.[n − j]`. -/
theorem chainAux_proof (M : ℕ) {tbl N E C S d n : V} (htbl : TableOK tbl N) (hC : len C = n + 1) (hS : len S = n)
    (hok : ∀ i < n, StepOK tbl E (M : V) C.[i] S.[i]) (hsucc : ∀ i < n, C.[i + 1] = ctxAfter C.[i] S.[i])
    (hd : DerivationOf TAct d C.[n]) : ∀ j ≤ n, DerivationOf TAct (chainAux tbl C S d j) C.[n - j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simpa using hd
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := le_trans le_self_add hj
    have ih' := ih hj'
    obtain ⟨i, rfl⟩ : ∃ i, n = i + (j + 1) := ⟨n - (j + 1), (tsub_add_cancel_of_le hj).symm⟩
    have hi : i < i + (j + 1) := lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have h1 : i + (j + 1) - j = i + 1 := by
      rw [show i + (j + 1) = (i + 1) + j by ring, add_tsub_cancel_right]
    rw [h1, hsucc i hi] at ih'
    rw [chainAux_succ, add_tsub_cancel_right, nthFromEnd_eq (a := i) (by rw [hC, add_assoc]),
      nthFromEnd_eq (a := i) hS]
    exact applyStep_proof M htbl (hok i hi) ih'

/-- **`chainCode` derives `Γ₀`** when every step is applicable at its context and the
continuation derives the final context. -/
theorem chainCode_proof (M : ℕ) {tbl N E Γ₀ S d : V} (htbl : TableOK tbl N)
    (hok : ∀ i < len S, StepOK tbl E (M : V) (ctxVec Γ₀ S).[i] S.[i])
    (hd : DerivationOf TAct d (ctxVec Γ₀ S).[len S]) : DerivationOf TAct (chainCode tbl Γ₀ S d) Γ₀ := by
  have := chainAux_proof M htbl (len_ctxVec Γ₀ S) rfl hok (fun _ hi ↦ nth_ctxVec_succ Γ₀ S hi) hd (len S) le_rfl
  rwa [tsub_self, nth_ctxVec_zero] at this

/-- The length invariant from the end. -/
theorem dlen_chainAux_le (M : ℕ) {tbl N E C S d n : V} (hE : 1 ≤ E) (htbl : TableOK tbl N) (hC : len C = n + 1)
    (hS : len S = n) (hok : ∀ i < n, StepOK tbl E (M : V) C.[i] S.[i])
    (hsucc : ∀ i < n, C.[i + 1] = ctxAfter C.[i] S.[i]) (hd : DerivationOf TAct d C.[n]) :
    ∀ j ≤ n, dlen TAct (chainAux tbl C S d j) ≤ dlen TAct d + costAux N E C S j := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := le_trans le_self_add hj
    have hder := chainAux_proof M htbl hC hS hok hsucc hd j hj'
    have ih' := ih hj'
    obtain ⟨i, rfl⟩ : ∃ i, n = i + (j + 1) := ⟨n - (j + 1), (tsub_add_cancel_of_le hj).symm⟩
    have hi : i < i + (j + 1) := lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have h1 : i + (j + 1) - j = i + 1 := by
      rw [show i + (j + 1) = (i + 1) + j by ring, add_tsub_cancel_right]
    rw [h1, hsucc i hi] at hder
    rw [chainAux_succ, costAux_succ, nthFromEnd_eq (a := i) (by rw [hC, add_assoc]), nthFromEnd_eq (a := i) hS,
      ← add_assoc]
    exact le_trans (dlen_applyStep_le M hE htbl (hok i hi) hder) (add_le_add ih' le_rfl)

/-- **The length of a chain**: `dlen (chainCode tbl Γ₀ S d) ≤ dlen d + costSum N E Γ₀ S`. -/
theorem dlen_chainCode_le (M : ℕ) {tbl N E Γ₀ S d : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hok : ∀ i < len S, StepOK tbl E (M : V) (ctxVec Γ₀ S).[i] S.[i])
    (hd : DerivationOf TAct d (ctxVec Γ₀ S).[len S]) :
    dlen TAct (chainCode tbl Γ₀ S d) ≤ dlen TAct d + costSum N E Γ₀ S :=
  dlen_chainAux_le M hE htbl (len_ctxVec Γ₀ S) rfl hok (fun _ hi ↦ nth_ctxVec_succ Γ₀ S hi) hd (len S) le_rfl

/-- Every context of an applicable chain is a formula set. -/
theorem ctxVec_isFormulaSet (M : ℕ) {tbl N E Γ₀ S : V} (htbl : TableOK tbl N) (hΓ₀ : IsFormulaSet LAct Γ₀)
    (hok : ∀ i < len S, StepOK tbl E (M : V) (ctxVec Γ₀ S).[i] S.[i]) :
    ∀ i ≤ len S, IsFormulaSet LAct (ctxVec Γ₀ S).[i] := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · rw [nth_ctxVec_zero]; exact hΓ₀
  · have hi' : i < len S := lt_of_lt_of_le (lt_add_one i) hi
    rw [nth_ctxVec_succ Γ₀ S hi']
    exact isFormulaSet_ctxAfter M htbl (hok i hi')

/-- **Smoke test**: a two-step chain unfolds to the two applications, inner step at `ctxAfter Γ₀ s₁`. -/
theorem chainCode_two (tbl Γ₀ s₁ s₂ d : V) :
    chainCode tbl Γ₀ (vecOf [s₁, s₂]) d = applyStep tbl Γ₀ s₁ (applyStep tbl (ctxAfter Γ₀ s₁) s₂ d) := by
  have hlen : len (vecOf [s₁, s₂]) = 1 + 1 := by rw [len_vecOf]; norm_num
  have hS1 : nthFromEnd (vecOf [s₁, s₂]) 1 = s₁ := by
    rw [nthFromEnd_eq (a := 0) (by rw [hlen, zero_add])]; simp
  have hS0 : nthFromEnd (vecOf [s₁, s₂]) 0 = s₂ := by
    rw [nthFromEnd_eq (a := 1) (by rw [hlen, zero_add])]
    simp
  have hC2 : nthFromEnd (ctxVecAux Γ₀ (vecOf [s₁, s₂]) (1 + 1)) (1 + 1) = Γ₀ := by
    rw [nthFromEnd_eq (a := 0) (by rw [len_ctxVecAux, zero_add]), nth_ctxVecAux_zero]
  have hC1 : nthFromEnd (ctxVecAux Γ₀ (vecOf [s₁, s₂]) (1 + 1)) 1 = ctxAfter Γ₀ s₁ := by
    rw [nthFromEnd_eq (a := 1) (by rw [len_ctxVecAux, add_assoc])]
    have h := nth_ctxVecAux_succ Γ₀ (vecOf [s₁, s₂]) (n := 1 + 1) (i := 0)
      (lt_of_lt_of_le _root_.zero_lt_one le_self_add)
    rw [zero_add] at h
    rw [h, nth_ctxVecAux_zero]
    simp
  have h1 := chainAux_succ tbl (ctxVecAux Γ₀ (vecOf [s₁, s₂]) (1 + 1)) (vecOf [s₁, s₂]) d 0
  rw [zero_add, chainAux_zero] at h1
  unfold chainCode ctxVec
  rw [hlen, chainAux_succ, h1, hC2, hC1, hS1, hS0]

/-- **Smoke test** (Part C): a lemma cut followed by the goal-closing cut is the two cuts, the
second at the context `insert (neg A) Γ₀`. -/
theorem chainCode_lemma_goal (tbl Γ₀ A dA e n s u d : V) :
    chainCode tbl Γ₀ (vecOf [sLemma A dA, sGoal e n s u]) d =
      cutRule Γ₀ A (wkToCode (insert A Γ₀) dA)
        (cutRule (insert (neg LAct A) Γ₀) (goalFact s u) (goalLeafCode (insert (neg LAct A) Γ₀) e n s u) d) := by
  have h7 : sTag (sLemma A dA) = 7 := by simp
  have h6 : sTag (sGoal e n s u) = 6 := by simp
  rw [chainCode_two, applyStep_tag7 h7, ctxAfter_tag7 h7, applyStep_tag6 h6]
  simp

end chainTheorems

end ArithS
