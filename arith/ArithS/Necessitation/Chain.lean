import ArithS.Necessitation.Steps

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
  succ := .mkSigma “y ih i w. !(qVecGraph L) y ih”

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
  adjoin := .mkSigma “y x xs ih c. !(impGraph L) y x ih”

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
noncomputable def impChainVDef : 𝚺₁.Semisentence 3 :=
  (ImpChainV.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance impChainV_defined : 𝚺₁-Function₂[V] impChainV L via impChainVDef L := .mk
  fun v ↦ by simp [(ImpChainV.construction L).result_defined_iff, impChainVDef]; rfl
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
  fun v ↦ by simp [(MapSubst.construction L).result_defined_iff, mapSubstDef]; rfl
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
noncomputable def sufChainsDef : 𝚺₁.Semisentence 3 :=
  (SufChains.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance sufChains_defined : 𝚺₁-Function₂[V] sufChains L via sufChainsDef L := .mk
  fun v ↦ by simp [(SufChains.construction L).result_defined_iff, sufChainsDef]; rfl
instance sufChains_definable : 𝚺₁-Function₂[V] sufChains L := sufChains_defined.to_definable

lemma sufChains_vecOf : ∀ (as : List V) (c : V),
    sufChains L (vecOf as) c = vecOf ((List.range (as.length + 1)).map fun i ↦ impChain L (as.drop i) c)
  | [], c => by simp
  | a :: as, c => by
    rw [vecOf_cons, sufChains_adjoin, sufChains_vecOf as c, List.range_succ_eq_map, List.map_cons,
      List.map_map, vecOf_cons, nth_adjoin_zero]
    simp [impChain_cons, Function.comp_def]

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

instance nthFromEnd_definable : 𝚺₁-Function₂ (nthFromEnd : V → V → V) := by
  unfold nthFromEnd; definability

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
      rw [nth_termBShiftVec hv.isUTerm (by rw [hv.lh]; exact hj), nth_qVecIter_single he n j hj]
      by_cases h : j < (n : V)
      · simp [h, lt_of_lt_of_le h le_self_add]
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
      rw [nth_termBShiftVec hv.isUTerm (by rw [hv.lh]; simpa using hj), nth_qVecIter_nil k j hj,
        termBShift_bvar]

/-- The identity substitution: `subst ?[#0, …, #(k-1)] q = q` for a `k`-semiformula. -/
lemma subst_qVecIter_nil {k : ℕ} {q : V} (hq : IsSemiformula L (k : V) q) :
    subst L (qVecIter L k (0 : V)) q = q :=
  subst_eq_self hq (by simpa using isSemitermVec_qVecIter (L := L) (n := k) (IsSemitermVec.nil 0))
    (nth_qVecIter_nil k)

/-- **The composition law**: substituting the outermost variable into a `k`-deep vector
instantiation appends the witness: `qVecIter k W ∘ qVecIter (n + k) (e ∷ 0) = qVecIter k (concat W e)`. -/
lemma termSubstVec_qVecIter_single {W e : V} {n : ℕ} (hW : IsSemitermVec L (n : V) 0 W) (he : IsTerm L e) :
    ∀ k : ℕ, termSubstVec L ((n + k : ℕ) + 1 : ℕ) (qVecIter L k W) (qVecIter L (n + k) (e ∷ (0 : V)))
      = qVecIter L k (concat W e)
  | 0 => by
    have hv : IsSemitermVec L ((n : V) + 1) (n : V) (qVecIter L n (e ∷ (0 : V))) :=
      isSemitermVec_qVecIter_single he
    simp only [Nat.add_zero, qVecIter_zero]
    apply nth_ext' ((n : V) + 1)
    · rw [len_termSubstVec (by simpa [Nat.cast_succ] using hv.isUTerm)]; push_cast; rfl
    · rw [len_concat, hW.lh]
    intro i hi
    rw [nth_termSubstVec (by simpa [Nat.cast_succ] using hv.isUTerm) (by push_cast; exact hi),
      nth_qVecIter_single he n i hi]
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
    have hw : IsSemitermVec L ((n : V) + (k : V)) (0 + (k : V)) (qVecIter L k W) := isSemitermVec_qVecIter hW
    rw [show n + (k + 1) = (n + k) + 1 by ring, qVecIter_succ, qVecIter_qVec, qVecIter_succ, qVecIter_qVec,
      qVecIter_succ, qVecIter_qVec]
    have := termSubstVec_qVec_qVec (L := L) hv (by simpa [Nat.cast_add] using hw)
    rw [show (((n + k + 1 : ℕ) + 1 : ℕ) : V) = (((n + k : ℕ) : V) + 1) + 1 by push_cast; ring, this,
      termSubstVec_qVecIter_single hW he k]

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
    exact (subst_qVecIter_nil hq).symm
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
    simp only [ExsBuild.construction, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, List.length_nil]
    rw [instOuterAt_eq_subst 0 pre (by simpa using hq) hes, qVecIter_zero,
      nthFromEnd_eq (a := (pre.length : V)) (by rw [len_ctxChain_natCast]; simp),
      nth_ctxChain_natCast _ _ pre.length pre.length le_rfl]
  | e :: rest, pre, hpre => by
    have hes' : ∀ e' ∈ pre, IsTerm L e' := fun e' h ↦ hes e' (by simp [hpre, h])
    have hlen : es.length = pre.length + (rest.length + 1) := by simp [hpre]
    have hq' : IsSemiformula L ((pre.length + (rest.length + 1) : ℕ) : V) q := by rwa [← hlen]
    have ih := exsBuild_vecOf es hq hes Γ d rest (pre ++ [e]) (by simp [hpre])
    rw [vecOf_cons, VecRec.Construction.result_adjoin, ih, exsChainCode_cons, List.length_append,
      List.length_singleton, instOuterAt_append]
    simp only [ExsBuild.construction, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, len_vecOf, levelBody]
    -- the partial instance at depth `pre.length`
    have hz : subst L (qVecIterV L (tailIter (vecOf es.reverse) ((rest.length : V) + 1)) ((rest.length : V) + 1)) q
        = instOuterAt L (rest.length + 1) pre q := by
      rw [instOuterAt_eq_subst (rest.length + 1) pre hq' hes', ← Nat.cast_succ, tailIter_vecOf,
        qVecIterV_natCast, hpre, show (e :: rest).length = rest.length + 1 from rfl, drop_reverse_append]
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
    rw [hz, hC, ctxL_succ, hF, qqExss_natCast, ← exsIter_succ, ← qqExss_natCast, ← Nat.cast_succ, qqExss_natCast]

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
    simp only [HornBuild.construction, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    rw [nthFromEnd_eq (a := (pre.length : V)) (by rw [len_ctxChain_natCast]; simp),
      nth_ctxChain_natCast _ _ pre.length pre.length le_rfl]
  | a :: rest, pre, hpre => by
    have hlen : as.length = pre.length + (rest.length + 1) := by simp [hpre]
    have ih := hornBuild_vecOf as c S d rest (pre ++ [a]) (by simp [hpre])
    rw [vecOf_cons, VecRec.Construction.result_adjoin, ih, hornClose_cons, List.length_append,
      List.length_singleton]
    simp only [HornBuild.construction, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      len_vecOf, impChainV_vecOf]
    have hN : (mapNeg L (sufChains L (vecOf as) c)).[(pre.length : V)] = neg L (impChain L (a :: rest) c) := by
      rw [mapNeg_vecOf, sufChains_vecOf, List.map_map, nth_vecOf _ pre.length (by simp; omega)]
      simp [hpre, List.drop_left']
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
  have := hornBuild_vecOf as c S d as [] rfl
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
  congr 3
  exact List.map_congr_left fun a ha ↦ subst_revV_vecOf es (has a ha) hes

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

end ArithS
