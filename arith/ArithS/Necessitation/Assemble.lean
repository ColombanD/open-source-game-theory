import ArithS.Necessitation.Top
import ArithS.Necessitation.Verify2
import ArithS.Necessitation.Pin
import ArithS.Necessitation.NodeSize

/-!
# ArithS.Necessitation.Assemble — the kit over `VerifyGraph'`, the root bridge, and the assembly

`Top.lean`'s kits quantify over the OLD relation `VerifyGraph W tblN` (`Verify.lean`), which `Verify2.lean`
superseded by `VerifyGraph' Ww Wl Wc W₁ W₂ W T A` (computed prologues, the `axm` certificate table `A`).
This file restates the verify kit over the new relation (`VerifyKit'''`), bridges the top's ROOT layout to
the node layout `verifyGraph'_ok` expects, discharges the kit from `verifyGraph'_ok_pow`, and assembles
`BoundedInnerNec 24` conditional on the named oracles.

**Why the kit cannot live in `Top.lean`:** `Verify2.lean` imports `Top.lean` (for `RootLayout`, `kitQ`, …),
so a kit mentioning `VerifyGraph'` has to sit ABOVE `Verify2` — here.

**The root bridge (§2).** `verifyGraph'_ok` wants the root laid out CANONICALLY at offset `0`
(`NodeLay … (fstIdx ρ)`: the member dossier at `&(3 + mLen x)`, the chain `&2 = insert &(3 + mLen x) 𝟎`, the
fold base `&1`, the length `&0`, plus the numeric `lenFact`/`leFact`), while the top's `RootLayout Γ x i`
has the consecutive triple `&i = setLen &(i+1)`, `&(i+1) = insert &(i+2) 𝟎`, `&(i+2) = x` and no numeric
length. The two shapes are incompatible at any common offset (the fold base sits between the length and
the chain), so the bridge RE-LAYS the root sequent `{x}` from scratch (`layoutSteps`, a fresh copy of the
member `x'` and of the sequent `s'`), and then IDENTIFIES the two copies: `eqSteps` (the identification walk
of the two dossiers of `x`) gives `x₀ = x'`, two `congMem`/`emptySubsetC`/`insertSubset` triples give
`s₀ ⊆ s'` and `s' ⊆ s₀`, `subsetAntisymm` gives `s₀ = s'`. After the verify list `L` (whose goal fact is
about the FRESH sequent `s'`), a RETARGET block moves the goal onto the ROOT sequent `s₀`: `goalElim`
(recover `d = &1`, `n = &0` and `fstIdxFact s' d`), `congFstIdx` (`fstIdxFact s₀ d`), `sGoal`
(re-close `goalFact s₀ (bnum (dlen ρ))`). So the kit's list is `vList = bridge ++ L ++ retarget`, and its
`ok` conjunct has EXACTLY `VerifyKit''.ok`'s shape — the goal at `&(i + 1 + shiftsV vList)` on the root
sequent — which is why `top_main'''` is `top_main''` with the list renamed. **Index reconciliation chosen:**
the goal is RETARGETED onto the root sequent (no index identity for the singleton is needed: the
identification makes the two sequent objects provably equal in the object proof).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 1. The singleton sequent `{x}`: its member list and its canonical layout, read off -/

section singleton

lemma len_memberList_single (x : V) : len (memberList (insert x (0 : V))) = 1 := by
  have h1 : 1 ≤ len (memberList (insert x (0 : V))) := one_le_len_memberList_insert x 0
  refine le_antisymm ?_ h1
  by_contra hlt
  have hlt' : 1 < len (memberList (insert x (0 : V))) := not_le.mp hlt
  have h0 : (memberList (insert x (0 : V))).[0] ∈ insert x (0 : V) :=
    nth_memberList_mem (lt_of_lt_of_le _root_.zero_lt_one h1)
  have h1' : (memberList (insert x (0 : V))).[1] ∈ insert x (0 : V) := nth_memberList_mem hlt'
  have e0 : (memberList (insert x (0 : V))).[0] = x := by
    rcases mem_bitInsert_iff.mp h0 with h | h
    · exact h
    · simp at h
  have e1 : (memberList (insert x (0 : V))).[1] = x := by
    rcases mem_bitInsert_iff.mp h1' with h | h
    · exact h
    · simp at h
  have := memberList_nodup (lt_of_lt_of_le _root_.zero_lt_one h1) hlt' (e0.trans e1.symm)
  exact _root_.zero_ne_one this

lemma memberList_single (x : V) : memberList (insert x (0 : V)) = x ∷ 0 := by
  refine nth_ext' 1 (len_memberList_single x) (by simp) ?_
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · have h0 : (memberList (insert x (0 : V))).[0] ∈ insert x (0 : V) :=
      nth_memberList_mem (by rw [len_memberList_single]; exact _root_.zero_lt_one)
    rw [nth_adjoin_zero]
    rcases mem_bitInsert_iff.mp h0 with h | h
    · exact h
    · simp at h
  · exact absurd hi (not_lt.mpr le_add_self)

/-- The index of the (fresh) member `x` in the canonical layout of `{x}` at chain offset `i`:
`mTop i 1 (mLen Wc T x + 0) = i + (2·1 + 1 + (mLen Wc T x + 0))`. -/
noncomputable def sTop (Wc T x i : V) : V := mTop i 1 (mLen Wc T x + 0)

lemma sTop_eq (Wc T x i : V) : sTop Wc T x i = i + 3 + mLen Wc T x := by
  unfold sTop mTop; ring

/-- **The canonical layout of `{x}`, read off**: the member's dossier, `piFact`, the chain fact
`&(i+2) = insert &(sTop) 𝟎` (the innermost member's `prevI` IS the literal `𝟎`), and the membership fact. -/
lemma layout_single {Ww Wc T Γ x i : V} (h : Layout Ww Wc T Γ (insert x (0 : V)) i) :
    DossF Ww Γ 0 x (sTop Wc T x i) ∧
    neg LAct (piFact (𝟎 : V) (^&(sTop Wc T x i))) ∈ Γ ∧
    neg LAct (insFact (^&(i + 2)) (^&(sTop Wc T x i)) (𝟎 : V)) ∈ Γ ∧
    neg LAct (memFact (^&(sTop Wc T x i)) (^&(i + 2))) ∈ Γ := by
  have hk : (0 : V) < len (memberList (insert x (0 : V))) := by
    rw [len_memberList_single]; exact _root_.zero_lt_one
  obtain ⟨hD, hpi, _, hins, _, hm⟩ := h.1 0 hk
  simp only [memberList_single, len_adjoin, len_nil, zero_add, offVec_adjoin, tailShift_nil, nth_adjoin_zero] at hD hpi hins hm
  have e2 : i + (1 + 1 + 0) = i + 2 := by ring
  have e2' : i + (1 + 1) = i + 2 := by ring
  have hprev : prevI i 1 0 = (𝟎 : V) := by
    unfold prevI; exact prevAt_of_eq (by ring)
  rw [e2, hprev] at hins
  rw [e2'] at hm
  exact ⟨hD, hpi, hins, hm⟩

end singleton

end ArithS
