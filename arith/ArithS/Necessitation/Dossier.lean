import ArithS.Necessitation.Cert
import ArithS.Necessitation.Members

/-!
# ArithS.Necessitation.Dossier — the DOSSIER BRIDGE (`DossF … → DossierAt …`)

`M4_BOUNDED_HBL/DESIGN_fragments.md` §3.5/§3.6; the sentence `Layout.lean:53` left open ("the
bridge from the walk's final context to `DossierAt` is NOT in this file").

Two dossier notions describe the same thing:

* `Cert.lean` Part 0: `DossF W Γ n r i` — every fact of the walk's own final context
  `finalCtx 0 (describeF W n r)` sits in `Γ` shifted by `i` (`DossT`/`DossV` for terms and
  vector tails), read node by node by the decomposition lemmas `dossF_and/or/all/exs/rel/nrel/
  verum/falsum`, `dossT_bvar/fvar/func`, `dossV_succ` (children at their WALK offsets
  `descCountF`/`descCountT`).
* `Layout.lean` §4.8: `DossierAt P Γ i r := AllNeg Γ (dossFacts P i r)` — the identification
  template's fact list relocated to `i`, decomposed at `P = factPreds` by `dossierAt_*`,
  `dossierAtT_*`, `dossierAtV_zero/succ` (children at the TEMPLATE offsets `eqCount`/`eqCountT`),
  stated in `Cert`'s fact order and offset spelling on purpose.

`Layout`'s dossier carries only the twelve SHAPE kinds (no `piFact`/`tPiFact`/`tvPiFact`/
`utvPiFact`), so `Cert`'s extra conjuncts are dropped; the offsets agree by `Cert`'s count bridges
`eqCount_eq_descCountF` and `pi1_eqT_eq_descCountT`. The bridge is one structural induction per
syntactic class (`IsSemiterm.induction 𝚷`, the `pi1_succ_induction` on the vector tail, and
`IsSemiformula.pi1_structural_induction`), matching the two decompositions node by node:

* `dossierAtT_of_dossT`, `dossierAtV_of_dossV`, `dossierAt_of_dossF` — a `Cert` dossier at
  offset `i` (over `walkPieces`) IS a `Layout` dossier at `i`;
* `dossierAt_of_walk` — the walk's final context holds `dossFacts factPreds 0 r`, and
  `dossierAt_of_walk_transport` — after any further `NoDrop` list `S`, at offset `shiftsV S`.

The predicate table `factPreds` is a closed `V`-generic term; the induction motives carry it as a
PARAMETER `P` with `hP : P = factPreds` (never inside a definability goal).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSectionVars false

section dossierBridge

variable {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {W : V} (hWp : W = walkPieces)
include htbl hW hWp

/-- The template count of a term is the walk's count (`eqCountT` unfolded into `Cert`'s bridge). -/
lemma eqCountT_eq_descCountT {n t : V} (ht : IsSemiterm LAct n t) : eqCountT t = descCountT W n t := by
  rw [eqCountT]; exact pi1_eqT_eq_descCountT W n t ht

/-- **The term bridge**, with the vector tail bridge inside (it needs the induction hypothesis on
the entries). Stated over a parameter `P = factPreds`. -/
theorem dossierAtT_of_dossT_aux (P : V) (hP : P = factPreds) (n : V) :
    ∀ t, IsSemiterm LAct n t → ∀ Γ i, DossT W Γ n t i → DossierAtT P Γ i t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z _ Γ i h
    subst hP
    rw [dossierAtT_bvar]
    exact (dossT_bvar htbl hW hWp h).1
  · intro x Γ i h
    subst hP
    rw [dossierAtT_fvar]
    exact (dossT_fvar htbl hW hWp h).1
  · intro k f v hkf hv ih
    have key : ∀ m ≤ k, ∀ Γ i, DossV W Γ n k v m i → DossierAtV P Γ i k v m := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _ Γ i _; rw [hP]; exact dossierAtV_zero _ _ _ _ _
      | succ m ihm =>
        intro hm Γ i h
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        obtain ⟨h1, _, h2, h3⟩ := dossV_succ htbl hW hWp hv hm h
        have hc : eqCountT v.[k - (m + 1)] = descCountT W n v.[k - (m + 1)] :=
          eqCountT_eq_descCountT htbl hW hWp (hv.nth hlt)
        subst hP
        rw [dossierAtV_succ hv.isUTerm hm, hc]
        exact ⟨h1, ih _ hlt Γ (i + 1) h2, ihm (le_trans le_self_add hm) Γ _ h3⟩
    intro Γ i h
    obtain ⟨h1, _, _, h4⟩ := dossT_func htbl hW hWp hkf hv h
    have hk := key k le_rfl Γ (i + 1) h4
    subst hP
    rw [dossierAtT_func hkf hv.isUTerm]
    exact ⟨h1, hk⟩

/-- **The term bridge**: a `Cert` term dossier at offset `i` is a `Layout` term dossier at `i`. -/
theorem dossierAtT_of_dossT {Γ n t i : V} (ht : IsSemiterm LAct n t) (h : DossT W Γ n t i) :
    DossierAtT factPreds Γ i t :=
  dossierAtT_of_dossT_aux htbl hW hWp factPreds rfl n t ht Γ i h

/-- **The vector bridge**: the last `j ≤ k` entries. -/
theorem dossierAtV_of_dossV {n k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ j ≤ k, ∀ Γ i, DossV W Γ n k v j i → DossierAtV factPreds Γ i k v j := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _ Γ i _; exact dossierAtV_zero _ _ _ _ _
  | succ j ihj =>
    intro hj Γ i h
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hlt : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    obtain ⟨h1, _, h2, h3⟩ := dossV_succ htbl hW hWp hv hj h
    rw [dossierAtV_succ hv.isUTerm hj, eqCountT_eq_descCountT htbl hW hWp (hv.nth hlt)]
    exact ⟨h1, dossierAtT_of_dossT htbl hW hWp (hv.nth hlt) h2, ihj (le_trans le_self_add hj) Γ _ h3⟩

/-- **The formula bridge**, over a parameter `P = factPreds`. -/
theorem dossierAt_of_dossF_aux (P : V) (hP : P = factPreds) :
    ∀ {n r : V}, IsSemiformula LAct n r → ∀ Γ i, DossF W Γ n r i → DossierAt P Γ i r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ Γ i, DossF W Γ n r i → DossierAt P Γ i r)
  · definability
  · intro n k R v hkR hv Γ i h
    obtain ⟨h1, _, _, h4⟩ := dossF_rel htbl hW hWp hkR hv h
    have hk := dossierAtV_of_dossV htbl hW hWp hv k le_rfl Γ (i + 1) h4
    subst hP
    rw [dossierAt_rel hkR hv.isUTerm]
    exact ⟨h1, hk⟩
  · intro n k R v hkR hv Γ i h
    obtain ⟨h1, _, _, h4⟩ := dossF_nrel htbl hW hWp hkR hv h
    have hk := dossierAtV_of_dossV htbl hW hWp hv k le_rfl Γ (i + 1) h4
    subst hP
    rw [dossierAt_nrel hkR hv.isUTerm]
    exact ⟨h1, hk⟩
  · intro n Γ i h
    subst hP
    rw [dossierAt_verum]
    exact (dossF_verum htbl hW hWp h).1
  · intro n Γ i h
    subst hP
    rw [dossierAt_falsum]
    exact (dossF_falsum htbl hW hWp h).1
  · intro n p q hp hq ihp ihq Γ i h
    obtain ⟨h1, _, hq', hp'⟩ := dossF_and htbl hW hWp hp hq h
    subst hP
    rw [dossierAt_and hp.isUFormula hq.isUFormula, eqCount_eq_descCountF W hq]
    exact ⟨h1, ihq Γ (i + 1) hq', ihp Γ _ hp'⟩
  · intro n p q hp hq ihp ihq Γ i h
    obtain ⟨h1, _, hq', hp'⟩ := dossF_or htbl hW hWp hp hq h
    subst hP
    rw [dossierAt_or hp.isUFormula hq.isUFormula, eqCount_eq_descCountF W hq]
    exact ⟨h1, ihq Γ (i + 1) hq', ihp Γ _ hp'⟩
  · intro n p hp ih Γ i h
    obtain ⟨h1, _, hp'⟩ := dossF_all htbl hW hWp hp h
    subst hP
    rw [dossierAt_all hp.isUFormula]
    exact ⟨h1, ih Γ (i + 1) hp'⟩
  · intro n p hp ih Γ i h
    obtain ⟨h1, _, hp'⟩ := dossF_exs htbl hW hWp hp h
    subst hP
    rw [dossierAt_exs hp.isUFormula]
    exact ⟨h1, ih Γ (i + 1) hp'⟩

/-- **The dossier bridge**: a `Cert` dossier of `r` at offset `i` (over `walkPieces`) is a
`Layout` dossier at `i` — `Layout.lean:53`'s missing bridge. -/
theorem dossierAt_of_dossF {Γ n r i : V} (hr : IsSemiformula LAct n r) (h : DossF W Γ n r i) :
    DossierAt factPreds Γ i r :=
  dossierAt_of_dossF_aux htbl hW hWp factPreds rfl hr Γ i h

/-- **The walk's final context holds the dossier at offset `0`** (from any initial context). -/
theorem dossierAt_of_walk {Γ n r : V} (hr : IsSemiformula LAct n r) :
    DossierAt factPreds (finalCtx Γ (describeF W n r)) 0 r :=
  dossierAt_of_dossF htbl hW hWp hr (dossF_of_walk (describeF_noDrop_shifts htbl hW hWp hr).1)

/-- The walked dossier survives any further non-dropping list `S`, at offset `shiftsV S`. -/
theorem dossierAt_of_walk_transport {Γ n r S : V} (hr : IsSemiformula LAct n r) (hS : NoDrop S) :
    DossierAt factPreds (finalCtx (finalCtx Γ (describeF W n r)) S) (shiftsV S) r := by
  have := dossierAt_of_dossF htbl hW hWp hr
    (dossF_transport hS (dossF_of_walk (Γ := Γ) (describeF_noDrop_shifts htbl hW hWp hr).1))
  rwa [zero_add] at this

/-- A `Cert` dossier transported by a non-dropping list is a `Layout` dossier at the moved offset. -/
theorem dossierAt_of_dossF_transport {Γ n r i S : V} (hr : IsSemiformula LAct n r) (hS : NoDrop S)
    (h : DossF W Γ n r i) : DossierAt factPreds (finalCtx Γ S) (i + shiftsV S) r :=
  dossierAt_of_dossF htbl hW hWp hr (dossF_transport hS h)

/-- The term walk's final context holds the term dossier at offset `0`. -/
theorem dossierAtT_of_walk {Γ n t : V} (ht : IsSemiterm LAct n t) :
    DossierAtT factPreds (finalCtx Γ (describeT W n t)) 0 t := by
  obtain ⟨_, hnd, _, _, _⟩ := describeT_ok htbl hW ht (E := 2 * n + 2 * termLen LAct t + 8) le_rfl
    (Γ := 0) IsFormulaSet.empty
  rw [← hWp] at hnd
  exact dossierAtT_of_dossT htbl hW hWp ht (dossT_of_walk hnd)

end dossierBridge

end ArithS
