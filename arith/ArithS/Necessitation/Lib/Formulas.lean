import ArithS.Necessitation.Lib.Basic

/-!
# ArithS.Necessitation.Lib.Formulas — the `formulas` rows of the library `Λ`

`DESIGN_inner_necessitation.md` §3.1, rows `formulas` and the formula-shaped `totality`
entries, over `LAct` codes. Same convention as `Sets.lean` (body `xB : ArithmeticSemisentence m`
in index order, `x := ∀¹* xB`, `models_x`, `pa_proves_x`, `lib_x`).

1. **Totality** of every constructor graph (`qqRel … qqExs`, `qqFunc/qqBvar/qqFvar`, `adjoin`)
   and of `neg`, `subst`, `substs1`, `qVec`, `termSubstVec`, `termShiftVec`.
2. **Formation**: `IsSemiformula n` for every constructor (atoms under `L.IsRel` +
   `IsSemitermVec`), for `neg`, `shift`, `subst`, `substs1`, `free`; `IsSemiterm` for the term
   constructors; `IsSemitermVec` for `nil`/`adjoin`.
3. **Commutation** of `neg`, `subst`, `shift`, `free` with every constructor (`neg (p ⋏ q) =
   neg p ⋎ neg q`, `subst w (∀ p) = ∀ (subst (qVec w) p)`, `shift (rel k R v) = rel k R
   (termShiftVec k v)`, `free (∀ p) = ∀ (subst (qVec ?[&0]) (shift p))`, …).
4. **Shape inversion**: `IsSemiformula n r → shift r = p ⋏ q → ∃ p' q', r = p' ⋏ q' ∧
   p = shift p' ∧ q = shift q'` and the analogues for the other seven constructors and for
   `subst` (by `IsSemiformula.case_iff` + constructor discrimination).

Hypotheses are `IsSemiformula n` facts at an arbitrary `n` (the fragments hold semiformula
facts, `IsUFormula` follows); the term-vector hypotheses of the atoms are `IsUTermVec` for the
commutations (what `neg_rel`/`substs_rel`/`shift_rel` ask) and `IsSemitermVec` for formation.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### V-level helpers: `free` on the constructors, shape inversion -/

section helpers

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma free_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    free L (^rel k R v) = ^rel k R (termSubstVec L k ?[^&0] (termShiftVec L k v)) := by
  simp [free, substs1, hR, hv, substs_rel hR (IsUTermVec.termShiftVec hv)]

lemma free_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    free L (^nrel k R v) = ^nrel k R (termSubstVec L k ?[^&0] (termShiftVec L k v)) := by
  simp [free, substs1, hR, hv, substs_nrel hR (IsUTermVec.termShiftVec hv)]

lemma free_verum : free L (^⊤ : V) = ^⊤ := by simp [free, substs1]

lemma free_falsum : free L (^⊥ : V) = ^⊥ := by simp [free, substs1]

lemma free_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    free L (p ^⋏ q) = free L p ^⋏ free L q := by
  simp [free, substs1, hp, hq, hp.shift, hq.shift]

lemma free_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    free L (p ^⋎ q) = free L p ^⋎ free L q := by
  simp [free, substs1, hp, hq, hp.shift, hq.shift]

lemma free_all {p : V} (hp : IsUFormula L p) :
    free L (^∀ p) = ^∀ (subst L (qVec L ?[^&0]) (shift L p)) := by
  simp [free, substs1, hp, hp.shift]

lemma free_exs {p : V} (hp : IsUFormula L p) :
    free L (^∃ p) = ^∃ (subst L (qVec L ?[^&0]) (shift L p)) := by
  simp [free, substs1, hp, hp.shift]

/-- The eight-way case split on a semiformula, with `shift` pushed through. -/
private lemma shift_cases {n r : V} (hr : IsSemiformula L n r) :
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ r = ^rel k R v ∧
      shift L r = ^rel k R (termShiftVec L k v)) ∨
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ r = ^nrel k R v ∧
      shift L r = ^nrel k R (termShiftVec L k v)) ∨
    (r = ^⊤ ∧ shift L r = ^⊤) ∨ (r = ^⊥ ∧ shift L r = ^⊥) ∨
    (∃ p q, IsSemiformula L n p ∧ IsSemiformula L n q ∧ r = p ^⋏ q ∧
      shift L r = shift L p ^⋏ shift L q) ∨
    (∃ p q, IsSemiformula L n p ∧ IsSemiformula L n q ∧ r = p ^⋎ q ∧
      shift L r = shift L p ^⋎ shift L q) ∨
    (∃ p, IsSemiformula L (n + 1) p ∧ r = ^∀ p ∧ shift L r = ^∀ (shift L p)) ∨
    (∃ p, IsSemiformula L (n + 1) p ∧ r = ^∃ p ∧ shift L r = ^∃ (shift L p)) := by
  rcases IsSemiformula.case_iff.mp hr with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ |
    rfl | rfl | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨k, R, v, hR, hv, rfl, shift_rel hR hv.isUTerm⟩
  · exact Or.inr <| Or.inl ⟨k, R, v, hR, hv, rfl, shift_nrel hR hv.isUTerm⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, shift_verum⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, shift_falsum⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨p, q, hp, hq, rfl, shift_and hp.isUFormula hq.isUFormula⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨p, q, hp, hq, rfl, shift_or hp.isUFormula hq.isUFormula⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨p, hp, rfl, shift_all hp.isUFormula⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨p, hp, rfl, shift_exs hp.isUFormula⟩

/-- The eight-way case split on a semiformula, with `subst w` pushed through. -/
private lemma substs_cases {n r : V} (w : V) (hr : IsSemiformula L n r) :
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ r = ^rel k R v ∧
      subst L w r = ^rel k R (termSubstVec L k w v)) ∨
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ r = ^nrel k R v ∧
      subst L w r = ^nrel k R (termSubstVec L k w v)) ∨
    (r = ^⊤ ∧ subst L w r = ^⊤) ∨ (r = ^⊥ ∧ subst L w r = ^⊥) ∨
    (∃ p q, IsSemiformula L n p ∧ IsSemiformula L n q ∧ r = p ^⋏ q ∧
      subst L w r = subst L w p ^⋏ subst L w q) ∨
    (∃ p q, IsSemiformula L n p ∧ IsSemiformula L n q ∧ r = p ^⋎ q ∧
      subst L w r = subst L w p ^⋎ subst L w q) ∨
    (∃ p, IsSemiformula L (n + 1) p ∧ r = ^∀ p ∧ subst L w r = ^∀ (subst L (qVec L w) p)) ∨
    (∃ p, IsSemiformula L (n + 1) p ∧ r = ^∃ p ∧ subst L w r = ^∃ (subst L (qVec L w) p)) := by
  rcases IsSemiformula.case_iff.mp hr with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ |
    rfl | rfl | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨k, R, v, hR, hv, rfl, substs_rel hR hv.isUTerm⟩
  · exact Or.inr <| Or.inl ⟨k, R, v, hR, hv, rfl, substs_nrel hR hv.isUTerm⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, substs_verum w⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, substs_falsum w⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨p, q, hp, hq, rfl, substs_and hp.isUFormula hq.isUFormula⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨p, q, hp, hq, rfl, substs_or hp.isUFormula hq.isUFormula⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨p, hp, rfl, substs_all hp.isUFormula⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨p, hp, rfl, substs_ex hp.isUFormula⟩

/-- Discriminate the eight constructor shapes: `simp` on the pair codes. -/
macro "qq_discr" h:ident : tactic =>
  `(tactic| first
    | (simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at $h:ident)
    | skip)

lemma shift_eq_rel_inv {n r k R v : V} (hr : IsSemiformula L n r) (h : shift L r = ^rel k R v) :
    ∃ v', r = ^rel k R v' ∧ v = termShiftVec L k v' := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h
  · obtain ⟨rfl, rfl, rfl⟩ := (qqRel_inj _ _ _ _ _ _).mp h; exact ⟨v', rfl, rfl⟩
  all_goals qq_discr h

lemma shift_eq_nrel_inv {n r k R v : V} (hr : IsSemiformula L n r) (h : shift L r = ^nrel k R v) :
    ∃ v', r = ^nrel k R v' ∧ v = termShiftVec L k v' := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · obtain ⟨rfl, rfl, rfl⟩ := (qqNRel_inj _ _ _ _ _ _).mp h; exact ⟨v', rfl, rfl⟩
  all_goals qq_discr h

lemma shift_eq_verum_inv {n r : V} (hr : IsSemiformula L n r) (h : shift L r = ^⊤) : r = ^⊤ := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h <;> qq_discr h

lemma shift_eq_falsum_inv {n r : V} (hr : IsSemiformula L n r) (h : shift L r = ^⊥) : r = ^⊥ := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h <;> qq_discr h

lemma shift_eq_and_inv {n r p q : V} (hr : IsSemiformula L n r) (h : shift L r = p ^⋏ q) :
    ∃ p' q', r = p' ^⋏ q' ∧ p = shift L p' ∧ q = shift L q' := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp h; exact ⟨p', q', rfl, rfl, rfl⟩
  all_goals qq_discr h

lemma shift_eq_or_inv {n r p q : V} (hr : IsSemiformula L n r) (h : shift L r = p ^⋎ q) :
    ∃ p' q', r = p' ^⋎ q' ∧ p = shift L p' ∧ q = shift L q' := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp h; exact ⟨p', q', rfl, rfl, rfl⟩
  all_goals qq_discr h

lemma shift_eq_all_inv {n r p : V} (hr : IsSemiformula L n r) (h : shift L r = ^∀ p) :
    ∃ p', r = ^∀ p' ∧ p = shift L p' := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain rfl := (qqAll_inj _ _).mp h; exact ⟨p', rfl, rfl⟩
  · qq_discr h

lemma shift_eq_exs_inv {n r p : V} (hr : IsSemiformula L n r) (h : shift L r = ^∃ p) :
    ∃ p', r = ^∃ p' ∧ p = shift L p' := by
  rcases shift_cases hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain rfl := (qqExs_inj _ _).mp h; exact ⟨p', rfl, rfl⟩

lemma substs_eq_rel_inv {n r w k R v : V} (hr : IsSemiformula L n r)
    (h : subst L w r = ^rel k R v) : ∃ v', r = ^rel k R v' ∧ v = termSubstVec L k w v' := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h
  · obtain ⟨rfl, rfl, rfl⟩ := (qqRel_inj _ _ _ _ _ _).mp h; exact ⟨v', rfl, rfl⟩
  all_goals qq_discr h

lemma substs_eq_nrel_inv {n r w k R v : V} (hr : IsSemiformula L n r)
    (h : subst L w r = ^nrel k R v) : ∃ v', r = ^nrel k R v' ∧ v = termSubstVec L k w v' := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · obtain ⟨rfl, rfl, rfl⟩ := (qqNRel_inj _ _ _ _ _ _).mp h; exact ⟨v', rfl, rfl⟩
  all_goals qq_discr h

lemma substs_eq_verum_inv {n r w : V} (hr : IsSemiformula L n r) (h : subst L w r = ^⊤) :
    r = ^⊤ := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h <;> qq_discr h

lemma substs_eq_falsum_inv {n r w : V} (hr : IsSemiformula L n r) (h : subst L w r = ^⊥) :
    r = ^⊥ := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, q, _, _, rfl, e⟩ | ⟨p, _, rfl, e⟩ |
    ⟨p, _, rfl, e⟩ <;> rw [e] at h <;> qq_discr h

lemma substs_eq_and_inv {n r w p q : V} (hr : IsSemiformula L n r) (h : subst L w r = p ^⋏ q) :
    ∃ p' q', r = p' ^⋏ q' ∧ p = subst L w p' ∧ q = subst L w q' := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain ⟨rfl, rfl⟩ := (qqAnd_inj _ _ _ _).mp h; exact ⟨p', q', rfl, rfl, rfl⟩
  all_goals qq_discr h

lemma substs_eq_or_inv {n r w p q : V} (hr : IsSemiformula L n r) (h : subst L w r = p ^⋎ q) :
    ∃ p' q', r = p' ^⋎ q' ∧ p = subst L w p' ∧ q = subst L w q' := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain ⟨rfl, rfl⟩ := (qqOr_inj _ _ _ _).mp h; exact ⟨p', q', rfl, rfl, rfl⟩
  all_goals qq_discr h

lemma substs_eq_all_inv {n r w p : V} (hr : IsSemiformula L n r) (h : subst L w r = ^∀ p) :
    ∃ p', r = ^∀ p' ∧ p = subst L (qVec L w) p' := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain rfl := (qqAll_inj _ _).mp h; exact ⟨p', rfl, rfl⟩
  · qq_discr h

lemma substs_eq_exs_inv {n r w p : V} (hr : IsSemiformula L n r) (h : subst L w r = ^∃ p) :
    ∃ p', r = ^∃ p' ∧ p = subst L (qVec L w) p' := by
  rcases substs_cases w hr with ⟨k', R', v', _, _, rfl, e⟩ | ⟨k', R', v', _, _, rfl, e⟩ |
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', q', _, _, rfl, e⟩ | ⟨p', _, rfl, e⟩ |
    ⟨p', _, rfl, e⟩ <;> rw [e] at h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · qq_discr h
  · obtain rfl := (qqExs_inj _ _).mp h; exact ⟨p', rfl, rfl⟩

end helpers


/-! ### Totality -/

/-- `∀ k R v, ∃ p, p = rel k R v`. -/
noncomputable def qqRelTotalB : ArithmeticSemisentence 3 :=
  “v R k. ∃ p, !qqRelDef p k R v”
noncomputable def qqRelTotal : ArithmeticSentence := ∀¹* qqRelTotalB

lemma models_qqRelTotal :
    V↓[ℒₒᵣ] ⊧ qqRelTotal ↔ ∀ v R k : V, ∃ p, p = ^rel k R v := by
  simp [qqRelTotal, qqRelTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqRelTotal : 𝗣𝗔 ⊢ qqRelTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqRelTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_qqRelTotal : Lib qqRelTotal := Lib.of_pa pa_proves_qqRelTotal

/-- `∀ k R v, ∃ p, p = nrel k R v`. -/
noncomputable def qqNRelTotalB : ArithmeticSemisentence 3 :=
  “v R k. ∃ p, !qqNRelDef p k R v”
noncomputable def qqNRelTotal : ArithmeticSentence := ∀¹* qqNRelTotalB

lemma models_qqNRelTotal :
    V↓[ℒₒᵣ] ⊧ qqNRelTotal ↔ ∀ v R k : V, ∃ p, p = ^nrel k R v := by
  simp [qqNRelTotal, qqNRelTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqNRelTotal : 𝗣𝗔 ⊢ qqNRelTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqNRelTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_qqNRelTotal : Lib qqNRelTotal := Lib.of_pa pa_proves_qqNRelTotal

/-- `∃ p, p = ⊤`. -/
noncomputable def qqVerumTotalB : ArithmeticSemisentence 0 :=
  “∃ p, !qqVerumDef p”
noncomputable def qqVerumTotal : ArithmeticSentence := ∀¹* qqVerumTotalB

lemma models_qqVerumTotal :
    V↓[ℒₒᵣ] ⊧ qqVerumTotal ↔ ∃ p : V, p = ^⊤ := by
  simp [qqVerumTotal, qqVerumTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqVerumTotal : 𝗣𝗔 ⊢ qqVerumTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqVerumTotal.mpr ⟨_, rfl⟩

theorem lib_qqVerumTotal : Lib qqVerumTotal := Lib.of_pa pa_proves_qqVerumTotal

/-- `∃ p, p = ⊥`. -/
noncomputable def qqFalsumTotalB : ArithmeticSemisentence 0 :=
  “∃ p, !qqFalsumDef p”
noncomputable def qqFalsumTotal : ArithmeticSentence := ∀¹* qqFalsumTotalB

lemma models_qqFalsumTotal :
    V↓[ℒₒᵣ] ⊧ qqFalsumTotal ↔ ∃ p : V, p = ^⊥ := by
  simp [qqFalsumTotal, qqFalsumTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqFalsumTotal : 𝗣𝗔 ⊢ qqFalsumTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqFalsumTotal.mpr ⟨_, rfl⟩

theorem lib_qqFalsumTotal : Lib qqFalsumTotal := Lib.of_pa pa_proves_qqFalsumTotal

/-- `∀ p q, ∃ r, r = p ⋏ q`. -/
noncomputable def qqAndTotalB : ArithmeticSemisentence 2 :=
  “q p. ∃ r, !qqAndDef r p q”
noncomputable def qqAndTotal : ArithmeticSentence := ∀¹* qqAndTotalB

lemma models_qqAndTotal :
    V↓[ℒₒᵣ] ⊧ qqAndTotal ↔ ∀ q p : V, ∃ r, r = p ^⋏ q := by
  simp [qqAndTotal, qqAndTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqAndTotal : 𝗣𝗔 ⊢ qqAndTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAndTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_qqAndTotal : Lib qqAndTotal := Lib.of_pa pa_proves_qqAndTotal

/-- `∀ p q, ∃ r, r = p ⋎ q`. -/
noncomputable def qqOrTotalB : ArithmeticSemisentence 2 :=
  “q p. ∃ r, !qqOrDef r p q”
noncomputable def qqOrTotal : ArithmeticSentence := ∀¹* qqOrTotalB

lemma models_qqOrTotal :
    V↓[ℒₒᵣ] ⊧ qqOrTotal ↔ ∀ q p : V, ∃ r, r = p ^⋎ q := by
  simp [qqOrTotal, qqOrTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqOrTotal : 𝗣𝗔 ⊢ qqOrTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqOrTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_qqOrTotal : Lib qqOrTotal := Lib.of_pa pa_proves_qqOrTotal

/-- `∀ p, ∃ q, q = ∀ p`. -/
noncomputable def qqAllTotalB : ArithmeticSemisentence 1 :=
  “p. ∃ q, !qqAllDef q p”
noncomputable def qqAllTotal : ArithmeticSentence := ∀¹* qqAllTotalB

lemma models_qqAllTotal :
    V↓[ℒₒᵣ] ⊧ qqAllTotal ↔ ∀ p : V, ∃ q, q = ^∀ p := by
  simp [qqAllTotal, qqAllTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqAllTotal : 𝗣𝗔 ⊢ qqAllTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAllTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqAllTotal : Lib qqAllTotal := Lib.of_pa pa_proves_qqAllTotal

/-- `∀ p, ∃ q, q = ∃ p`. -/
noncomputable def qqExsTotalB : ArithmeticSemisentence 1 :=
  “p. ∃ q, !qqExsDef q p”
noncomputable def qqExsTotal : ArithmeticSentence := ∀¹* qqExsTotalB

lemma models_qqExsTotal :
    V↓[ℒₒᵣ] ⊧ qqExsTotal ↔ ∀ p : V, ∃ q, q = ^∃ p := by
  simp [qqExsTotal, qqExsTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqExsTotal : 𝗣𝗔 ⊢ qqExsTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqExsTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqExsTotal : Lib qqExsTotal := Lib.of_pa pa_proves_qqExsTotal

/-- `∀ k f v, ∃ t, t = func k f v`. -/
noncomputable def qqFuncTotalB : ArithmeticSemisentence 3 :=
  “v f k. ∃ t, !qqFuncDef t k f v”
noncomputable def qqFuncTotal : ArithmeticSentence := ∀¹* qqFuncTotalB

lemma models_qqFuncTotal :
    V↓[ℒₒᵣ] ⊧ qqFuncTotal ↔ ∀ v f k : V, ∃ t, t = qqFunc k f v := by
  simp [qqFuncTotal, qqFuncTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqFuncTotal : 𝗣𝗔 ⊢ qqFuncTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqFuncTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_qqFuncTotal : Lib qqFuncTotal := Lib.of_pa pa_proves_qqFuncTotal

/-- `∀ z, ∃ t, t = #z`. -/
noncomputable def qqBvarTotalB : ArithmeticSemisentence 1 :=
  “z. ∃ t, !qqBvarDef t z”
noncomputable def qqBvarTotal : ArithmeticSentence := ∀¹* qqBvarTotalB

lemma models_qqBvarTotal :
    V↓[ℒₒᵣ] ⊧ qqBvarTotal ↔ ∀ z : V, ∃ t, t = qqBvar z := by
  simp [qqBvarTotal, qqBvarTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqBvarTotal : 𝗣𝗔 ⊢ qqBvarTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqBvarTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqBvarTotal : Lib qqBvarTotal := Lib.of_pa pa_proves_qqBvarTotal

/-- `∀ x, ∃ t, t = &x`. -/
noncomputable def qqFvarTotalB : ArithmeticSemisentence 1 :=
  “x. ∃ t, !qqFvarDef t x”
noncomputable def qqFvarTotal : ArithmeticSentence := ∀¹* qqFvarTotalB

lemma models_qqFvarTotal :
    V↓[ℒₒᵣ] ⊧ qqFvarTotal ↔ ∀ x : V, ∃ t, t = qqFvar x := by
  simp [qqFvarTotal, qqFvarTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_qqFvarTotal : 𝗣𝗔 ⊢ qqFvarTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqFvarTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqFvarTotal : Lib qqFvarTotal := Lib.of_pa pa_proves_qqFvarTotal

/-- `∀ t v, ∃ w, w = t ∷ v`. -/
noncomputable def adjoinTotalB : ArithmeticSemisentence 2 :=
  “v t. ∃ w, !adjoinDef w t v”
noncomputable def adjoinTotal : ArithmeticSentence := ∀¹* adjoinTotalB

lemma models_adjoinTotal :
    V↓[ℒₒᵣ] ⊧ adjoinTotal ↔ ∀ v t : V, ∃ w, w = t ∷ v := by
  simp [adjoinTotal, adjoinTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_adjoinTotal : 𝗣𝗔 ⊢ adjoinTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_adjoinTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_adjoinTotal : Lib adjoinTotal := Lib.of_pa pa_proves_adjoinTotal

/-- `∀ p, ∃ y, y = neg p`. -/
noncomputable def negTotalB : ArithmeticSemisentence 1 :=
  “p. ∃ y, !(negGraph LAct) y p”
noncomputable def negTotal : ArithmeticSentence := ∀¹* negTotalB

lemma models_negTotal :
    V↓[ℒₒᵣ] ⊧ negTotal ↔ ∀ p : V, ∃ y, y = neg LAct p := by
  simp [negTotal, negTotalB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negTotal : 𝗣𝗔 ⊢ negTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_negTotal : Lib negTotal := Lib.of_pa pa_proves_negTotal

/-- `∀ w p, ∃ y, y = subst w p`. -/
noncomputable def substsTotalB : ArithmeticSemisentence 2 :=
  “p w. ∃ y, !(substsGraph LAct) y w p”
noncomputable def substsTotal : ArithmeticSentence := ∀¹* substsTotalB

lemma models_substsTotal :
    V↓[ℒₒᵣ] ⊧ substsTotal ↔ ∀ p w : V, ∃ y, y = subst LAct w p := by
  simp [substsTotal, substsTotalB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsTotal : 𝗣𝗔 ⊢ substsTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_substsTotal : Lib substsTotal := Lib.of_pa pa_proves_substsTotal

/-- `∀ t p, ∃ y, y = substs1 t p`. -/
noncomputable def substs1TotalB : ArithmeticSemisentence 2 :=
  “p t. ∃ y, !(substs1Graph LAct) y t p”
noncomputable def substs1Total : ArithmeticSentence := ∀¹* substs1TotalB

lemma models_substs1Total :
    V↓[ℒₒᵣ] ⊧ substs1Total ↔ ∀ p t : V, ∃ y, y = substs1 LAct t p := by
  simp [substs1Total, substs1TotalB, models_iff, Matrix.vecForall_iff, substs1.defined.iff]

theorem pa_proves_substs1Total : 𝗣𝗔 ⊢ substs1Total :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substs1Total.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_substs1Total : Lib substs1Total := Lib.of_pa pa_proves_substs1Total

/-- `∀ w, ∃ u, u = qVec w`. -/
noncomputable def qVecTotalB : ArithmeticSemisentence 1 :=
  “w. ∃ u, !(qVecGraph LAct) u w”
noncomputable def qVecTotal : ArithmeticSentence := ∀¹* qVecTotalB

lemma models_qVecTotal :
    V↓[ℒₒᵣ] ⊧ qVecTotal ↔ ∀ w : V, ∃ u, u = qVec LAct w := by
  simp [qVecTotal, qVecTotalB, models_iff, Matrix.vecForall_iff, qVec.defined.iff]

theorem pa_proves_qVecTotal : 𝗣𝗔 ⊢ qVecTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qVecTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qVecTotal : Lib qVecTotal := Lib.of_pa pa_proves_qVecTotal

/-- `∀ k w v, ∃ u, u = termSubstVec k w v`. -/
noncomputable def termSubstVecTotalB : ArithmeticSemisentence 3 :=
  “v w k. ∃ u, !(termSubstVecGraph LAct) u k w v”
noncomputable def termSubstVecTotal : ArithmeticSentence := ∀¹* termSubstVecTotalB

lemma models_termSubstVecTotal :
    V↓[ℒₒᵣ] ⊧ termSubstVecTotal ↔ ∀ v w k : V, ∃ u, u = termSubstVec LAct k w v := by
  simp [termSubstVecTotal, termSubstVecTotalB, models_iff, Matrix.vecForall_iff, termSubstVec.defined.iff]

theorem pa_proves_termSubstVecTotal : 𝗣𝗔 ⊢ termSubstVecTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termSubstVecTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_termSubstVecTotal : Lib termSubstVecTotal := Lib.of_pa pa_proves_termSubstVecTotal

/-- `∀ k v, ∃ u, u = termShiftVec k v`. -/
noncomputable def termShiftVecTotalB : ArithmeticSemisentence 2 :=
  “v k. ∃ u, !(termShiftVecGraph LAct) u k v”
noncomputable def termShiftVecTotal : ArithmeticSentence := ∀¹* termShiftVecTotalB

lemma models_termShiftVecTotal :
    V↓[ℒₒᵣ] ⊧ termShiftVecTotal ↔ ∀ v k : V, ∃ u, u = termShiftVec LAct k v := by
  simp [termShiftVecTotal, termShiftVecTotalB, models_iff, Matrix.vecForall_iff, termShiftVec.defined.iff]

theorem pa_proves_termShiftVecTotal : 𝗣𝗔 ⊢ termShiftVecTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termShiftVecTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_termShiftVecTotal : Lib termShiftVecTotal := Lib.of_pa pa_proves_termShiftVecTotal

/-! ### Formation -/

/-- `IsRel k R → IsSemitermVec k n v → IsSemiformula n (rel k R v)`. -/
noncomputable def isSemiformulaRelB : ArithmeticSemisentence 5 :=
  “p v R k n. !LAct.isRel k R → !(isSemitermVec LAct).pi k n v → !qqRelDef p k R v → !(isSemiformula LAct).sigma n p”
noncomputable def isSemiformulaRel : ArithmeticSentence := ∀¹* isSemiformulaRelB

lemma models_isSemiformulaRel :
    V↓[ℒₒᵣ] ⊧ isSemiformulaRel ↔ ∀ p v R k n : V, LAct.IsRel k R → IsSemitermVec LAct k n v → p = ^rel k R v → IsSemiformula LAct n p := by
  simp [isSemiformulaRel, isSemiformulaRelB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaRel : 𝗣𝗔 ⊢ isSemiformulaRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaRel.mpr fun _ _ _ _ _ hR hv h ↦ by subst h; exact IsSemiformula.rel.mpr ⟨hR, hv⟩

theorem lib_isSemiformulaRel : Lib isSemiformulaRel := Lib.of_pa pa_proves_isSemiformulaRel

/-- `IsRel k R → IsSemitermVec k n v → IsSemiformula n (nrel k R v)`. -/
noncomputable def isSemiformulaNRelB : ArithmeticSemisentence 5 :=
  “p v R k n. !LAct.isRel k R → !(isSemitermVec LAct).pi k n v → !qqNRelDef p k R v → !(isSemiformula LAct).sigma n p”
noncomputable def isSemiformulaNRel : ArithmeticSentence := ∀¹* isSemiformulaNRelB

lemma models_isSemiformulaNRel :
    V↓[ℒₒᵣ] ⊧ isSemiformulaNRel ↔ ∀ p v R k n : V, LAct.IsRel k R → IsSemitermVec LAct k n v → p = ^nrel k R v → IsSemiformula LAct n p := by
  simp [isSemiformulaNRel, isSemiformulaNRelB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaNRel : 𝗣𝗔 ⊢ isSemiformulaNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaNRel.mpr fun _ _ _ _ _ hR hv h ↦ by subst h; exact IsSemiformula.nrel.mpr ⟨hR, hv⟩

theorem lib_isSemiformulaNRel : Lib isSemiformulaNRel := Lib.of_pa pa_proves_isSemiformulaNRel

/-- `IsSemiformula n ⊤`. -/
noncomputable def isSemiformulaVerumB : ArithmeticSemisentence 2 :=
  “p n. !qqVerumDef p → !(isSemiformula LAct).sigma n p”
noncomputable def isSemiformulaVerum : ArithmeticSentence := ∀¹* isSemiformulaVerumB

lemma models_isSemiformulaVerum :
    V↓[ℒₒᵣ] ⊧ isSemiformulaVerum ↔ ∀ p n : V, p = ^⊤ → IsSemiformula LAct n p := by
  simp [isSemiformulaVerum, isSemiformulaVerumB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaVerum : 𝗣𝗔 ⊢ isSemiformulaVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaVerum.mpr fun _ _ h ↦ by subst h; exact IsSemiformula.verum

theorem lib_isSemiformulaVerum : Lib isSemiformulaVerum := Lib.of_pa pa_proves_isSemiformulaVerum

/-- `IsSemiformula n ⊥`. -/
noncomputable def isSemiformulaFalsumB : ArithmeticSemisentence 2 :=
  “p n. !qqFalsumDef p → !(isSemiformula LAct).sigma n p”
noncomputable def isSemiformulaFalsum : ArithmeticSentence := ∀¹* isSemiformulaFalsumB

lemma models_isSemiformulaFalsum :
    V↓[ℒₒᵣ] ⊧ isSemiformulaFalsum ↔ ∀ p n : V, p = ^⊥ → IsSemiformula LAct n p := by
  simp [isSemiformulaFalsum, isSemiformulaFalsumB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaFalsum : 𝗣𝗔 ⊢ isSemiformulaFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaFalsum.mpr fun _ _ h ↦ by subst h; exact IsSemiformula.falsum

theorem lib_isSemiformulaFalsum : Lib isSemiformulaFalsum := Lib.of_pa pa_proves_isSemiformulaFalsum

/-- `IsSemiformula n p → IsSemiformula n q → IsSemiformula n (p ⋏ q)`. -/
noncomputable def isSemiformulaAndB : ArithmeticSemisentence 4 :=
  “r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(isSemiformula LAct).sigma n r”
noncomputable def isSemiformulaAnd : ArithmeticSentence := ∀¹* isSemiformulaAndB

lemma models_isSemiformulaAnd :
    V↓[ℒₒᵣ] ⊧ isSemiformulaAnd ↔ ∀ r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → IsSemiformula LAct n r := by
  simp [isSemiformulaAnd, isSemiformulaAndB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaAnd : 𝗣𝗔 ⊢ isSemiformulaAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaAnd.mpr fun _ _ _ _ hp hq h ↦ by subst h; exact IsSemiformula.and.mpr ⟨hp, hq⟩

theorem lib_isSemiformulaAnd : Lib isSemiformulaAnd := Lib.of_pa pa_proves_isSemiformulaAnd

/-- `IsSemiformula n p → IsSemiformula n q → IsSemiformula n (p ⋎ q)`. -/
noncomputable def isSemiformulaOrB : ArithmeticSemisentence 4 :=
  “r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(isSemiformula LAct).sigma n r”
noncomputable def isSemiformulaOr : ArithmeticSentence := ∀¹* isSemiformulaOrB

lemma models_isSemiformulaOr :
    V↓[ℒₒᵣ] ⊧ isSemiformulaOr ↔ ∀ r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → IsSemiformula LAct n r := by
  simp [isSemiformulaOr, isSemiformulaOrB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaOr : 𝗣𝗔 ⊢ isSemiformulaOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaOr.mpr fun _ _ _ _ hp hq h ↦ by subst h; exact IsSemiformula.or.mpr ⟨hp, hq⟩

theorem lib_isSemiformulaOr : Lib isSemiformulaOr := Lib.of_pa pa_proves_isSemiformulaOr

/-- `IsSemiformula (n+1) p → IsSemiformula n (∀ p)`. -/
noncomputable def isSemiformulaAllB : ArithmeticSemisentence 3 :=
  “q p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef q p → !(isSemiformula LAct).sigma n q”
noncomputable def isSemiformulaAll : ArithmeticSentence := ∀¹* isSemiformulaAllB

lemma models_isSemiformulaAll :
    V↓[ℒₒᵣ] ⊧ isSemiformulaAll ↔ ∀ q p n : V, IsSemiformula LAct (n + 1) p → q = ^∀ p → IsSemiformula LAct n q := by
  simp [isSemiformulaAll, isSemiformulaAllB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaAll : 𝗣𝗔 ⊢ isSemiformulaAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaAll.mpr fun _ _ _ hp h ↦ by subst h; exact IsSemiformula.all.mpr hp

theorem lib_isSemiformulaAll : Lib isSemiformulaAll := Lib.of_pa pa_proves_isSemiformulaAll

/-- `IsSemiformula (n+1) p → IsSemiformula n (∃ p)`. -/
noncomputable def isSemiformulaExsB : ArithmeticSemisentence 3 :=
  “q p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef q p → !(isSemiformula LAct).sigma n q”
noncomputable def isSemiformulaExs : ArithmeticSentence := ∀¹* isSemiformulaExsB

lemma models_isSemiformulaExs :
    V↓[ℒₒᵣ] ⊧ isSemiformulaExs ↔ ∀ q p n : V, IsSemiformula LAct (n + 1) p → q = ^∃ p → IsSemiformula LAct n q := by
  simp [isSemiformulaExs, isSemiformulaExsB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaExs : 𝗣𝗔 ⊢ isSemiformulaExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaExs.mpr fun _ _ _ hp h ↦ by subst h; exact IsSemiformula.exs.mpr hp

theorem lib_isSemiformulaExs : Lib isSemiformulaExs := Lib.of_pa pa_proves_isSemiformulaExs

/-- `IsSemiformula n p → IsSemiformula n (neg p)`. -/
noncomputable def isSemiformulaNegB : ArithmeticSemisentence 3 :=
  “y p n. !(isSemiformula LAct).pi n p → !(negGraph LAct) y p → !(isSemiformula LAct).sigma n y”
noncomputable def isSemiformulaNeg : ArithmeticSentence := ∀¹* isSemiformulaNegB

lemma models_isSemiformulaNeg :
    V↓[ℒₒᵣ] ⊧ isSemiformulaNeg ↔ ∀ y p n : V, IsSemiformula LAct n p → y = neg LAct p → IsSemiformula LAct n y := by
  simp [isSemiformulaNeg, isSemiformulaNegB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_isSemiformulaNeg : 𝗣𝗔 ⊢ isSemiformulaNeg :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaNeg.mpr fun _ _ _ hp h ↦ by subst h; exact IsSemiformula.neg_iff.mpr hp

theorem lib_isSemiformulaNeg : Lib isSemiformulaNeg := Lib.of_pa pa_proves_isSemiformulaNeg

/-- `IsSemiformula n p → IsSemiformula n (shift p)`. -/
noncomputable def isSemiformulaShiftB : ArithmeticSemisentence 3 :=
  “y p n. !(isSemiformula LAct).pi n p → !(shiftGraph LAct) y p → !(isSemiformula LAct).sigma n y”
noncomputable def isSemiformulaShift : ArithmeticSentence := ∀¹* isSemiformulaShiftB

lemma models_isSemiformulaShift :
    V↓[ℒₒᵣ] ⊧ isSemiformulaShift ↔ ∀ y p n : V, IsSemiformula LAct n p → y = shift LAct p → IsSemiformula LAct n y := by
  simp [isSemiformulaShift, isSemiformulaShiftB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_isSemiformulaShift : 𝗣𝗔 ⊢ isSemiformulaShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaShift.mpr fun _ _ _ hp h ↦ by subst h; exact hp.shift

theorem lib_isSemiformulaShift : Lib isSemiformulaShift := Lib.of_pa pa_proves_isSemiformulaShift

/-- `IsSemiformula n p → IsSemitermVec n m w → IsSemiformula m (subst w p)`. -/
noncomputable def isSemiformulaSubstB : ArithmeticSemisentence 5 :=
  “y w p m n. !(isSemiformula LAct).pi n p → !(isSemitermVec LAct).pi n m w → !(substsGraph LAct) y w p → !(isSemiformula LAct).sigma m y”
noncomputable def isSemiformulaSubst : ArithmeticSentence := ∀¹* isSemiformulaSubstB

lemma models_isSemiformulaSubst :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSubst ↔ ∀ y w p m n : V, IsSemiformula LAct n p → IsSemitermVec LAct n m w → y = subst LAct w p → IsSemiformula LAct m y := by
  simp [isSemiformulaSubst, isSemiformulaSubstB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_isSemiformulaSubst : 𝗣𝗔 ⊢ isSemiformulaSubst :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSubst.mpr fun _ _ _ _ _ hp hw h ↦ by subst h; exact IsSemiformula.subst hp hw

theorem lib_isSemiformulaSubst : Lib isSemiformulaSubst := Lib.of_pa pa_proves_isSemiformulaSubst

/-- `IsSemiterm n t → IsSemiformula 1 p → IsSemiformula n (substs1 t p)`. -/
noncomputable def isSemiformulaSubsts1B : ArithmeticSemisentence 4 :=
  “y p t n. !(isSemiterm LAct).pi n t → !(isSemiformula LAct).pi 1 p → !(substs1Graph LAct) y t p → !(isSemiformula LAct).sigma n y”
noncomputable def isSemiformulaSubsts1 : ArithmeticSentence := ∀¹* isSemiformulaSubsts1B

lemma models_isSemiformulaSubsts1 :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSubsts1 ↔ ∀ y p t n : V, IsSemiterm LAct n t → IsSemiformula LAct 1 p → y = substs1 LAct t p → IsSemiformula LAct n y := by
  simp [isSemiformulaSubsts1, isSemiformulaSubsts1B, models_iff, Matrix.vecForall_iff, substs1.defined.iff]

theorem pa_proves_isSemiformulaSubsts1 : 𝗣𝗔 ⊢ isSemiformulaSubsts1 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSubsts1.mpr fun _ _ _ _ ht hp h ↦ by subst h; exact IsSemiformula.substs1 ht hp

theorem lib_isSemiformulaSubsts1 : Lib isSemiformulaSubsts1 := Lib.of_pa pa_proves_isSemiformulaSubsts1

/-- `IsSemiformula 1 p → IsFormula (free p)`. -/
noncomputable def isFormulaFreeB : ArithmeticSemisentence 2 :=
  “y p. !(isSemiformula LAct).pi 1 p → !(freeGraph LAct) y p → !(isSemiformula LAct).sigma 0 y”
noncomputable def isFormulaFree : ArithmeticSentence := ∀¹* isFormulaFreeB

lemma models_isFormulaFree :
    V↓[ℒₒᵣ] ⊧ isFormulaFree ↔ ∀ y p : V, IsSemiformula LAct 1 p → y = free LAct p → IsFormula LAct y := by
  simp [isFormulaFree, isFormulaFreeB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_isFormulaFree : 𝗣𝗔 ⊢ isFormulaFree :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaFree.mpr fun _ _ hp h ↦ by subst h; exact hp.free

theorem lib_isFormulaFree : Lib isFormulaFree := Lib.of_pa pa_proves_isFormulaFree

/-- `IsFunc k f → IsSemitermVec k n v → IsSemiterm n (func k f v)`. -/
noncomputable def isSemitermFuncB : ArithmeticSemisentence 5 :=
  “t v f k n. !LAct.isFunc k f → !(isSemitermVec LAct).pi k n v → !qqFuncDef t k f v → !(isSemiterm LAct).sigma n t”
noncomputable def isSemitermFunc : ArithmeticSentence := ∀¹* isSemitermFuncB

lemma models_isSemitermFunc :
    V↓[ℒₒᵣ] ⊧ isSemitermFunc ↔ ∀ t v f k n : V, LAct.IsFunc k f → IsSemitermVec LAct k n v → t = qqFunc k f v → IsSemiterm LAct n t := by
  simp [isSemitermFunc, isSemitermFuncB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemitermFunc : 𝗣𝗔 ⊢ isSemitermFunc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermFunc.mpr fun _ _ _ _ _ hf hv h ↦ by subst h; exact IsSemiterm.func.mpr ⟨hf, hv⟩

theorem lib_isSemitermFunc : Lib isSemitermFunc := Lib.of_pa pa_proves_isSemitermFunc

/-- `z < n → IsSemiterm n #z`. -/
noncomputable def isSemitermBvarB : ArithmeticSemisentence 3 :=
  “t z n. z < n → !qqBvarDef t z → !(isSemiterm LAct).sigma n t”
noncomputable def isSemitermBvar : ArithmeticSentence := ∀¹* isSemitermBvarB

lemma models_isSemitermBvar :
    V↓[ℒₒᵣ] ⊧ isSemitermBvar ↔ ∀ t z n : V, z < n → t = qqBvar z → IsSemiterm LAct n t := by
  simp [isSemitermBvar, isSemitermBvarB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemitermBvar : 𝗣𝗔 ⊢ isSemitermBvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermBvar.mpr fun _ _ _ hz h ↦ by subst h; exact IsSemiterm.bvar.mpr hz

theorem lib_isSemitermBvar : Lib isSemitermBvar := Lib.of_pa pa_proves_isSemitermBvar

/-- `IsSemiterm n &x`. -/
noncomputable def isSemitermFvarB : ArithmeticSemisentence 3 :=
  “t x n. !qqFvarDef t x → !(isSemiterm LAct).sigma n t”
noncomputable def isSemitermFvar : ArithmeticSentence := ∀¹* isSemitermFvarB

lemma models_isSemitermFvar :
    V↓[ℒₒᵣ] ⊧ isSemitermFvar ↔ ∀ t x n : V, t = qqFvar x → IsSemiterm LAct n t := by
  simp [isSemitermFvar, isSemitermFvarB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemitermFvar : 𝗣𝗔 ⊢ isSemitermFvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermFvar.mpr fun _ x n h ↦ by subst h; exact IsSemiterm.fvar n x

theorem lib_isSemitermFvar : Lib isSemitermFvar := Lib.of_pa pa_proves_isSemitermFvar

/-- `IsSemitermVec 0 n 0`. -/
noncomputable def isSemitermVecNilB : ArithmeticSemisentence 1 :=
  “n. !(isSemitermVec LAct).sigma 0 n 0”
noncomputable def isSemitermVecNil : ArithmeticSentence := ∀¹* isSemitermVecNilB

lemma models_isSemitermVecNil :
    V↓[ℒₒᵣ] ⊧ isSemitermVecNil ↔ ∀ n : V, IsSemitermVec LAct 0 n 0 := by
  simp [isSemitermVecNil, isSemitermVecNilB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemitermVecNil : 𝗣𝗔 ⊢ isSemitermVecNil :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecNil.mpr fun n ↦ IsSemitermVec.nil n

theorem lib_isSemitermVecNil : Lib isSemitermVecNil := Lib.of_pa pa_proves_isSemitermVecNil

/-- `IsSemitermVec k n w → IsSemiterm n t → IsSemitermVec (k+1) n (t ∷ w)`. -/
noncomputable def isSemitermVecAdjoinB : ArithmeticSemisentence 5 :=
  “u t w n k. !(isSemitermVec LAct).pi k n w → !(isSemiterm LAct).pi n t → !adjoinDef u t w → !(isSemitermVec LAct).sigma (k + 1) n u”
noncomputable def isSemitermVecAdjoin : ArithmeticSentence := ∀¹* isSemitermVecAdjoinB

lemma models_isSemitermVecAdjoin :
    V↓[ℒₒᵣ] ⊧ isSemitermVecAdjoin ↔ ∀ u t w n k : V, IsSemitermVec LAct k n w → IsSemiterm LAct n t → u = t ∷ w → IsSemitermVec LAct (k + 1) n u := by
  simp [isSemitermVecAdjoin, isSemitermVecAdjoinB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemitermVecAdjoin : 𝗣𝗔 ⊢ isSemitermVecAdjoin :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecAdjoin.mpr fun _ _ _ _ _ hw ht h ↦ by subst h; exact IsSemitermVec.adjoin hw ht

theorem lib_isSemitermVecAdjoin : Lib isSemitermVecAdjoin := Lib.of_pa pa_proves_isSemitermVecAdjoin

/-! ### Commutation: `neg` -/

/-- `neg (rel k R v) = nrel k R v`. -/
noncomputable def negRelB : ArithmeticSemisentence 5 :=
  “y r v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !(negGraph LAct) y r → !qqNRelDef y k R v”
noncomputable def negRel : ArithmeticSentence := ∀¹* negRelB

lemma models_negRel :
    V↓[ℒₒᵣ] ⊧ negRel ↔ ∀ y r v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → y = neg LAct r → y = ^nrel k R v := by
  simp [negRel, negRelB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negRel : 𝗣𝗔 ⊢ negRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negRel.mpr fun _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact neg_rel hR hv

theorem lib_negRel : Lib negRel := Lib.of_pa pa_proves_negRel

/-- `neg (nrel k R v) = rel k R v`. -/
noncomputable def negNRelB : ArithmeticSemisentence 5 :=
  “y r v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !(negGraph LAct) y r → !qqRelDef y k R v”
noncomputable def negNRel : ArithmeticSentence := ∀¹* negNRelB

lemma models_negNRel :
    V↓[ℒₒᵣ] ⊧ negNRel ↔ ∀ y r v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → y = neg LAct r → y = ^rel k R v := by
  simp [negNRel, negNRelB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negNRel : 𝗣𝗔 ⊢ negNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negNRel.mpr fun _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact neg_nrel hR hv

theorem lib_negNRel : Lib negNRel := Lib.of_pa pa_proves_negNRel

/-- `neg ⊤ = ⊥`. -/
noncomputable def negVerumB : ArithmeticSemisentence 2 :=
  “y r. !qqVerumDef r → !(negGraph LAct) y r → !qqFalsumDef y”
noncomputable def negVerum : ArithmeticSentence := ∀¹* negVerumB

lemma models_negVerum :
    V↓[ℒₒᵣ] ⊧ negVerum ↔ ∀ y r : V, r = ^⊤ → y = neg LAct r → y = ^⊥ := by
  simp [negVerum, negVerumB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negVerum : 𝗣𝗔 ⊢ negVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negVerum.mpr fun _ _ hr hy ↦ by subst hr; subst hy; exact neg_verum

theorem lib_negVerum : Lib negVerum := Lib.of_pa pa_proves_negVerum

/-- `neg ⊥ = ⊤`. -/
noncomputable def negFalsumB : ArithmeticSemisentence 2 :=
  “y r. !qqFalsumDef r → !(negGraph LAct) y r → !qqVerumDef y”
noncomputable def negFalsum : ArithmeticSentence := ∀¹* negFalsumB

lemma models_negFalsum :
    V↓[ℒₒᵣ] ⊧ negFalsum ↔ ∀ y r : V, r = ^⊥ → y = neg LAct r → y = ^⊤ := by
  simp [negFalsum, negFalsumB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negFalsum : 𝗣𝗔 ⊢ negFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negFalsum.mpr fun _ _ hr hy ↦ by subst hr; subst hy; exact neg_falsum

theorem lib_negFalsum : Lib negFalsum := Lib.of_pa pa_proves_negFalsum

/-- `neg (p ⋏ q) = neg p ⋎ neg q`. -/
noncomputable def negAndB : ArithmeticSemisentence 5 :=
  “y r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(negGraph LAct) y r → ∃ np nq, !(negGraph LAct) np p ∧ !(negGraph LAct) nq q ∧ !qqOrDef y np nq”
noncomputable def negAnd : ArithmeticSentence := ∀¹* negAndB

lemma models_negAnd :
    V↓[ℒₒᵣ] ⊧ negAnd ↔ ∀ y r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → y = neg LAct r → ∃ np nq, np = neg LAct p ∧ nq = neg LAct q ∧ y = np ^⋎ nq := by
  simp [negAnd, negAndB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negAnd : 𝗣𝗔 ⊢ negAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negAnd.mpr fun _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, neg_and hp.isUFormula hq.isUFormula⟩

theorem lib_negAnd : Lib negAnd := Lib.of_pa pa_proves_negAnd

/-- `neg (p ⋎ q) = neg p ⋏ neg q`. -/
noncomputable def negOrB : ArithmeticSemisentence 5 :=
  “y r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(negGraph LAct) y r → ∃ np nq, !(negGraph LAct) np p ∧ !(negGraph LAct) nq q ∧ !qqAndDef y np nq”
noncomputable def negOr : ArithmeticSentence := ∀¹* negOrB

lemma models_negOr :
    V↓[ℒₒᵣ] ⊧ negOr ↔ ∀ y r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → y = neg LAct r → ∃ np nq, np = neg LAct p ∧ nq = neg LAct q ∧ y = np ^⋏ nq := by
  simp [negOr, negOrB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negOr : 𝗣𝗔 ⊢ negOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negOr.mpr fun _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, neg_or hp.isUFormula hq.isUFormula⟩

theorem lib_negOr : Lib negOr := Lib.of_pa pa_proves_negOr

/-- `neg (∀ p) = ∃ (neg p)`. -/
noncomputable def negAllB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(negGraph LAct) y r → ∃ np, !(negGraph LAct) np p ∧ !qqExsDef y np”
noncomputable def negAll : ArithmeticSentence := ∀¹* negAllB

lemma models_negAll :
    V↓[ℒₒᵣ] ⊧ negAll ↔ ∀ y r p n : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → y = neg LAct r → ∃ np, np = neg LAct p ∧ y = ^∃ np := by
  simp [negAll, negAllB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negAll : 𝗣𝗔 ⊢ negAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negAll.mpr fun _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, neg_all hp.isUFormula⟩

theorem lib_negAll : Lib negAll := Lib.of_pa pa_proves_negAll

/-- `neg (∃ p) = ∀ (neg p)`. -/
noncomputable def negExsB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(negGraph LAct) y r → ∃ np, !(negGraph LAct) np p ∧ !qqAllDef y np”
noncomputable def negExs : ArithmeticSentence := ∀¹* negExsB

lemma models_negExs :
    V↓[ℒₒᵣ] ⊧ negExs ↔ ∀ y r p n : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → y = neg LAct r → ∃ np, np = neg LAct p ∧ y = ^∀ np := by
  simp [negExs, negExsB, models_iff, Matrix.vecForall_iff, neg.defined.iff]

theorem pa_proves_negExs : 𝗣𝗔 ⊢ negExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negExs.mpr fun _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, neg_ex hp.isUFormula⟩

theorem lib_negExs : Lib negExs := Lib.of_pa pa_proves_negExs

/-! ### Commutation: `subst` -/

/-- `subst w (rel k R v) = rel k R (termSubstVec k w v)`. -/
noncomputable def substsRelB : ArithmeticSemisentence 6 :=
  “y r v R k w. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !(substsGraph LAct) y w r → ∃ u, !(termSubstVecGraph LAct) u k w v ∧ !qqRelDef y k R u”
noncomputable def substsRel : ArithmeticSentence := ∀¹* substsRelB

lemma models_substsRel :
    V↓[ℒₒᵣ] ⊧ substsRel ↔ ∀ y r v R k w : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → y = subst LAct w r → ∃ u, u = termSubstVec LAct k w v ∧ y = ^rel k R u := by
  simp [substsRel, substsRelB, models_iff, Matrix.vecForall_iff, subst.defined.iff, termSubstVec.defined.iff]

theorem pa_proves_substsRel : 𝗣𝗔 ⊢ substsRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsRel.mpr fun _ _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, substs_rel hR hv⟩

theorem lib_substsRel : Lib substsRel := Lib.of_pa pa_proves_substsRel

/-- `subst w (nrel k R v) = nrel k R (termSubstVec k w v)`. -/
noncomputable def substsNRelB : ArithmeticSemisentence 6 :=
  “y r v R k w. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !(substsGraph LAct) y w r → ∃ u, !(termSubstVecGraph LAct) u k w v ∧ !qqNRelDef y k R u”
noncomputable def substsNRel : ArithmeticSentence := ∀¹* substsNRelB

lemma models_substsNRel :
    V↓[ℒₒᵣ] ⊧ substsNRel ↔ ∀ y r v R k w : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → y = subst LAct w r → ∃ u, u = termSubstVec LAct k w v ∧ y = ^nrel k R u := by
  simp [substsNRel, substsNRelB, models_iff, Matrix.vecForall_iff, subst.defined.iff, termSubstVec.defined.iff]

theorem pa_proves_substsNRel : 𝗣𝗔 ⊢ substsNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsNRel.mpr fun _ _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, substs_nrel hR hv⟩

theorem lib_substsNRel : Lib substsNRel := Lib.of_pa pa_proves_substsNRel

/-- `subst w ⊤ = ⊤`. -/
noncomputable def substsVerumB : ArithmeticSemisentence 3 :=
  “y r w. !qqVerumDef r → !(substsGraph LAct) y w r → !qqVerumDef y”
noncomputable def substsVerum : ArithmeticSentence := ∀¹* substsVerumB

lemma models_substsVerum :
    V↓[ℒₒᵣ] ⊧ substsVerum ↔ ∀ y r w : V, r = ^⊤ → y = subst LAct w r → y = ^⊤ := by
  simp [substsVerum, substsVerumB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsVerum : 𝗣𝗔 ⊢ substsVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsVerum.mpr fun _ _ w hr hy ↦ by subst hr; subst hy; exact substs_verum w

theorem lib_substsVerum : Lib substsVerum := Lib.of_pa pa_proves_substsVerum

/-- `subst w ⊥ = ⊥`. -/
noncomputable def substsFalsumB : ArithmeticSemisentence 3 :=
  “y r w. !qqFalsumDef r → !(substsGraph LAct) y w r → !qqFalsumDef y”
noncomputable def substsFalsum : ArithmeticSentence := ∀¹* substsFalsumB

lemma models_substsFalsum :
    V↓[ℒₒᵣ] ⊧ substsFalsum ↔ ∀ y r w : V, r = ^⊥ → y = subst LAct w r → y = ^⊥ := by
  simp [substsFalsum, substsFalsumB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsFalsum : 𝗣𝗔 ⊢ substsFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsFalsum.mpr fun _ _ w hr hy ↦ by subst hr; subst hy; exact substs_falsum w

theorem lib_substsFalsum : Lib substsFalsum := Lib.of_pa pa_proves_substsFalsum

/-- `subst w (p ⋏ q) = subst w p ⋏ subst w q`. -/
noncomputable def substsAndB : ArithmeticSemisentence 6 :=
  “y r q p n w. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(substsGraph LAct) y w r → ∃ sp sq, !(substsGraph LAct) sp w p ∧ !(substsGraph LAct) sq w q ∧ !qqAndDef y sp sq”
noncomputable def substsAnd : ArithmeticSentence := ∀¹* substsAndB

lemma models_substsAnd :
    V↓[ℒₒᵣ] ⊧ substsAnd ↔ ∀ y r q p n w : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → y = subst LAct w r → ∃ sp sq, sp = subst LAct w p ∧ sq = subst LAct w q ∧ y = sp ^⋏ sq := by
  simp [substsAnd, substsAndB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsAnd : 𝗣𝗔 ⊢ substsAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsAnd.mpr fun _ _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, substs_and hp.isUFormula hq.isUFormula⟩

theorem lib_substsAnd : Lib substsAnd := Lib.of_pa pa_proves_substsAnd

/-- `subst w (p ⋎ q) = subst w p ⋎ subst w q`. -/
noncomputable def substsOrB : ArithmeticSemisentence 6 :=
  “y r q p n w. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(substsGraph LAct) y w r → ∃ sp sq, !(substsGraph LAct) sp w p ∧ !(substsGraph LAct) sq w q ∧ !qqOrDef y sp sq”
noncomputable def substsOr : ArithmeticSentence := ∀¹* substsOrB

lemma models_substsOr :
    V↓[ℒₒᵣ] ⊧ substsOr ↔ ∀ y r q p n w : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → y = subst LAct w r → ∃ sp sq, sp = subst LAct w p ∧ sq = subst LAct w q ∧ y = sp ^⋎ sq := by
  simp [substsOr, substsOrB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsOr : 𝗣𝗔 ⊢ substsOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsOr.mpr fun _ _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, substs_or hp.isUFormula hq.isUFormula⟩

theorem lib_substsOr : Lib substsOr := Lib.of_pa pa_proves_substsOr

/-- `subst w (∀ p) = ∀ (subst (qVec w) p)`. -/
noncomputable def substsAllB : ArithmeticSemisentence 5 :=
  “y r p n w. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(substsGraph LAct) y w r → ∃ u sp, !(qVecGraph LAct) u w ∧ !(substsGraph LAct) sp u p ∧ !qqAllDef y sp”
noncomputable def substsAll : ArithmeticSentence := ∀¹* substsAllB

lemma models_substsAll :
    V↓[ℒₒᵣ] ⊧ substsAll ↔ ∀ y r p n w : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → y = subst LAct w r → ∃ u sp, u = qVec LAct w ∧ sp = subst LAct u p ∧ y = ^∀ sp := by
  simp [substsAll, substsAllB, models_iff, Matrix.vecForall_iff, subst.defined.iff, qVec.defined.iff]

theorem pa_proves_substsAll : 𝗣𝗔 ⊢ substsAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsAll.mpr fun _ _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, substs_all hp.isUFormula⟩

theorem lib_substsAll : Lib substsAll := Lib.of_pa pa_proves_substsAll

/-- `subst w (∃ p) = ∃ (subst (qVec w) p)`. -/
noncomputable def substsExsB : ArithmeticSemisentence 5 :=
  “y r p n w. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(substsGraph LAct) y w r → ∃ u sp, !(qVecGraph LAct) u w ∧ !(substsGraph LAct) sp u p ∧ !qqExsDef y sp”
noncomputable def substsExs : ArithmeticSentence := ∀¹* substsExsB

lemma models_substsExs :
    V↓[ℒₒᵣ] ⊧ substsExs ↔ ∀ y r p n w : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → y = subst LAct w r → ∃ u sp, u = qVec LAct w ∧ sp = subst LAct u p ∧ y = ^∃ sp := by
  simp [substsExs, substsExsB, models_iff, Matrix.vecForall_iff, subst.defined.iff, qVec.defined.iff]

theorem pa_proves_substsExs : 𝗣𝗔 ⊢ substsExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsExs.mpr fun _ _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, substs_ex hp.isUFormula⟩

theorem lib_substsExs : Lib substsExs := Lib.of_pa pa_proves_substsExs

/-! ### Commutation: `shift` -/

/-- `shift (rel k R v) = rel k R (termShiftVec k v)`. -/
noncomputable def shiftRelB : ArithmeticSemisentence 5 :=
  “y r v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !(shiftGraph LAct) y r → ∃ u, !(termShiftVecGraph LAct) u k v ∧ !qqRelDef y k R u”
noncomputable def shiftRel : ArithmeticSentence := ∀¹* shiftRelB

lemma models_shiftRel :
    V↓[ℒₒᵣ] ⊧ shiftRel ↔ ∀ y r v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → y = shift LAct r → ∃ u, u = termShiftVec LAct k v ∧ y = ^rel k R u := by
  simp [shiftRel, shiftRelB, models_iff, Matrix.vecForall_iff, shift.defined.iff, termShiftVec.defined.iff]

theorem pa_proves_shiftRel : 𝗣𝗔 ⊢ shiftRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftRel.mpr fun _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, shift_rel hR hv⟩

theorem lib_shiftRel : Lib shiftRel := Lib.of_pa pa_proves_shiftRel

/-- `shift (nrel k R v) = nrel k R (termShiftVec k v)`. -/
noncomputable def shiftNRelB : ArithmeticSemisentence 5 :=
  “y r v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !(shiftGraph LAct) y r → ∃ u, !(termShiftVecGraph LAct) u k v ∧ !qqNRelDef y k R u”
noncomputable def shiftNRel : ArithmeticSentence := ∀¹* shiftNRelB

lemma models_shiftNRel :
    V↓[ℒₒᵣ] ⊧ shiftNRel ↔ ∀ y r v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → y = shift LAct r → ∃ u, u = termShiftVec LAct k v ∧ y = ^nrel k R u := by
  simp [shiftNRel, shiftNRelB, models_iff, Matrix.vecForall_iff, shift.defined.iff, termShiftVec.defined.iff]

theorem pa_proves_shiftNRel : 𝗣𝗔 ⊢ shiftNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftNRel.mpr fun _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, shift_nrel hR hv⟩

theorem lib_shiftNRel : Lib shiftNRel := Lib.of_pa pa_proves_shiftNRel

/-- `shift ⊤ = ⊤`. -/
noncomputable def shiftVerumB : ArithmeticSemisentence 2 :=
  “y r. !qqVerumDef r → !(shiftGraph LAct) y r → !qqVerumDef y”
noncomputable def shiftVerum : ArithmeticSentence := ∀¹* shiftVerumB

lemma models_shiftVerum :
    V↓[ℒₒᵣ] ⊧ shiftVerum ↔ ∀ y r : V, r = ^⊤ → y = shift LAct r → y = ^⊤ := by
  simp [shiftVerum, shiftVerumB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftVerum : 𝗣𝗔 ⊢ shiftVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftVerum.mpr fun _ _ hr hy ↦ by subst hr; subst hy; exact shift_verum

theorem lib_shiftVerum : Lib shiftVerum := Lib.of_pa pa_proves_shiftVerum

/-- `shift ⊥ = ⊥`. -/
noncomputable def shiftFalsumB : ArithmeticSemisentence 2 :=
  “y r. !qqFalsumDef r → !(shiftGraph LAct) y r → !qqFalsumDef y”
noncomputable def shiftFalsum : ArithmeticSentence := ∀¹* shiftFalsumB

lemma models_shiftFalsum :
    V↓[ℒₒᵣ] ⊧ shiftFalsum ↔ ∀ y r : V, r = ^⊥ → y = shift LAct r → y = ^⊥ := by
  simp [shiftFalsum, shiftFalsumB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftFalsum : 𝗣𝗔 ⊢ shiftFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftFalsum.mpr fun _ _ hr hy ↦ by subst hr; subst hy; exact shift_falsum

theorem lib_shiftFalsum : Lib shiftFalsum := Lib.of_pa pa_proves_shiftFalsum

/-- `shift (p ⋏ q) = shift p ⋏ shift q`. -/
noncomputable def shiftAndB : ArithmeticSemisentence 5 :=
  “y r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(shiftGraph LAct) y r → ∃ sp sq, !(shiftGraph LAct) sp p ∧ !(shiftGraph LAct) sq q ∧ !qqAndDef y sp sq”
noncomputable def shiftAnd : ArithmeticSentence := ∀¹* shiftAndB

lemma models_shiftAnd :
    V↓[ℒₒᵣ] ⊧ shiftAnd ↔ ∀ y r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → y = shift LAct r → ∃ sp sq, sp = shift LAct p ∧ sq = shift LAct q ∧ y = sp ^⋏ sq := by
  simp [shiftAnd, shiftAndB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftAnd : 𝗣𝗔 ⊢ shiftAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftAnd.mpr fun _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, shift_and hp.isUFormula hq.isUFormula⟩

theorem lib_shiftAnd : Lib shiftAnd := Lib.of_pa pa_proves_shiftAnd

/-- `shift (p ⋎ q) = shift p ⋎ shift q`. -/
noncomputable def shiftOrB : ArithmeticSemisentence 5 :=
  “y r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(shiftGraph LAct) y r → ∃ sp sq, !(shiftGraph LAct) sp p ∧ !(shiftGraph LAct) sq q ∧ !qqOrDef y sp sq”
noncomputable def shiftOr : ArithmeticSentence := ∀¹* shiftOrB

lemma models_shiftOr :
    V↓[ℒₒᵣ] ⊧ shiftOr ↔ ∀ y r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → y = shift LAct r → ∃ sp sq, sp = shift LAct p ∧ sq = shift LAct q ∧ y = sp ^⋎ sq := by
  simp [shiftOr, shiftOrB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftOr : 𝗣𝗔 ⊢ shiftOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftOr.mpr fun _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, shift_or hp.isUFormula hq.isUFormula⟩

theorem lib_shiftOr : Lib shiftOr := Lib.of_pa pa_proves_shiftOr

/-- `shift (∀ p) = ∀ (shift p)`. -/
noncomputable def shiftAllB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(shiftGraph LAct) y r → ∃ sp, !(shiftGraph LAct) sp p ∧ !qqAllDef y sp”
noncomputable def shiftAll : ArithmeticSentence := ∀¹* shiftAllB

lemma models_shiftAll :
    V↓[ℒₒᵣ] ⊧ shiftAll ↔ ∀ y r p n : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → y = shift LAct r → ∃ sp, sp = shift LAct p ∧ y = ^∀ sp := by
  simp [shiftAll, shiftAllB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftAll : 𝗣𝗔 ⊢ shiftAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftAll.mpr fun _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, shift_all hp.isUFormula⟩

theorem lib_shiftAll : Lib shiftAll := Lib.of_pa pa_proves_shiftAll

/-- `shift (∃ p) = ∃ (shift p)`. -/
noncomputable def shiftExsB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(shiftGraph LAct) y r → ∃ sp, !(shiftGraph LAct) sp p ∧ !qqExsDef y sp”
noncomputable def shiftExs : ArithmeticSentence := ∀¹* shiftExsB

lemma models_shiftExs :
    V↓[ℒₒᵣ] ⊧ shiftExs ↔ ∀ y r p n : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → y = shift LAct r → ∃ sp, sp = shift LAct p ∧ y = ^∃ sp := by
  simp [shiftExs, shiftExsB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftExs : 𝗣𝗔 ⊢ shiftExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftExs.mpr fun _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, rfl, shift_exs hp.isUFormula⟩

theorem lib_shiftExs : Lib shiftExs := Lib.of_pa pa_proves_shiftExs

/-! ### Commutation: `free` -/

/-- `free (rel k R v) = rel k R (termSubstVec k ?[&0] (termShiftVec k v))`. -/
noncomputable def freeRelB : ArithmeticSemisentence 5 :=
  “y r v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !(freeGraph LAct) y r → ∃ fz w, !qqFvarDef fz 0 ∧ !adjoinDef w fz 0 ∧ ∃ u u', !(termShiftVecGraph LAct) u k v ∧ !(termSubstVecGraph LAct) u' k w u ∧ !qqRelDef y k R u'”
noncomputable def freeRel : ArithmeticSentence := ∀¹* freeRelB

lemma models_freeRel :
    V↓[ℒₒᵣ] ⊧ freeRel ↔ ∀ y r v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → y = free LAct r → ∃ fz w, fz = qqFvar 0 ∧ w = fz ∷ 0 ∧ ∃ u u', u = termShiftVec LAct k v ∧ u' = termSubstVec LAct k w u ∧ y = ^rel k R u' := by
  simp [freeRel, freeRelB, models_iff, Matrix.vecForall_iff, free.defined.iff, termShiftVec.defined.iff, termSubstVec.defined.iff]

theorem pa_proves_freeRel : 𝗣𝗔 ⊢ freeRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeRel.mpr fun _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, _, _, rfl, rfl, free_rel hR hv⟩

theorem lib_freeRel : Lib freeRel := Lib.of_pa pa_proves_freeRel

/-- `free (nrel k R v) = nrel k R (termSubstVec k ?[&0] (termShiftVec k v))`. -/
noncomputable def freeNRelB : ArithmeticSemisentence 5 :=
  “y r v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !(freeGraph LAct) y r → ∃ fz w, !qqFvarDef fz 0 ∧ !adjoinDef w fz 0 ∧ ∃ u u', !(termShiftVecGraph LAct) u k v ∧ !(termSubstVecGraph LAct) u' k w u ∧ !qqNRelDef y k R u'”
noncomputable def freeNRel : ArithmeticSentence := ∀¹* freeNRelB

lemma models_freeNRel :
    V↓[ℒₒᵣ] ⊧ freeNRel ↔ ∀ y r v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → y = free LAct r → ∃ fz w, fz = qqFvar 0 ∧ w = fz ∷ 0 ∧ ∃ u u', u = termShiftVec LAct k v ∧ u' = termSubstVec LAct k w u ∧ y = ^nrel k R u' := by
  simp [freeNRel, freeNRelB, models_iff, Matrix.vecForall_iff, free.defined.iff, termShiftVec.defined.iff, termSubstVec.defined.iff]

theorem pa_proves_freeNRel : 𝗣𝗔 ⊢ freeNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeNRel.mpr fun _ _ _ _ _ hR hv hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, _, _, rfl, rfl, free_nrel hR hv⟩

theorem lib_freeNRel : Lib freeNRel := Lib.of_pa pa_proves_freeNRel

/-- `free ⊤ = ⊤`. -/
noncomputable def freeVerumB : ArithmeticSemisentence 2 :=
  “y r. !qqVerumDef r → !(freeGraph LAct) y r → !qqVerumDef y”
noncomputable def freeVerum : ArithmeticSentence := ∀¹* freeVerumB

lemma models_freeVerum :
    V↓[ℒₒᵣ] ⊧ freeVerum ↔ ∀ y r : V, r = ^⊤ → y = free LAct r → y = ^⊤ := by
  simp [freeVerum, freeVerumB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_freeVerum : 𝗣𝗔 ⊢ freeVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeVerum.mpr fun _ _ hr hy ↦ by subst hr; subst hy; exact free_verum

theorem lib_freeVerum : Lib freeVerum := Lib.of_pa pa_proves_freeVerum

/-- `free ⊥ = ⊥`. -/
noncomputable def freeFalsumB : ArithmeticSemisentence 2 :=
  “y r. !qqFalsumDef r → !(freeGraph LAct) y r → !qqFalsumDef y”
noncomputable def freeFalsum : ArithmeticSentence := ∀¹* freeFalsumB

lemma models_freeFalsum :
    V↓[ℒₒᵣ] ⊧ freeFalsum ↔ ∀ y r : V, r = ^⊥ → y = free LAct r → y = ^⊥ := by
  simp [freeFalsum, freeFalsumB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_freeFalsum : 𝗣𝗔 ⊢ freeFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeFalsum.mpr fun _ _ hr hy ↦ by subst hr; subst hy; exact free_falsum

theorem lib_freeFalsum : Lib freeFalsum := Lib.of_pa pa_proves_freeFalsum

/-- `free (p ⋏ q) = free p ⋏ free q`. -/
noncomputable def freeAndB : ArithmeticSemisentence 5 :=
  “y r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(freeGraph LAct) y r → ∃ fp fq, !(freeGraph LAct) fp p ∧ !(freeGraph LAct) fq q ∧ !qqAndDef y fp fq”
noncomputable def freeAnd : ArithmeticSentence := ∀¹* freeAndB

lemma models_freeAnd :
    V↓[ℒₒᵣ] ⊧ freeAnd ↔ ∀ y r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → y = free LAct r → ∃ fp fq, fp = free LAct p ∧ fq = free LAct q ∧ y = fp ^⋏ fq := by
  simp [freeAnd, freeAndB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_freeAnd : 𝗣𝗔 ⊢ freeAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeAnd.mpr fun _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, free_and hp.isUFormula hq.isUFormula⟩

theorem lib_freeAnd : Lib freeAnd := Lib.of_pa pa_proves_freeAnd

/-- `free (p ⋎ q) = free p ⋎ free q`. -/
noncomputable def freeOrB : ArithmeticSemisentence 5 :=
  “y r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(freeGraph LAct) y r → ∃ fp fq, !(freeGraph LAct) fp p ∧ !(freeGraph LAct) fq q ∧ !qqOrDef y fp fq”
noncomputable def freeOr : ArithmeticSentence := ∀¹* freeOrB

lemma models_freeOr :
    V↓[ℒₒᵣ] ⊧ freeOr ↔ ∀ y r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → y = free LAct r → ∃ fp fq, fp = free LAct p ∧ fq = free LAct q ∧ y = fp ^⋎ fq := by
  simp [freeOr, freeOrB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_freeOr : 𝗣𝗔 ⊢ freeOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeOr.mpr fun _ _ _ _ _ hp hq hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, free_or hp.isUFormula hq.isUFormula⟩

theorem lib_freeOr : Lib freeOr := Lib.of_pa pa_proves_freeOr

/-- `free (∀ p) = ∀ (subst (qVec ?[&0]) (shift p))`. -/
noncomputable def freeAllB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(freeGraph LAct) y r → ∃ fz w, !qqFvarDef fz 0 ∧ !adjoinDef w fz 0 ∧ ∃ u sp sp', !(qVecGraph LAct) u w ∧ !(shiftGraph LAct) sp p ∧ !(substsGraph LAct) sp' u sp ∧ !qqAllDef y sp'”
noncomputable def freeAll : ArithmeticSentence := ∀¹* freeAllB

lemma models_freeAll :
    V↓[ℒₒᵣ] ⊧ freeAll ↔ ∀ y r p n : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → y = free LAct r → ∃ fz w, fz = qqFvar 0 ∧ w = fz ∷ 0 ∧ ∃ u sp sp', u = qVec LAct w ∧ sp = shift LAct p ∧ sp' = subst LAct u sp ∧ y = ^∀ sp' := by
  simp [freeAll, freeAllB, models_iff, Matrix.vecForall_iff, free.defined.iff, qVec.defined.iff, shift.defined.iff, subst.defined.iff]

theorem pa_proves_freeAll : 𝗣𝗔 ⊢ freeAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeAll.mpr fun _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, _, _, _, rfl, rfl, rfl, free_all hp.isUFormula⟩

theorem lib_freeAll : Lib freeAll := Lib.of_pa pa_proves_freeAll

/-- `free (∃ p) = ∃ (subst (qVec ?[&0]) (shift p))`. -/
noncomputable def freeExsB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(freeGraph LAct) y r → ∃ fz w, !qqFvarDef fz 0 ∧ !adjoinDef w fz 0 ∧ ∃ u sp sp', !(qVecGraph LAct) u w ∧ !(shiftGraph LAct) sp p ∧ !(substsGraph LAct) sp' u sp ∧ !qqExsDef y sp'”
noncomputable def freeExs : ArithmeticSentence := ∀¹* freeExsB

lemma models_freeExs :
    V↓[ℒₒᵣ] ⊧ freeExs ↔ ∀ y r p n : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → y = free LAct r → ∃ fz w, fz = qqFvar 0 ∧ w = fz ∷ 0 ∧ ∃ u sp sp', u = qVec LAct w ∧ sp = shift LAct p ∧ sp' = subst LAct u sp ∧ y = ^∃ sp' := by
  simp [freeExs, freeExsB, models_iff, Matrix.vecForall_iff, free.defined.iff, qVec.defined.iff, shift.defined.iff, subst.defined.iff]

theorem pa_proves_freeExs : 𝗣𝗔 ⊢ freeExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeExs.mpr fun _ _ _ _ hp hr hy ↦ by subst hr; subst hy; exact ⟨_, _, rfl, rfl, _, _, _, rfl, rfl, rfl, free_exs hp.isUFormula⟩

theorem lib_freeExs : Lib freeExs := Lib.of_pa pa_proves_freeExs

/-! ### Shape inversion: `shift` -/

/-- `shift r = rel k R v → ∃ v', r = rel k R v' ∧ v = termShiftVec k v'`. -/
noncomputable def shiftInvRelB : ArithmeticSemisentence 6 :=
  “v R k y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqRelDef y k R v → ∃ u, !qqRelDef r k R u ∧ !(termShiftVecGraph LAct) v k u”
noncomputable def shiftInvRel : ArithmeticSentence := ∀¹* shiftInvRelB

lemma models_shiftInvRel :
    V↓[ℒₒᵣ] ⊧ shiftInvRel ↔ ∀ v R k y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = ^rel k R v → ∃ u, r = ^rel k R u ∧ v = termShiftVec LAct k u := by
  simp [shiftInvRel, shiftInvRelB, models_iff, Matrix.vecForall_iff, shift.defined.iff, termShiftVec.defined.iff]

theorem pa_proves_shiftInvRel : 𝗣𝗔 ⊢ shiftInvRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvRel.mpr fun _ _ _ _ _ _ hr hy h ↦ by subst hy; exact shift_eq_rel_inv hr h

theorem lib_shiftInvRel : Lib shiftInvRel := Lib.of_pa pa_proves_shiftInvRel

/-- `shift r = nrel k R v → ∃ v', r = nrel k R v' ∧ v = termShiftVec k v'`. -/
noncomputable def shiftInvNRelB : ArithmeticSemisentence 6 :=
  “v R k y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqNRelDef y k R v → ∃ u, !qqNRelDef r k R u ∧ !(termShiftVecGraph LAct) v k u”
noncomputable def shiftInvNRel : ArithmeticSentence := ∀¹* shiftInvNRelB

lemma models_shiftInvNRel :
    V↓[ℒₒᵣ] ⊧ shiftInvNRel ↔ ∀ v R k y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = ^nrel k R v → ∃ u, r = ^nrel k R u ∧ v = termShiftVec LAct k u := by
  simp [shiftInvNRel, shiftInvNRelB, models_iff, Matrix.vecForall_iff, shift.defined.iff, termShiftVec.defined.iff]

theorem pa_proves_shiftInvNRel : 𝗣𝗔 ⊢ shiftInvNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvNRel.mpr fun _ _ _ _ _ _ hr hy h ↦ by subst hy; exact shift_eq_nrel_inv hr h

theorem lib_shiftInvNRel : Lib shiftInvNRel := Lib.of_pa pa_proves_shiftInvNRel

/-- `shift r = ⊤ → r = ⊤`. -/
noncomputable def shiftInvVerumB : ArithmeticSemisentence 3 :=
  “y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqVerumDef y → !qqVerumDef r”
noncomputable def shiftInvVerum : ArithmeticSentence := ∀¹* shiftInvVerumB

lemma models_shiftInvVerum :
    V↓[ℒₒᵣ] ⊧ shiftInvVerum ↔ ∀ y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = ^⊤ → r = ^⊤ := by
  simp [shiftInvVerum, shiftInvVerumB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftInvVerum : 𝗣𝗔 ⊢ shiftInvVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvVerum.mpr fun _ _ _ hr hy h ↦ by subst hy; exact shift_eq_verum_inv hr h

theorem lib_shiftInvVerum : Lib shiftInvVerum := Lib.of_pa pa_proves_shiftInvVerum

/-- `shift r = ⊥ → r = ⊥`. -/
noncomputable def shiftInvFalsumB : ArithmeticSemisentence 3 :=
  “y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqFalsumDef y → !qqFalsumDef r”
noncomputable def shiftInvFalsum : ArithmeticSentence := ∀¹* shiftInvFalsumB

lemma models_shiftInvFalsum :
    V↓[ℒₒᵣ] ⊧ shiftInvFalsum ↔ ∀ y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = ^⊥ → r = ^⊥ := by
  simp [shiftInvFalsum, shiftInvFalsumB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftInvFalsum : 𝗣𝗔 ⊢ shiftInvFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvFalsum.mpr fun _ _ _ hr hy h ↦ by subst hy; exact shift_eq_falsum_inv hr h

theorem lib_shiftInvFalsum : Lib shiftInvFalsum := Lib.of_pa pa_proves_shiftInvFalsum

/-- `shift r = p ⋏ q → ∃ p' q', r = p' ⋏ q' ∧ p = shift p' ∧ q = shift q'`. -/
noncomputable def shiftInvAndB : ArithmeticSemisentence 5 :=
  “q p y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqAndDef y p q → ∃ p' q', !qqAndDef r p' q' ∧ !(shiftGraph LAct) p p' ∧ !(shiftGraph LAct) q q'”
noncomputable def shiftInvAnd : ArithmeticSentence := ∀¹* shiftInvAndB

lemma models_shiftInvAnd :
    V↓[ℒₒᵣ] ⊧ shiftInvAnd ↔ ∀ q p y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = p ^⋏ q → ∃ p' q', r = p' ^⋏ q' ∧ p = shift LAct p' ∧ q = shift LAct q' := by
  simp [shiftInvAnd, shiftInvAndB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftInvAnd : 𝗣𝗔 ⊢ shiftInvAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvAnd.mpr fun _ _ _ _ _ hr hy h ↦ by subst hy; exact shift_eq_and_inv hr h

theorem lib_shiftInvAnd : Lib shiftInvAnd := Lib.of_pa pa_proves_shiftInvAnd

/-- `shift r = p ⋎ q → ∃ p' q', r = p' ⋎ q' ∧ p = shift p' ∧ q = shift q'`. -/
noncomputable def shiftInvOrB : ArithmeticSemisentence 5 :=
  “q p y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqOrDef y p q → ∃ p' q', !qqOrDef r p' q' ∧ !(shiftGraph LAct) p p' ∧ !(shiftGraph LAct) q q'”
noncomputable def shiftInvOr : ArithmeticSentence := ∀¹* shiftInvOrB

lemma models_shiftInvOr :
    V↓[ℒₒᵣ] ⊧ shiftInvOr ↔ ∀ q p y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = p ^⋎ q → ∃ p' q', r = p' ^⋎ q' ∧ p = shift LAct p' ∧ q = shift LAct q' := by
  simp [shiftInvOr, shiftInvOrB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftInvOr : 𝗣𝗔 ⊢ shiftInvOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvOr.mpr fun _ _ _ _ _ hr hy h ↦ by subst hy; exact shift_eq_or_inv hr h

theorem lib_shiftInvOr : Lib shiftInvOr := Lib.of_pa pa_proves_shiftInvOr

/-- `shift r = ∀ p → ∃ p', r = ∀ p' ∧ p = shift p'`. -/
noncomputable def shiftInvAllB : ArithmeticSemisentence 4 :=
  “p y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqAllDef y p → ∃ p', !qqAllDef r p' ∧ !(shiftGraph LAct) p p'”
noncomputable def shiftInvAll : ArithmeticSentence := ∀¹* shiftInvAllB

lemma models_shiftInvAll :
    V↓[ℒₒᵣ] ⊧ shiftInvAll ↔ ∀ p y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = ^∀ p → ∃ p', r = ^∀ p' ∧ p = shift LAct p' := by
  simp [shiftInvAll, shiftInvAllB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftInvAll : 𝗣𝗔 ⊢ shiftInvAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvAll.mpr fun _ _ _ _ hr hy h ↦ by subst hy; exact shift_eq_all_inv hr h

theorem lib_shiftInvAll : Lib shiftInvAll := Lib.of_pa pa_proves_shiftInvAll

/-- `shift r = ∃ p → ∃ p', r = ∃ p' ∧ p = shift p'`. -/
noncomputable def shiftInvExsB : ArithmeticSemisentence 4 :=
  “p y r n. !(isSemiformula LAct).pi n r → !(shiftGraph LAct) y r → !qqExsDef y p → ∃ p', !qqExsDef r p' ∧ !(shiftGraph LAct) p p'”
noncomputable def shiftInvExs : ArithmeticSentence := ∀¹* shiftInvExsB

lemma models_shiftInvExs :
    V↓[ℒₒᵣ] ⊧ shiftInvExs ↔ ∀ p y r n : V, IsSemiformula LAct n r → y = shift LAct r → y = ^∃ p → ∃ p', r = ^∃ p' ∧ p = shift LAct p' := by
  simp [shiftInvExs, shiftInvExsB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftInvExs : 𝗣𝗔 ⊢ shiftInvExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftInvExs.mpr fun _ _ _ _ hr hy h ↦ by subst hy; exact shift_eq_exs_inv hr h

theorem lib_shiftInvExs : Lib shiftInvExs := Lib.of_pa pa_proves_shiftInvExs

/-! ### Shape inversion: `subst` -/

/-- `subst w r = rel k R v → ∃ v', r = rel k R v' ∧ v = termSubstVec k w v'`. -/
noncomputable def substsInvRelB : ArithmeticSemisentence 7 :=
  “v R k y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqRelDef y k R v → ∃ u, !qqRelDef r k R u ∧ !(termSubstVecGraph LAct) v k w u”
noncomputable def substsInvRel : ArithmeticSentence := ∀¹* substsInvRelB

lemma models_substsInvRel :
    V↓[ℒₒᵣ] ⊧ substsInvRel ↔ ∀ v R k y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = ^rel k R v → ∃ u, r = ^rel k R u ∧ v = termSubstVec LAct k w u := by
  simp [substsInvRel, substsInvRelB, models_iff, Matrix.vecForall_iff, subst.defined.iff, termSubstVec.defined.iff]

theorem pa_proves_substsInvRel : 𝗣𝗔 ⊢ substsInvRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvRel.mpr fun _ _ _ _ _ _ _ hr hy h ↦ by subst hy; exact substs_eq_rel_inv hr h

theorem lib_substsInvRel : Lib substsInvRel := Lib.of_pa pa_proves_substsInvRel

/-- `subst w r = nrel k R v → ∃ v', r = nrel k R v' ∧ v = termSubstVec k w v'`. -/
noncomputable def substsInvNRelB : ArithmeticSemisentence 7 :=
  “v R k y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqNRelDef y k R v → ∃ u, !qqNRelDef r k R u ∧ !(termSubstVecGraph LAct) v k w u”
noncomputable def substsInvNRel : ArithmeticSentence := ∀¹* substsInvNRelB

lemma models_substsInvNRel :
    V↓[ℒₒᵣ] ⊧ substsInvNRel ↔ ∀ v R k y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = ^nrel k R v → ∃ u, r = ^nrel k R u ∧ v = termSubstVec LAct k w u := by
  simp [substsInvNRel, substsInvNRelB, models_iff, Matrix.vecForall_iff, subst.defined.iff, termSubstVec.defined.iff]

theorem pa_proves_substsInvNRel : 𝗣𝗔 ⊢ substsInvNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvNRel.mpr fun _ _ _ _ _ _ _ hr hy h ↦ by subst hy; exact substs_eq_nrel_inv hr h

theorem lib_substsInvNRel : Lib substsInvNRel := Lib.of_pa pa_proves_substsInvNRel

/-- `subst w r = ⊤ → r = ⊤`. -/
noncomputable def substsInvVerumB : ArithmeticSemisentence 4 :=
  “y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqVerumDef y → !qqVerumDef r”
noncomputable def substsInvVerum : ArithmeticSentence := ∀¹* substsInvVerumB

lemma models_substsInvVerum :
    V↓[ℒₒᵣ] ⊧ substsInvVerum ↔ ∀ y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = ^⊤ → r = ^⊤ := by
  simp [substsInvVerum, substsInvVerumB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsInvVerum : 𝗣𝗔 ⊢ substsInvVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvVerum.mpr fun _ _ _ _ hr hy h ↦ by subst hy; exact substs_eq_verum_inv hr h

theorem lib_substsInvVerum : Lib substsInvVerum := Lib.of_pa pa_proves_substsInvVerum

/-- `subst w r = ⊥ → r = ⊥`. -/
noncomputable def substsInvFalsumB : ArithmeticSemisentence 4 :=
  “y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqFalsumDef y → !qqFalsumDef r”
noncomputable def substsInvFalsum : ArithmeticSentence := ∀¹* substsInvFalsumB

lemma models_substsInvFalsum :
    V↓[ℒₒᵣ] ⊧ substsInvFalsum ↔ ∀ y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = ^⊥ → r = ^⊥ := by
  simp [substsInvFalsum, substsInvFalsumB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsInvFalsum : 𝗣𝗔 ⊢ substsInvFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvFalsum.mpr fun _ _ _ _ hr hy h ↦ by subst hy; exact substs_eq_falsum_inv hr h

theorem lib_substsInvFalsum : Lib substsInvFalsum := Lib.of_pa pa_proves_substsInvFalsum

/-- `subst w r = p ⋏ q → ∃ p' q', r = p' ⋏ q' ∧ p = subst w p' ∧ q = subst w q'`. -/
noncomputable def substsInvAndB : ArithmeticSemisentence 6 :=
  “q p y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqAndDef y p q → ∃ p' q', !qqAndDef r p' q' ∧ !(substsGraph LAct) p w p' ∧ !(substsGraph LAct) q w q'”
noncomputable def substsInvAnd : ArithmeticSentence := ∀¹* substsInvAndB

lemma models_substsInvAnd :
    V↓[ℒₒᵣ] ⊧ substsInvAnd ↔ ∀ q p y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = p ^⋏ q → ∃ p' q', r = p' ^⋏ q' ∧ p = subst LAct w p' ∧ q = subst LAct w q' := by
  simp [substsInvAnd, substsInvAndB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsInvAnd : 𝗣𝗔 ⊢ substsInvAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvAnd.mpr fun _ _ _ _ _ _ hr hy h ↦ by subst hy; exact substs_eq_and_inv hr h

theorem lib_substsInvAnd : Lib substsInvAnd := Lib.of_pa pa_proves_substsInvAnd

/-- `subst w r = p ⋎ q → ∃ p' q', r = p' ⋎ q' ∧ p = subst w p' ∧ q = subst w q'`. -/
noncomputable def substsInvOrB : ArithmeticSemisentence 6 :=
  “q p y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqOrDef y p q → ∃ p' q', !qqOrDef r p' q' ∧ !(substsGraph LAct) p w p' ∧ !(substsGraph LAct) q w q'”
noncomputable def substsInvOr : ArithmeticSentence := ∀¹* substsInvOrB

lemma models_substsInvOr :
    V↓[ℒₒᵣ] ⊧ substsInvOr ↔ ∀ q p y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = p ^⋎ q → ∃ p' q', r = p' ^⋎ q' ∧ p = subst LAct w p' ∧ q = subst LAct w q' := by
  simp [substsInvOr, substsInvOrB, models_iff, Matrix.vecForall_iff, subst.defined.iff]

theorem pa_proves_substsInvOr : 𝗣𝗔 ⊢ substsInvOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvOr.mpr fun _ _ _ _ _ _ hr hy h ↦ by subst hy; exact substs_eq_or_inv hr h

theorem lib_substsInvOr : Lib substsInvOr := Lib.of_pa pa_proves_substsInvOr

/-- `subst w r = ∀ p → ∃ p', r = ∀ p' ∧ p = subst (qVec w) p'`. -/
noncomputable def substsInvAllB : ArithmeticSemisentence 5 :=
  “p y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqAllDef y p → ∃ p' u, !qqAllDef r p' ∧ !(qVecGraph LAct) u w ∧ !(substsGraph LAct) p u p'”
noncomputable def substsInvAll : ArithmeticSentence := ∀¹* substsInvAllB

lemma models_substsInvAll :
    V↓[ℒₒᵣ] ⊧ substsInvAll ↔ ∀ p y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = ^∀ p → ∃ p' u, r = ^∀ p' ∧ u = qVec LAct w ∧ p = subst LAct u p' := by
  simp [substsInvAll, substsInvAllB, models_iff, Matrix.vecForall_iff, subst.defined.iff, qVec.defined.iff]

theorem pa_proves_substsInvAll : 𝗣𝗔 ⊢ substsInvAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvAll.mpr fun _ _ _ _ _ hr hy h ↦ by subst hy; obtain ⟨p', rfl, rfl⟩ := substs_eq_all_inv hr h; exact ⟨p', _, rfl, rfl, rfl⟩

theorem lib_substsInvAll : Lib substsInvAll := Lib.of_pa pa_proves_substsInvAll

/-- `subst w r = ∃ p → ∃ p', r = ∃ p' ∧ p = subst (qVec w) p'`. -/
noncomputable def substsInvExsB : ArithmeticSemisentence 5 :=
  “p y r n w. !(isSemiformula LAct).pi n r → !(substsGraph LAct) y w r → !qqExsDef y p → ∃ p' u, !qqExsDef r p' ∧ !(qVecGraph LAct) u w ∧ !(substsGraph LAct) p u p'”
noncomputable def substsInvExs : ArithmeticSentence := ∀¹* substsInvExsB

lemma models_substsInvExs :
    V↓[ℒₒᵣ] ⊧ substsInvExs ↔ ∀ p y r n w : V, IsSemiformula LAct n r → y = subst LAct w r → y = ^∃ p → ∃ p' u, r = ^∃ p' ∧ u = qVec LAct w ∧ p = subst LAct u p' := by
  simp [substsInvExs, substsInvExsB, models_iff, Matrix.vecForall_iff, subst.defined.iff, qVec.defined.iff]

theorem pa_proves_substsInvExs : 𝗣𝗔 ⊢ substsInvExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsInvExs.mpr fun _ _ _ _ _ hr hy h ↦ by subst hy; obtain ⟨p', rfl, rfl⟩ := substs_eq_exs_inv hr h; exact ⟨p', _, rfl, rfl, rfl⟩

theorem lib_substsInvExs : Lib substsInvExs := Lib.of_pa pa_proves_substsInvExs


end ArithS
