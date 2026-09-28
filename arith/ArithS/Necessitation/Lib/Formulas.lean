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
  simp [qqRelTotal, qqRelTotalB, models_iff]

theorem pa_proves_qqRelTotal : 𝗣𝗔 ⊢ qqRelTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqRelTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_qqRelTotal : Lib qqRelTotal := Lib.of_pa pa_proves_qqRelTotal

/-- `∀ k R v, ∃ p, p = nrel k R v`. -/
noncomputable def qqNRelTotalB : ArithmeticSemisentence 3 :=
  “v R k. ∃ p, !qqNRelDef p k R v”
noncomputable def qqNRelTotal : ArithmeticSentence := ∀¹* qqNRelTotalB

lemma models_qqNRelTotal :
    V↓[ℒₒᵣ] ⊧ qqNRelTotal ↔ ∀ v R k : V, ∃ p, p = ^nrel k R v := by
  simp [qqNRelTotal, qqNRelTotalB, models_iff]

theorem pa_proves_qqNRelTotal : 𝗣𝗔 ⊢ qqNRelTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqNRelTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_qqNRelTotal : Lib qqNRelTotal := Lib.of_pa pa_proves_qqNRelTotal

/-- `∃ p, p = ⊤`. -/
noncomputable def qqVerumTotalB : ArithmeticSemisentence 0 :=
  “∃ p, !qqVerumDef p”
noncomputable def qqVerumTotal : ArithmeticSentence := ∀¹* qqVerumTotalB

lemma models_qqVerumTotal :
    V↓[ℒₒᵣ] ⊧ qqVerumTotal ↔ ∃ p : V, p = ^⊤ := by
  simp [qqVerumTotal, qqVerumTotalB, models_iff]

theorem pa_proves_qqVerumTotal : 𝗣𝗔 ⊢ qqVerumTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqVerumTotal.mpr ⟨_, rfl⟩

theorem lib_qqVerumTotal : Lib qqVerumTotal := Lib.of_pa pa_proves_qqVerumTotal

/-- `∃ p, p = ⊥`. -/
noncomputable def qqFalsumTotalB : ArithmeticSemisentence 0 :=
  “∃ p, !qqFalsumDef p”
noncomputable def qqFalsumTotal : ArithmeticSentence := ∀¹* qqFalsumTotalB

lemma models_qqFalsumTotal :
    V↓[ℒₒᵣ] ⊧ qqFalsumTotal ↔ ∃ p : V, p = ^⊥ := by
  simp [qqFalsumTotal, qqFalsumTotalB, models_iff]

theorem pa_proves_qqFalsumTotal : 𝗣𝗔 ⊢ qqFalsumTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqFalsumTotal.mpr ⟨_, rfl⟩

theorem lib_qqFalsumTotal : Lib qqFalsumTotal := Lib.of_pa pa_proves_qqFalsumTotal

/-- `∀ p q, ∃ r, r = p ⋏ q`. -/
noncomputable def qqAndTotalB : ArithmeticSemisentence 2 :=
  “q p. ∃ r, !qqAndDef r p q”
noncomputable def qqAndTotal : ArithmeticSentence := ∀¹* qqAndTotalB

lemma models_qqAndTotal :
    V↓[ℒₒᵣ] ⊧ qqAndTotal ↔ ∀ q p : V, ∃ r, r = p ^⋏ q := by
  simp [qqAndTotal, qqAndTotalB, models_iff]

theorem pa_proves_qqAndTotal : 𝗣𝗔 ⊢ qqAndTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAndTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_qqAndTotal : Lib qqAndTotal := Lib.of_pa pa_proves_qqAndTotal

/-- `∀ p q, ∃ r, r = p ⋎ q`. -/
noncomputable def qqOrTotalB : ArithmeticSemisentence 2 :=
  “q p. ∃ r, !qqOrDef r p q”
noncomputable def qqOrTotal : ArithmeticSentence := ∀¹* qqOrTotalB

lemma models_qqOrTotal :
    V↓[ℒₒᵣ] ⊧ qqOrTotal ↔ ∀ q p : V, ∃ r, r = p ^⋎ q := by
  simp [qqOrTotal, qqOrTotalB, models_iff]

theorem pa_proves_qqOrTotal : 𝗣𝗔 ⊢ qqOrTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqOrTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_qqOrTotal : Lib qqOrTotal := Lib.of_pa pa_proves_qqOrTotal

/-- `∀ p, ∃ q, q = ∀ p`. -/
noncomputable def qqAllTotalB : ArithmeticSemisentence 1 :=
  “p. ∃ q, !qqAllDef q p”
noncomputable def qqAllTotal : ArithmeticSentence := ∀¹* qqAllTotalB

lemma models_qqAllTotal :
    V↓[ℒₒᵣ] ⊧ qqAllTotal ↔ ∀ p : V, ∃ q, q = ^∀ p := by
  simp [qqAllTotal, qqAllTotalB, models_iff]

theorem pa_proves_qqAllTotal : 𝗣𝗔 ⊢ qqAllTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAllTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqAllTotal : Lib qqAllTotal := Lib.of_pa pa_proves_qqAllTotal

/-- `∀ p, ∃ q, q = ∃ p`. -/
noncomputable def qqExsTotalB : ArithmeticSemisentence 1 :=
  “p. ∃ q, !qqExsDef q p”
noncomputable def qqExsTotal : ArithmeticSentence := ∀¹* qqExsTotalB

lemma models_qqExsTotal :
    V↓[ℒₒᵣ] ⊧ qqExsTotal ↔ ∀ p : V, ∃ q, q = ^∃ p := by
  simp [qqExsTotal, qqExsTotalB, models_iff]

theorem pa_proves_qqExsTotal : 𝗣𝗔 ⊢ qqExsTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqExsTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqExsTotal : Lib qqExsTotal := Lib.of_pa pa_proves_qqExsTotal

/-- `∀ k f v, ∃ t, t = func k f v`. -/
noncomputable def qqFuncTotalB : ArithmeticSemisentence 3 :=
  “v f k. ∃ t, !qqFuncDef t k f v”
noncomputable def qqFuncTotal : ArithmeticSentence := ∀¹* qqFuncTotalB

lemma models_qqFuncTotal :
    V↓[ℒₒᵣ] ⊧ qqFuncTotal ↔ ∀ v f k : V, ∃ t, t = qqFunc k f v := by
  simp [qqFuncTotal, qqFuncTotalB, models_iff]

theorem pa_proves_qqFuncTotal : 𝗣𝗔 ⊢ qqFuncTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqFuncTotal.mpr fun _ _ _ ↦ ⟨_, rfl⟩

theorem lib_qqFuncTotal : Lib qqFuncTotal := Lib.of_pa pa_proves_qqFuncTotal

/-- `∀ z, ∃ t, t = #z`. -/
noncomputable def qqBvarTotalB : ArithmeticSemisentence 1 :=
  “z. ∃ t, !qqBvarDef t z”
noncomputable def qqBvarTotal : ArithmeticSentence := ∀¹* qqBvarTotalB

lemma models_qqBvarTotal :
    V↓[ℒₒᵣ] ⊧ qqBvarTotal ↔ ∀ z : V, ∃ t, t = qqBvar z := by
  simp [qqBvarTotal, qqBvarTotalB, models_iff]

theorem pa_proves_qqBvarTotal : 𝗣𝗔 ⊢ qqBvarTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqBvarTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqBvarTotal : Lib qqBvarTotal := Lib.of_pa pa_proves_qqBvarTotal

/-- `∀ x, ∃ t, t = &x`. -/
noncomputable def qqFvarTotalB : ArithmeticSemisentence 1 :=
  “x. ∃ t, !qqFvarDef t x”
noncomputable def qqFvarTotal : ArithmeticSentence := ∀¹* qqFvarTotalB

lemma models_qqFvarTotal :
    V↓[ℒₒᵣ] ⊧ qqFvarTotal ↔ ∀ x : V, ∃ t, t = qqFvar x := by
  simp [qqFvarTotal, qqFvarTotalB, models_iff]

theorem pa_proves_qqFvarTotal : 𝗣𝗔 ⊢ qqFvarTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqFvarTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_qqFvarTotal : Lib qqFvarTotal := Lib.of_pa pa_proves_qqFvarTotal

/-- `∀ t v, ∃ w, w = t ∷ v`. -/
noncomputable def adjoinTotalB : ArithmeticSemisentence 2 :=
  “v t. ∃ w, !adjoinDef w t v”
noncomputable def adjoinTotal : ArithmeticSentence := ∀¹* adjoinTotalB

lemma models_adjoinTotal :
    V↓[ℒₒᵣ] ⊧ adjoinTotal ↔ ∀ v t : V, ∃ w, w = t ∷ v := by
  simp [adjoinTotal, adjoinTotalB, models_iff]

theorem pa_proves_adjoinTotal : 𝗣𝗔 ⊢ adjoinTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_adjoinTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_adjoinTotal : Lib adjoinTotal := Lib.of_pa pa_proves_adjoinTotal

/-- `∀ p, ∃ y, y = neg p`. -/
noncomputable def negTotalB : ArithmeticSemisentence 1 :=
  “p. ∃ y, !(negGraph LAct) y p”
noncomputable def negTotal : ArithmeticSentence := ∀¹* negTotalB

lemma models_negTotal :
    V↓[ℒₒᵣ] ⊧ negTotal ↔ ∀ p : V, ∃ y, y = neg LAct p := by
  simp [negTotal, negTotalB, models_iff, neg.defined.iff]

theorem pa_proves_negTotal : 𝗣𝗔 ⊢ negTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_negTotal : Lib negTotal := Lib.of_pa pa_proves_negTotal

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
  simp [isSemitermVecNil, isSemitermVecNilB, models_iff]

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

/-! ### Commutation: `subst` -/

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

/-! ### Commutation: `shift` -/

/-! ### Commutation: `free` -/

/-- `free (∀ p) = ∀ (subst (qVec ?[&0]) (shift p))`. -/
noncomputable def freeAllB : ArithmeticSemisentence 4 :=
  “y r p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(freeGraph LAct) y r → ∃ fz w, !qqFvarDef fz 0 ∧ !adjoinDef w fz 0 ∧ ∃ u sp sp', !(qVecGraph LAct) u w ∧ !(shiftGraph LAct) sp p ∧ !(substsGraph LAct) sp' u sp ∧ !qqAllDef y sp'”

/-! ### Shape inversion: `shift` -/

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

/-! ### Shape inversion: `subst` -/

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

end ArithS
