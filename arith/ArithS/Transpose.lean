import ArithS.TheoryAct

/-!
# ArithS.Transpose — derivations transport along language homs; τ preserves length

The renaming lemma of roadmap §2.4, on Foundation's meta calculus `Derivation2`: a language
hom `Φ` that maps the axioms of `T` into `T'` sends every `T`-derivation of `Γ` to a
`T'`-derivation of `Γ.image (lMap Φ)` (`lMapT`), node for node — so the symbol count `mlen`
is preserved whenever `lMap Φ` is injective on propositions (`mlen_lMapT`). Specialised to
`swap`, whose `lMap` is an involution, and to `TAct`, which is literally closed under `swap`
(`lMap_swap_mem_TAct`): every `TAct`-proof of `φ` has a twin proof of `swap φ` of the SAME
length (`transpose_exists`). This is the whole content of "τ-closure" for the red cell.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct

section transport

variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₂.DecidableEq] (Φ : L₁ →ᵥ L₂)
variable {T : Theory L₁} {T' : Theory L₂}

/-- Transport of a derivation along a hom that maps axioms to axioms. -/
noncomputable def lMapT (hT : ∀ σ ∈ T, Semiformula.lMap Φ σ ∈ T') :
    {Γ : Finset (Proposition L₁)} → T ⟹₂ Γ → T' ⟹₂ Γ.image (Semiformula.lMap Φ)
  | _, .closed Γ φ h hn =>
    Derivation2.closed _ (Semiformula.lMap Φ φ) (Finset.mem_image_of_mem _ h)
      (by simpa [LogicalConnective.HomClass.map_neg] using
        Finset.mem_image_of_mem (Semiformula.lMap Φ) hn)
  | _, .axm σ hT₀ hΓ =>
    Derivation2.axm (Semiformula.lMap Φ σ) (hT σ hT₀)
      (by simpa [← Semiformula.lMap_emb] using Finset.mem_image_of_mem (Semiformula.lMap Φ) hΓ)
  | _, .verum h => Derivation2.verum (by simpa using Finset.mem_image_of_mem (Semiformula.lMap Φ) h)
  | _, .and (φ := φ) (ψ := ψ) h d₁ d₂ =>
    Derivation2.and (φ := Semiformula.lMap Φ φ) (ψ := Semiformula.lMap Φ ψ)
      (by simpa using Finset.mem_image_of_mem (Semiformula.lMap Φ) h)
      ((lMapT hT d₁).cast (by simp [Finset.image_insert]))
      ((lMapT hT d₂).cast (by simp [Finset.image_insert]))
  | _, .or (φ := φ) (ψ := ψ) h d =>
    Derivation2.or (φ := Semiformula.lMap Φ φ) (ψ := Semiformula.lMap Φ ψ)
      (by simpa using Finset.mem_image_of_mem (Semiformula.lMap Φ) h)
      ((lMapT hT d).cast (by simp [Finset.image_insert]))
  | _, .all (φ := φ) h d =>
    Derivation2.all (φ := Semiformula.lMap Φ φ)
      (by simpa using Finset.mem_image_of_mem (Semiformula.lMap Φ) h)
      ((lMapT hT d).cast (by
        simp [Finset.image_insert, Finset.image_image, Function.comp_def,
          Semiformula.lMap_free, Semiformula.lMap_shift]))
  | _, .exs (φ := φ) h t d =>
    Derivation2.exs (φ := Semiformula.lMap Φ φ)
      (by simpa using Finset.mem_image_of_mem (Semiformula.lMap Φ) h)
      (Semiterm.lMap Φ t)
      ((lMapT hT d).cast (by simp [Finset.image_insert, Semiformula.lMap_subst]))
  | _, .wk d ss => Derivation2.wk (lMapT hT d) (Finset.image_subset_image ss)
  | _, .shift d =>
    (Derivation2.shift (lMapT hT d)).cast (by
      simp [Finset.image_image, Function.comp_def, Semiformula.lMap_shift])
  | _, .cut (φ := φ) d₁ d₂ =>
    Derivation2.cut (φ := Semiformula.lMap Φ φ)
      ((lMapT hT d₁).cast (by simp [Finset.image_insert]))
      ((lMapT hT d₂).cast (by simp [Finset.image_insert, LogicalConnective.HomClass.map_neg]))

end transport

/-! ### Length is preserved -/

section length

variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₁.Encodable] [L₁.LORDefinable]
  [L₂.DecidableEq] [L₂.Encodable] [L₂.LORDefinable]
variable {T : Theory L₁} [T.Δ₁] {T' : Theory L₂} [T'.Δ₁]

lemma mlen_cast {Γ Δ : Finset (Proposition L₁)} (d : T ⟹₂ Γ) (h : Γ = Δ) :
    mlen (d.cast h) = mlen d := by
  subst h; rfl

lemma sqlen_image (Φ : L₁ →ᵥ L₂)
    (hinj : Function.Injective (Semiformula.lMap Φ : Proposition L₁ → Proposition L₂))
    (Γ : Finset (Proposition L₁)) :
    sqlen (Γ.image (Semiformula.lMap Φ)) = sqlen Γ := by
  unfold sqlen
  rw [Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
  exact Finset.sum_congr rfl (fun φ _ ↦ flen_lMap Φ φ)

/-- The transported derivation has the same symbol count. -/
theorem mlen_lMapT (Φ : L₁ →ᵥ L₂) (hT : ∀ σ ∈ T, Semiformula.lMap Φ σ ∈ T')
    (hinj : Function.Injective (Semiformula.lMap Φ : Proposition L₁ → Proposition L₂))
    {Γ : Finset (Proposition L₁)} (d : T ⟹₂ Γ) :
    mlen (lMapT Φ hT d) = mlen d := by
  induction d with
  | closed Γ φ h hn => simp [lMapT, mlen, sqlen_image Φ hinj]
  | axm σ hT₀ hΓ => simp [lMapT, mlen, sqlen_image Φ hinj]
  | verum h => simp [lMapT, mlen, sqlen_image Φ hinj]
  | and h d₁ d₂ ih₁ ih₂ => simp [lMapT, mlen, mlen_cast, sqlen_image Φ hinj, ih₁, ih₂]
  | or h d ih => simp [lMapT, mlen, mlen_cast, sqlen_image Φ hinj, ih]
  | all h d ih => simp [lMapT, mlen, mlen_cast, sqlen_image Φ hinj, ih]
  | exs h t d ih => simp [lMapT, mlen, mlen_cast, sqlen_image Φ hinj, ih, tlen_lMap]
  | wk d ss ih => simp [lMapT, mlen, sqlen_image Φ hinj, ih]
  | @shift Γ d ih =>
    have e : Finset.image Rewriting.shift (Finset.image (Semiformula.lMap Φ) Γ) =
        Finset.image (Semiformula.lMap Φ) (Finset.image Rewriting.shift Γ) := by
      simp [Finset.image_image, Function.comp_def, Semiformula.lMap_shift]
    simp [lMapT, mlen, mlen_cast, ih, e, sqlen_image Φ hinj]
  | cut d₁ d₂ ih₁ ih₂ => simp [lMapT, mlen, mlen_cast, sqlen_image Φ hinj, ih₁, ih₂]

end length

/-! ### The swap is an involution, hence injective -/

section swap

lemma term_lMap_swap_swap {n : ℕ} {ξ : Type*} (t : Semiterm LAct ξ n) :
    Semiterm.lMap swap (Semiterm.lMap swap t) = t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => simp [Semiterm.lMap_func, Function.comp_def, ih, swap_swap_func]

lemma lMap_swap_swap {n : ℕ} {ξ : Type*} (φ : Semiformula LAct ξ n) :
    Semiformula.lMap swap (Semiformula.lMap swap φ) = φ := by
  induction φ with
  | rel R v => simp [Semiformula.lMap_rel, Function.comp_def, term_lMap_swap_swap]
  | nrel R v => simp [Semiformula.lMap_nrel, Function.comp_def, term_lMap_swap_swap]
  | verum =>
    change Semiformula.lMap swap (Semiformula.lMap swap ⊤) = ⊤
    simp
  | falsum =>
    change Semiformula.lMap swap (Semiformula.lMap swap ⊥) = ⊥
    simp
  | and φ ψ ihφ ihψ =>
    change Semiformula.lMap swap (Semiformula.lMap swap (φ ⋏ ψ)) = φ ⋏ ψ
    simp [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change Semiformula.lMap swap (Semiformula.lMap swap (φ ⋎ ψ)) = φ ⋎ ψ
    simp [ihφ, ihψ]
  | all φ ih =>
    change Semiformula.lMap swap (Semiformula.lMap swap (∀¹ φ)) = ∀¹ φ
    simp [ih]
  | exs φ ih =>
    change Semiformula.lMap swap (Semiformula.lMap swap (∃¹ φ)) = ∃¹ φ
    simp [ih]

lemma lMap_swap_injective {n : ℕ} {ξ : Type*} :
    Function.Injective (Semiformula.lMap swap : Semiformula LAct ξ n → Semiformula LAct ξ n) :=
  fun φ ψ h ↦ by simpa [lMap_swap_swap] using congrArg (Semiformula.lMap swap) h

/-- **τ-closure of `TAct`, meta form**: every `TAct`-proof of `φ` has a twin proof of
`swap φ` of exactly the same length. -/
theorem transpose_exists (φ : Proposition LAct) (d : TAct ⟹₂ {φ}) :
    ∃ d' : TAct ⟹₂ {Semiformula.lMap swap φ}, mlen d' = mlen d :=
  ⟨(lMapT swap (fun _ h ↦ lMap_swap_mem_TAct h) d).cast (by simp),
    by rw [mlen_cast, mlen_lMapT swap (fun _ h ↦ lMap_swap_mem_TAct h) lMap_swap_injective]⟩

end swap

end ArithS
