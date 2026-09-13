import ArithS.Necessitation.Describe
import ArithS.Necessitation.NumSteps
import ArithS.Necessitation.RowInstB

/-!
# ArithS.Necessitation.Cert — certified re-description (`neg`/`shift`/`eq`) and length steps

`M4_BOUNDED_HBL/DESIGN_fragments.md` §3.6. Part 0 — the DOSSIER of a code in a context: the
facts the walk (`Describe.lean`) leaves for a code, read off the walk's own final context from the
EMPTY context, transported to any offset `i` by `shiftIterV` (`DossF W Γ n r i` := every fact of
`finalCtx 0 (describeF W n r)` sits in `Γ` shifted by `i`, so the top of `r` is `&i` and every
descendant at its walk offset above `i`); the same for terms (`DossT`) and for the last `j` entries
of a vector (`DossV`). A freshly walked code has its dossier at offset `0`
(`dossF_of_walk`), a dossier survives a `NoDrop` list shifted by its eigenvariable count
(`dossF_transport`), and the per-constructor DECOMPOSITION lemmas read the shape facts and the
children's dossiers off a parent's (`dossF_and`, `dossF_all`, `dossF_rel`, `dossT_bvar`, …).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## Part 0 — dossiers -/

section dossier

/-- A non-dropping step is monotone in its context. -/
lemma ctxAfter_mono {Γ Γ' s : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4)
    (hsub : Γ ⊆ Γ') : ctxAfter Γ s ⊆ ctxAfter Γ' s := by
  intro x hx
  rcases h with h | h | h | h | h
  · rw [ctxAfter_tag0 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · exact mem_bitInsert_iff.mpr (Or.inr (hsub hx))
  · rw [ctxAfter_tag1 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · rcases mem_bitInsert_iff.mp hx with rfl | hx
      · simp
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (hsub hx))))
  · rw [ctxAfter_tag2 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
      exact mem_bitInsert_iff.mpr (Or.inr (mem_setShift_iff.mpr ⟨y, hsub hy, rfl⟩))
  · rw [ctxAfter_tag3 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
      exact mem_bitInsert_iff.mpr (Or.inr (mem_setShift_iff.mpr ⟨y, hsub hy, rfl⟩))
  · rw [ctxAfter_tag4 h] at hx ⊢
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · rcases mem_bitInsert_iff.mp hx with rfl | hx
      · simp
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (hsub hx))))

/-- The context vector of a non-dropping list is monotone in the initial context. -/
lemma ctxVec_mono {Γ Γ' S : V} (hS : NoDrop S) (hsub : Γ ⊆ Γ') :
    ∀ j ≤ len S, (ctxVec Γ S).[j] ⊆ (ctxVec Γ' S).[j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simpa using hsub
  | succ j ih =>
    intro hj
    have hj' : j < len S := lt_of_lt_of_le (lt_add_one j) hj
    rw [nth_ctxVec_succ Γ S hj', nth_ctxVec_succ Γ' S hj']
    exact ctxAfter_mono (hS j hj') (ih (le_of_lt hj'))

lemma finalCtx_mono {Γ Γ' S : V} (hS : NoDrop S) (hsub : Γ ⊆ Γ') : finalCtx Γ S ⊆ finalCtx Γ' S :=
  ctxVec_mono hS hsub (len S) le_rfl

/-- **The dossier of a formula code at offset `i`**: every fact the walk leaves from the empty
context sits in `Γ`, shifted `i` times (top at `&i`, descendants at their walk offsets above `i`). -/
def DossF (W Γ n r i : V) : Prop := ∀ f ∈ finalCtx 0 (describeF W n r), shiftIterV f i ∈ Γ
/-- The dossier of a term code at offset `i`. -/
def DossT (W Γ n t i : V) : Prop := ∀ f ∈ finalCtx 0 (describeT W n t), shiftIterV f i ∈ Γ
/-- The dossier of the walk of the last `j` entries of the vector `v` (of length `k`) at offset `i`. -/
def DossV (W Γ n k v j i : V) : Prop :=
  ∀ f ∈ finalCtx 0 (π₂ (descVecAux W n (descTVec W n k v) j)), shiftIterV f i ∈ Γ

instance dossF_definable : 𝚫₁-Relation₅ (DossF : V → V → V → V → V → Prop) := by
  unfold DossF; definability
instance dossT_definable : 𝚫₁-Relation₅ (DossT : V → V → V → V → V → Prop) := by
  unfold DossT; definability
instance dossV_definable : 𝚫₁.Definable (fun v : Fin 7 → V ↦ DossV (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold DossV; definability

/-- A dossier survives a non-dropping list, moved up by its eigenvariable count. -/
lemma dossF_transport {W Γ n r i S : V} (hS : NoDrop S) (h : DossF W Γ n r i) :
    DossF W (finalCtx Γ S) n r (i + shiftsV S) := by
  intro f hf
  rw [shiftIterV_add]
  exact mem_finalCtx_of_mem hS (h f hf)
lemma dossT_transport {W Γ n t i S : V} (hS : NoDrop S) (h : DossT W Γ n t i) :
    DossT W (finalCtx Γ S) n t (i + shiftsV S) := by
  intro f hf
  rw [shiftIterV_add]
  exact mem_finalCtx_of_mem hS (h f hf)
lemma dossV_transport {W Γ n k v j i S : V} (hS : NoDrop S) (h : DossV W Γ n k v j i) :
    DossV W (finalCtx Γ S) n k v j (i + shiftsV S) := by
  intro f hf
  rw [shiftIterV_add]
  exact mem_finalCtx_of_mem hS (h f hf)

/-- A dossier is stable under growing the context. -/
lemma DossF.mono {W Γ Γ' n r i : V} (h : DossF W Γ n r i) (hsub : Γ ⊆ Γ') : DossF W Γ' n r i :=
  fun f hf ↦ hsub (h f hf)
lemma DossT.mono {W Γ Γ' n t i : V} (h : DossT W Γ n t i) (hsub : Γ ⊆ Γ') : DossT W Γ' n t i :=
  fun f hf ↦ hsub (h f hf)
lemma DossV.mono {W Γ Γ' n k v j i : V} (h : DossV W Γ n k v j i) (hsub : Γ ⊆ Γ') : DossV W Γ' n k v j i :=
  fun f hf ↦ hsub (h f hf)

/-- A freshly walked formula has its dossier at offset `0` (for a non-dropping walk). -/
lemma dossF_of_walk {W Γ n r : V} (hnd : NoDrop (describeF W n r)) :
    DossF W (finalCtx Γ (describeF W n r)) n r 0 := by
  intro f hf
  rw [shiftIterV_zero]
  exact finalCtx_mono hnd (fun x hx ↦ by simp at hx) hf
lemma dossT_of_walk {W Γ n t : V} (hnd : NoDrop (describeT W n t)) :
    DossT W (finalCtx Γ (describeT W n t)) n t 0 := by
  intro f hf
  rw [shiftIterV_zero]
  exact finalCtx_mono hnd (fun x hx ↦ by simp at hx) hf

end dossier

/-! ### 0.2 Iterated shifts of the facts (`shiftIterV_<fact>`, the `shiftIterV_piFact` pattern) -/

section factIter

lemma shiftIterV_sigmaFact {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) :
    ∀ m, shiftIterV (sigmaFact n a) m = sigmaFact (termShiftIterV n m) (termShiftIterV a m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_sigmaFact (isSemiterm_termShiftIterV hn m) (isSemiterm_termShiftIterV ha m), termShiftIterV_succ, termShiftIterV_succ]

instance andFact_definable : 𝚺₁-Function₃ (andFact : V → V → V → V) := by
  have : (andFact : V → V → V → V) = fun z a b ↦ subst LAct (z ∷ a ∷ b ∷ 0) Pand := rfl
  rw [this]; definability
lemma shiftIterV_andFact {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ m, shiftIterV (andFact z a b) m = andFact (termShiftIterV z m) (termShiftIterV a m) (termShiftIterV b m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_andFact (isSemiterm_termShiftIterV hz m) (isSemiterm_termShiftIterV ha m) (isSemiterm_termShiftIterV hb m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance orFact_definable : 𝚺₁-Function₃ (orFact : V → V → V → V) := by
  have : (orFact : V → V → V → V) = fun z a b ↦ subst LAct (z ∷ a ∷ b ∷ 0) Por := rfl
  rw [this]; definability
lemma shiftIterV_orFact {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ m, shiftIterV (orFact z a b) m = orFact (termShiftIterV z m) (termShiftIterV a m) (termShiftIterV b m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_orFact (isSemiterm_termShiftIterV hz m) (isSemiterm_termShiftIterV ha m) (isSemiterm_termShiftIterV hb m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance allFact_definable : 𝚺₁-Function₂ (allFact : V → V → V) := by
  have : (allFact : V → V → V) = fun q p ↦ subst LAct (q ∷ p ∷ 0) Pall := rfl
  rw [this]; definability
lemma shiftIterV_allFact {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (allFact q p) m = allFact (termShiftIterV q m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_allFact (isSemiterm_termShiftIterV hq m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ]

instance exsFact_definable : 𝚺₁-Function₂ (exsFact : V → V → V) := by
  have : (exsFact : V → V → V) = fun q p ↦ subst LAct (q ∷ p ∷ 0) Pexs := rfl
  rw [this]; definability
lemma shiftIterV_exsFact {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (exsFact q p) m = exsFact (termShiftIterV q m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_exsFact (isSemiterm_termShiftIterV hq m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ]

instance relFact_definable : 𝚺₁-Function₄ (relFact : V → V → V → V → V) := by
  have : (relFact : V → V → V → V → V) = fun p k R v ↦ subst LAct (p ∷ k ∷ R ∷ v ∷ 0) Prel := rfl
  rw [this]; definability
lemma shiftIterV_relFact {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (relFact p k R v) m = relFact (termShiftIterV p m) (termShiftIterV k m) (termShiftIterV R m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_relFact (isSemiterm_termShiftIterV hp m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hR m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance nrelFact_definable : 𝚺₁-Function₄ (nrelFact : V → V → V → V → V) := by
  have : (nrelFact : V → V → V → V → V) = fun p k R v ↦ subst LAct (p ∷ k ∷ R ∷ v ∷ 0) Pnrel := rfl
  rw [this]; definability
lemma shiftIterV_nrelFact {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (nrelFact p k R v) m = nrelFact (termShiftIterV p m) (termShiftIterV k m) (termShiftIterV R m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_nrelFact (isSemiterm_termShiftIterV hp m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hR m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance verumFact_definable : 𝚺₁-Function₁ (verumFact : V → V) := by
  have : (verumFact : V → V) = fun p ↦ subst LAct (p ∷ 0) Pverum := rfl
  rw [this]; definability
lemma shiftIterV_verumFact {p : V} (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (verumFact p) m = verumFact (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_verumFact (isSemiterm_termShiftIterV hp m), termShiftIterV_succ]

instance falsumFact_definable : 𝚺₁-Function₁ (falsumFact : V → V) := by
  have : (falsumFact : V → V) = fun p ↦ subst LAct (p ∷ 0) Pfalsum := rfl
  rw [this]; definability
lemma shiftIterV_falsumFact {p : V} (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (falsumFact p) m = falsumFact (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_falsumFact (isSemiterm_termShiftIterV hp m), termShiftIterV_succ]

instance funcFact_definable : 𝚺₁-Function₄ (funcFact : V → V → V → V → V) := by
  have : (funcFact : V → V → V → V → V) = fun t k f v ↦ subst LAct (t ∷ k ∷ f ∷ v ∷ 0) Pfunc := rfl
  rw [this]; definability
lemma shiftIterV_funcFact {t k f v : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (funcFact t k f v) m = funcFact (termShiftIterV t m) (termShiftIterV k m) (termShiftIterV f m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_funcFact (isSemiterm_termShiftIterV ht m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hf m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_bvarFact {t z : V} (ht : IsSemiterm LAct 0 t) (hz : IsSemiterm LAct 0 z) :
    ∀ m, shiftIterV (bvarFact t z) m = bvarFact (termShiftIterV t m) (termShiftIterV z m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_bvarFact (isSemiterm_termShiftIterV ht m) (isSemiterm_termShiftIterV hz m), termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_fvarFact {t x : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) :
    ∀ m, shiftIterV (fvarFact t x) m = fvarFact (termShiftIterV t m) (termShiftIterV x m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_fvarFact (isSemiterm_termShiftIterV ht m) (isSemiterm_termShiftIterV hx m), termShiftIterV_succ, termShiftIterV_succ]

instance adjFact_definable : 𝚺₁-Function₃ (adjFact : V → V → V → V) := by
  have : (adjFact : V → V → V → V) = fun w t v ↦ subst LAct (w ∷ t ∷ v ∷ 0) Padjoin := rfl
  rw [this]; definability
lemma shiftIterV_adjFact {w t v : V} (hw : IsSemiterm LAct 0 w) (ht : IsSemiterm LAct 0 t) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (adjFact w t v) m = adjFact (termShiftIterV w m) (termShiftIterV t m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_adjFact (isSemiterm_termShiftIterV hw m) (isSemiterm_termShiftIterV ht m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_tSigmaFact {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) :
    ∀ m, shiftIterV (tSigmaFact n t) m = tSigmaFact (termShiftIterV n m) (termShiftIterV t m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tSigmaFact (isSemiterm_termShiftIterV hn m) (isSemiterm_termShiftIterV ht m), termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_tvSigmaFact {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (tvSigmaFact k n v) m = tvSigmaFact (termShiftIterV k m) (termShiftIterV n m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tvSigmaFact (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hn m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance utvPiFact_definable : 𝚺₁-Function₂ (utvPiFact : V → V → V) := by
  have : (utvPiFact : V → V → V) = fun k v ↦ subst LAct (k ∷ v ∷ 0) PutvPi := rfl
  rw [this]; definability
lemma shiftIterV_utvPiFact {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (utvPiFact k v) m = utvPiFact (termShiftIterV k m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_utvPiFact (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ]

instance utvSigmaFact_definable : 𝚺₁-Function₂ (utvSigmaFact : V → V → V) := by
  have : (utvSigmaFact : V → V → V) = fun k v ↦ subst LAct (k ∷ v ∷ 0) PutvSigma := rfl
  rw [this]; definability
lemma shiftIterV_utvSigmaFact {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (utvSigmaFact k v) m = utvSigmaFact (termShiftIterV k m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_utvSigmaFact (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ]

instance isRelFact_definable : 𝚺₁-Function₂ (isRelFact : V → V → V) := by
  have : (isRelFact : V → V → V) = fun k R ↦ subst LAct (k ∷ R ∷ 0) PisRel := rfl
  rw [this]; definability
lemma shiftIterV_isRelFact {k R : V} (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) :
    ∀ m, shiftIterV (isRelFact k R) m = isRelFact (termShiftIterV k m) (termShiftIterV R m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_isRelFact (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hR m), termShiftIterV_succ, termShiftIterV_succ]

instance isFuncFact_definable : 𝚺₁-Function₂ (isFuncFact : V → V → V) := by
  have : (isFuncFact : V → V → V) = fun k f ↦ subst LAct (k ∷ f ∷ 0) PisFunc := rfl
  rw [this]; definability
lemma shiftIterV_isFuncFact {k f : V} (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) :
    ∀ m, shiftIterV (isFuncFact k f) m = isFuncFact (termShiftIterV k m) (termShiftIterV f m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_isFuncFact (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hf m), termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_ltFact {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ m, shiftIterV (ltFact a b) m = ltFact (termShiftIterV a m) (termShiftIterV b m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_ltFact (isSemiterm_termShiftIterV ha m) (isSemiterm_termShiftIterV hb m), termShiftIterV_succ, termShiftIterV_succ]

instance negFact_definable : 𝚺₁-Function₂ (negFact : V → V → V) := by
  have : (negFact : V → V → V) = fun y p ↦ subst LAct (y ∷ p ∷ 0) PnegG := rfl
  rw [this]; definability
lemma shiftIterV_negFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (negFact y p) m = negFact (termShiftIterV y m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_negFact (isSemiterm_termShiftIterV hy m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ]

instance shiftFact_definable : 𝚺₁-Function₂ (shiftFact : V → V → V) := by
  have : (shiftFact : V → V → V) = fun y p ↦ subst LAct (y ∷ p ∷ 0) PshiftG := rfl
  rw [this]; definability
lemma shiftIterV_shiftFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (shiftFact y p) m = shiftFact (termShiftIterV y m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_shiftFact (isSemiterm_termShiftIterV hy m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ]

instance substFact_definable : 𝚺₁-Function₃ (substFact : V → V → V → V) := by
  have : (substFact : V → V → V → V) = fun y w p ↦ subst LAct (y ∷ w ∷ p ∷ 0) PsubstsG := rfl
  rw [this]; definability
lemma shiftIterV_substFact {y w p : V} (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (substFact y w p) m = substFact (termShiftIterV y m) (termShiftIterV w m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_substFact (isSemiterm_termShiftIterV hy m) (isSemiterm_termShiftIterV hw m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance substs1Fact_definable : 𝚺₁-Function₃ (substs1Fact : V → V → V → V) := by
  have : (substs1Fact : V → V → V → V) = fun y t p ↦ subst LAct (y ∷ t ∷ p ∷ 0) Psubsts1G := rfl
  rw [this]; definability
lemma shiftIterV_substs1Fact {y t p : V} (hy : IsSemiterm LAct 0 y) (ht : IsSemiterm LAct 0 t) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (substs1Fact y t p) m = substs1Fact (termShiftIterV y m) (termShiftIterV t m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_substs1Fact (isSemiterm_termShiftIterV hy m) (isSemiterm_termShiftIterV ht m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance freeFact_definable : 𝚺₁-Function₂ (freeFact : V → V → V) := by
  have : (freeFact : V → V → V) = fun y p ↦ subst LAct (y ∷ p ∷ 0) PfreeG := rfl
  rw [this]; definability
lemma shiftIterV_freeFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (freeFact y p) m = freeFact (termShiftIterV y m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_freeFact (isSemiterm_termShiftIterV hy m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ]

instance qVecFact_definable : 𝚺₁-Function₂ (qVecFact : V → V → V) := by
  have : (qVecFact : V → V → V) = fun u w ↦ subst LAct (u ∷ w ∷ 0) PqVecG := rfl
  rw [this]; definability
lemma shiftIterV_qVecFact {u w : V} (hu : IsSemiterm LAct 0 u) (hw : IsSemiterm LAct 0 w) :
    ∀ m, shiftIterV (qVecFact u w) m = qVecFact (termShiftIterV u m) (termShiftIterV w m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_qVecFact (isSemiterm_termShiftIterV hu m) (isSemiterm_termShiftIterV hw m), termShiftIterV_succ, termShiftIterV_succ]

instance tsvFact_definable : 𝚺₁-Function₄ (tsvFact : V → V → V → V → V) := by
  have : (tsvFact : V → V → V → V → V) = fun u k w v ↦ subst LAct (u ∷ k ∷ w ∷ v ∷ 0) PtsvG := rfl
  rw [this]; definability
lemma shiftIterV_tsvFact {u k w v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hw : IsSemiterm LAct 0 w) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (tsvFact u k w v) m = tsvFact (termShiftIterV u m) (termShiftIterV k m) (termShiftIterV w m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tsvFact (isSemiterm_termShiftIterV hu m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hw m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance tshvFact_definable : 𝚺₁-Function₃ (tshvFact : V → V → V → V) := by
  have : (tshvFact : V → V → V → V) = fun u k v ↦ subst LAct (u ∷ k ∷ v ∷ 0) PtshvG := rfl
  rw [this]; definability
lemma shiftIterV_tshvFact {u k v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (tshvFact u k v) m = tshvFact (termShiftIterV u m) (termShiftIterV k m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tshvFact (isSemiterm_termShiftIterV hu m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance eqFactB_definable : 𝚺₁-Function₂ (eqFactB : V → V → V) := by
  have : (eqFactB : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) PeqB := rfl
  rw [this]; definability
lemma shiftIterV_eqFactB {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ m, shiftIterV (eqFactB a b) m = eqFactB (termShiftIterV a m) (termShiftIterV b m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_eqFactB (isSemiterm_termShiftIterV ha m) (isSemiterm_termShiftIterV hb m), termShiftIterV_succ, termShiftIterV_succ]

instance lenFact_definable : 𝚺₁-Function₂ (lenFact : V → V → V) := by
  have : (lenFact : V → V → V) = fun l p ↦ subst LAct (l ∷ p ∷ 0) PflenG := rfl
  rw [this]; definability
lemma shiftIterV_lenFact {l p : V} (hl : IsSemiterm LAct 0 l) (hp : IsSemiterm LAct 0 p) :
    ∀ m, shiftIterV (lenFact l p) m = lenFact (termShiftIterV l m) (termShiftIterV p m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_lenFact (isSemiterm_termShiftIterV hl m) (isSemiterm_termShiftIterV hp m), termShiftIterV_succ, termShiftIterV_succ]

instance tlenFact_definable : 𝚺₁-Function₂ (tlenFact : V → V → V) := by
  have : (tlenFact : V → V → V) = fun l t ↦ subst LAct (l ∷ t ∷ 0) PtlenG := rfl
  rw [this]; definability
lemma shiftIterV_tlenFact {l t : V} (hl : IsSemiterm LAct 0 l) (ht : IsSemiterm LAct 0 t) :
    ∀ m, shiftIterV (tlenFact l t) m = tlenFact (termShiftIterV l m) (termShiftIterV t m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tlenFact (isSemiterm_termShiftIterV hl m) (isSemiterm_termShiftIterV ht m), termShiftIterV_succ, termShiftIterV_succ]

instance tlvFact_definable : 𝚺₁-Function₃ (tlvFact : V → V → V → V) := by
  have : (tlvFact : V → V → V → V) = fun M k v ↦ subst LAct (M ∷ k ∷ v ∷ 0) PtlvG := rfl
  rw [this]; definability
lemma shiftIterV_tlvFact {M k v : V} (hM : IsSemiterm LAct 0 M) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (tlvFact M k v) m = tlvFact (termShiftIterV M m) (termShiftIterV k m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tlvFact (isSemiterm_termShiftIterV hM m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance listSumFact_definable : 𝚺₁-Function₂ (listSumFact : V → V → V) := by
  have : (listSumFact : V → V → V) = fun s M ↦ subst LAct (s ∷ M ∷ 0) PlistSum := rfl
  rw [this]; definability
lemma shiftIterV_listSumFact {s M : V} (hs : IsSemiterm LAct 0 s) (hM : IsSemiterm LAct 0 M) :
    ∀ m, shiftIterV (listSumFact s M) m = listSumFact (termShiftIterV s m) (termShiftIterV M m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_listSumFact (isSemiterm_termShiftIterV hs m) (isSemiterm_termShiftIterV hM m), termShiftIterV_succ, termShiftIterV_succ]

instance nthFact_definable : 𝚺₁-Function₃ (nthFact : V → V → V → V) := by
  have : (nthFact : V → V → V → V) = fun e w i ↦ subst LAct (e ∷ w ∷ i ∷ 0) Pnth := rfl
  rw [this]; definability
lemma shiftIterV_nthFact {e w i : V} (he : IsSemiterm LAct 0 e) (hw : IsSemiterm LAct 0 w) (hi : IsSemiterm LAct 0 i) :
    ∀ m, shiftIterV (nthFact e w i) m = nthFact (termShiftIterV e m) (termShiftIterV w m) (termShiftIterV i m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_nthFact (isSemiterm_termShiftIterV he m) (isSemiterm_termShiftIterV hw m) (isSemiterm_termShiftIterV hi m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance tshFact_definable : 𝚺₁-Function₂ (tshFact : V → V → V) := by
  have : (tshFact : V → V → V) = fun t2 t ↦ subst LAct (t2 ∷ t ∷ 0) PtshG := rfl
  rw [this]; definability
lemma shiftIterV_tshFact {t2 t : V} (ht2 : IsSemiterm LAct 0 t2) (ht : IsSemiterm LAct 0 t) :
    ∀ m, shiftIterV (tshFact t2 t) m = tshFact (termShiftIterV t2 m) (termShiftIterV t m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tshFact (isSemiterm_termShiftIterV ht2 m) (isSemiterm_termShiftIterV ht m), termShiftIterV_succ, termShiftIterV_succ]

instance tsFact_definable : 𝚺₁-Function₃ (tsFact : V → V → V → V) := by
  have : (tsFact : V → V → V → V) = fun e w t ↦ subst LAct (e ∷ w ∷ t ∷ 0) PtsG := rfl
  rw [this]; definability
lemma shiftIterV_tsFact {e w t : V} (he : IsSemiterm LAct 0 e) (hw : IsSemiterm LAct 0 w) (ht : IsSemiterm LAct 0 t) :
    ∀ m, shiftIterV (tsFact e w t) m = tsFact (termShiftIterV e m) (termShiftIterV w m) (termShiftIterV t m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tsFact (isSemiterm_termShiftIterV he m) (isSemiterm_termShiftIterV hw m) (isSemiterm_termShiftIterV ht m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

instance tbshFact_definable : 𝚺₁-Function₂ (tbshFact : V → V → V) := by
  have : (tbshFact : V → V → V) = fun e2 e ↦ subst LAct (e2 ∷ e ∷ 0) PtbshG := rfl
  rw [this]; definability
lemma shiftIterV_tbshFact {e2 e : V} (he2 : IsSemiterm LAct 0 e2) (he : IsSemiterm LAct 0 e) :
    ∀ m, shiftIterV (tbshFact e2 e) m = tbshFact (termShiftIterV e2 m) (termShiftIterV e m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tbshFact (isSemiterm_termShiftIterV he2 m) (isSemiterm_termShiftIterV he m), termShiftIterV_succ, termShiftIterV_succ]

instance tbshvFact_definable : 𝚺₁-Function₃ (tbshvFact : V → V → V → V) := by
  have : (tbshvFact : V → V → V → V) = fun u k v ↦ subst LAct (u ∷ k ∷ v ∷ 0) PtbshvG := rfl
  rw [this]; definability
lemma shiftIterV_tbshvFact {u k v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    ∀ m, shiftIterV (tbshvFact u k v) m = tbshvFact (termShiftIterV u m) (termShiftIterV k m) (termShiftIterV v m) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ m ih =>
    rw [shiftIterV_succ, ih, shift_tbshvFact (isSemiterm_termShiftIterV hu m) (isSemiterm_termShiftIterV hk m) (isSemiterm_termShiftIterV hv m), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

end factIter

/-! ### 0.3 The context after one walk step, as a pure computation (no applicability needed) -/

section ctxSteps

variable {W : V} (hWp : W = walkPieces)
include hWp

lemma ctx_qqBvarTotal {Γ wz : V} (hwz : IsSemiterm LAct 0 wz) :
    ctxAfter Γ (mkStep W 2 ?[wz]) = insert (neg LAct (bvarFact (^&0) (termShift LAct wz))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqBvarTotal : ℕ) : V) = (2 : V) := by simp [rIdx_qqBvarTotal]
  have hstep := mkStep_qqBvarTotal (V := V) ?[wz]
  rw [hk] at hstep
  rw [hstep, show (?[wz] : V) = vecOf [wz] from rfl,
    ctxAfter_introFact [wz] row_qqBvarTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqBvarTotal_R)
      (List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_nil _⟩),
    show row_qqBvarTotal_R = row_qqBvarTotal_body from rfl, ← freeIter_one, (inst_qqBvarTotal hwz).2]
  simp

lemma ctx_qqFvarTotal {Γ wx : V} (hwx : IsSemiterm LAct 0 wx) :
    ctxAfter Γ (mkStep W 5 ?[wx]) = insert (neg LAct (fvarFact (^&0) (termShift LAct wx))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqFvarTotal : ℕ) : V) = (5 : V) := by simp [rIdx_qqFvarTotal]
  have hstep := mkStep_qqFvarTotal (V := V) ?[wx]
  rw [hk] at hstep
  rw [hstep, show (?[wx] : V) = vecOf [wx] from rfl,
    ctxAfter_introFact [wx] row_qqFvarTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqFvarTotal_R)
      (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩),
    show row_qqFvarTotal_R = row_qqFvarTotal_body from rfl, ← freeIter_one, (inst_qqFvarTotal hwx).2]
  simp

lemma ctx_qqFuncTotal {Γ wk wf wv : V} (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) :
    ctxAfter Γ (mkStep W 7 ?[wk, wf, wv]) =
      insert (neg LAct (funcFact (^&0) (termShift LAct wk) (termShift LAct wf) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqFuncTotal : ℕ) : V) = (7 : V) := by simp [rIdx_qqFuncTotal]
  have hstep := mkStep_qqFuncTotal (V := V) ?[wk, wf, wv]
  rw [hk] at hstep
  rw [hstep, show (?[wk, wf, wv] : V) = vecOf [wk, wf, wv] from rfl,
    ctxAfter_introFact [wk, wf, wv] row_qqFuncTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqFuncTotal_R)
      (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩),
    show row_qqFuncTotal_R = row_qqFuncTotal_body from rfl, ← freeIter_one, (inst_qqFuncTotal hwk hwf hwv).2]
  simp

lemma ctx_adjoinTotal {Γ wt wv : V} (hwt : IsSemiterm LAct 0 wt) (hwv : IsSemiterm LAct 0 wv) :
    ctxAfter Γ (mkStep W 17 ?[wt, wv]) =
      insert (neg LAct (adjFact (^&0) (termShift LAct wt) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_adjoinTotal : ℕ) : V) = (17 : V) := by simp [rIdx_adjoinTotal]
  have hstep := mkStep_adjoinTotal (V := V) ?[wt, wv]
  rw [hk] at hstep
  rw [hstep, show (?[wt, wv] : V) = vecOf [wt, wv] from rfl,
    ctxAfter_introFact [wt, wv] row_adjoinTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_adjoinTotal_R)
      (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩),
    show row_adjoinTotal_R = row_adjoinTotal_body from rfl, ← freeIter_one, (inst_adjoinTotal hwt hwv).2]
  simp

lemma ctx_qqVerumTotal {Γ : V} :
    ctxAfter Γ (mkStep W 19 0) = insert (neg LAct (verumFact (^&0))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqVerumTotal : ℕ) : V) = (19 : V) := by simp [rIdx_qqVerumTotal]
  have hstep := mkStep_qqVerumTotal (V := V) 0
  rw [hk] at hstep
  rw [hstep, show (0 : V) = vecOf [] from rfl,
    ctxAfter_introFact [] row_qqVerumTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqVerumTotal_R)
      (List.forall_mem_nil _),
    show row_qqVerumTotal_R = row_qqVerumTotal_body from rfl, ← freeIter_one, (inst_qqVerumTotal (V := V)).2]
  simp

lemma ctx_qqFalsumTotal {Γ : V} :
    ctxAfter Γ (mkStep W 22 0) = insert (neg LAct (falsumFact (^&0))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqFalsumTotal : ℕ) : V) = (22 : V) := by simp [rIdx_qqFalsumTotal]
  have hstep := mkStep_qqFalsumTotal (V := V) 0
  rw [hk] at hstep
  rw [hstep, show (0 : V) = vecOf [] from rfl,
    ctxAfter_introFact [] row_qqFalsumTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqFalsumTotal_R)
      (List.forall_mem_nil _),
    show row_qqFalsumTotal_R = row_qqFalsumTotal_body from rfl, ← freeIter_one, (inst_qqFalsumTotal (V := V)).2]
  simp

lemma ctx_qqAndTotal {Γ wp wq : V} (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) :
    ctxAfter Γ (mkStep W 24 ?[wp, wq]) =
      insert (neg LAct (andFact (^&0) (termShift LAct wp) (termShift LAct wq))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqAndTotal : ℕ) : V) = (24 : V) := by simp [rIdx_qqAndTotal]
  have hstep := mkStep_qqAndTotal (V := V) ?[wp, wq]
  rw [hk] at hstep
  rw [hstep, show (?[wp, wq] : V) = vecOf [wp, wq] from rfl,
    ctxAfter_introFact [wp, wq] row_qqAndTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqAndTotal_R)
      (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_nil _⟩⟩),
    show row_qqAndTotal_R = row_qqAndTotal_body from rfl, ← freeIter_one, (inst_qqAndTotal hwp hwq).2]
  simp

lemma ctx_qqOrTotal {Γ wp wq : V} (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) :
    ctxAfter Γ (mkStep W 26 ?[wp, wq]) =
      insert (neg LAct (orFact (^&0) (termShift LAct wp) (termShift LAct wq))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqOrTotal : ℕ) : V) = (26 : V) := by simp [rIdx_qqOrTotal]
  have hstep := mkStep_qqOrTotal (V := V) ?[wp, wq]
  rw [hk] at hstep
  rw [hstep, show (?[wp, wq] : V) = vecOf [wp, wq] from rfl,
    ctxAfter_introFact [wp, wq] row_qqOrTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqOrTotal_R)
      (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_nil _⟩⟩),
    show row_qqOrTotal_R = row_qqOrTotal_body from rfl, ← freeIter_one, (inst_qqOrTotal hwp hwq).2]
  simp

lemma ctx_qqAllTotal {Γ wp : V} (hwp : IsSemiterm LAct 0 wp) :
    ctxAfter Γ (mkStep W 28 ?[wp]) = insert (neg LAct (allFact (^&0) (termShift LAct wp))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqAllTotal : ℕ) : V) = (28 : V) := by simp [rIdx_qqAllTotal]
  have hstep := mkStep_qqAllTotal (V := V) ?[wp]
  rw [hk] at hstep
  rw [hstep, show (?[wp] : V) = vecOf [wp] from rfl,
    ctxAfter_introFact [wp] row_qqAllTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqAllTotal_R)
      (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩),
    show row_qqAllTotal_R = row_qqAllTotal_body from rfl, ← freeIter_one, (inst_qqAllTotal hwp).2]
  simp

lemma ctx_qqExsTotal {Γ wp : V} (hwp : IsSemiterm LAct 0 wp) :
    ctxAfter Γ (mkStep W 30 ?[wp]) = insert (neg LAct (exsFact (^&0) (termShift LAct wp))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqExsTotal : ℕ) : V) = (30 : V) := by simp [rIdx_qqExsTotal]
  have hstep := mkStep_qqExsTotal (V := V) ?[wp]
  rw [hk] at hstep
  rw [hstep, show (?[wp] : V) = vecOf [wp] from rfl,
    ctxAfter_introFact [wp] row_qqExsTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqExsTotal_R)
      (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩),
    show row_qqExsTotal_R = row_qqExsTotal_body from rfl, ← freeIter_one, (inst_qqExsTotal hwp).2]
  simp

lemma ctx_qqRelTotal {Γ wk wR wv : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) :
    ctxAfter Γ (mkStep W 32 ?[wk, wR, wv]) =
      insert (neg LAct (relFact (^&0) (termShift LAct wk) (termShift LAct wR) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqRelTotal : ℕ) : V) = (32 : V) := by simp [rIdx_qqRelTotal]
  have hstep := mkStep_qqRelTotal (V := V) ?[wk, wR, wv]
  rw [hk] at hstep
  rw [hstep, show (?[wk, wR, wv] : V) = vecOf [wk, wR, wv] from rfl,
    ctxAfter_introFact [wk, wR, wv] row_qqRelTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqRelTotal_R)
      (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩),
    show row_qqRelTotal_R = row_qqRelTotal_body from rfl, ← freeIter_one, (inst_qqRelTotal hwk hwR hwv).2]
  simp

lemma ctx_qqNRelTotal {Γ wk wR wv : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) :
    ctxAfter Γ (mkStep W 34 ?[wk, wR, wv]) =
      insert (neg LAct (nrelFact (^&0) (termShift LAct wk) (termShift LAct wR) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqNRelTotal : ℕ) : V) = (34 : V) := by simp [rIdx_qqNRelTotal]
  have hstep := mkStep_qqNRelTotal (V := V) ?[wk, wR, wv]
  rw [hk] at hstep
  rw [hstep, show (?[wk, wR, wv] : V) = vecOf [wk, wR, wv] from rfl,
    ctxAfter_introFact [wk, wR, wv] row_qqNRelTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqNRelTotal_R)
      (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩),
    show row_qqNRelTotal_R = row_qqNRelTotal_body from rfl, ← freeIter_one, (inst_qqNRelTotal hwk hwR hwv).2]
  simp

/-- The Horn bridges: the `.pi` facts and `utvPi`. -/
lemma ctx_isSemitermSigmaPiLAct {Γ wn wt : V} (hwn : IsSemiterm LAct 0 wn) (hwt : IsSemiterm LAct 0 wt) :
    ctxAfter Γ (mkStep W 4 ?[wn, wt]) = insert (neg LAct (tPiFact wn wt)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermSigmaPiLAct : ℕ) : V) = (4 : V) := by simp [rIdx_isSemitermSigmaPiLAct]
  have hstep := mkStep_isSemitermSigmaPiLAct (V := V) ?[wn, wt]
  rw [hk] at hstep
  rw [hstep, show (?[wn, wt] : V) = vecOf [wn, wt] from rfl,
    ctxAfter_useHorn [wn, wt] row_isSemitermSigmaPiLAct_as isSemiformula_isSemitermSigmaPiLAct_c
      (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩),
    (inst_isSemitermSigmaPiLAct hwn hwt).2]

lemma ctx_isSemitermVecSigmaPiLAct {Γ wk wn wv : V} (hwk : IsSemiterm LAct 0 wk) (hwn : IsSemiterm LAct 0 wn) (hwv : IsSemiterm LAct 0 wv) :
    ctxAfter Γ (mkStep W 16 ?[wk, wn, wv]) = insert (neg LAct (tvPiFact wk wn wv)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V) = (16 : V) := by simp [rIdx_isSemitermVecSigmaPiLAct]
  have hstep := mkStep_isSemitermVecSigmaPiLAct (V := V) ?[wk, wn, wv]
  rw [hk] at hstep
  rw [hstep, show (?[wk, wn, wv] : V) = vecOf [wk, wn, wv] from rfl,
    ctxAfter_useHorn [wk, wn, wv] row_isSemitermVecSigmaPiLAct_as isSemiformula_isSemitermVecSigmaPiLAct_c
      (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩),
    (inst_isSemitermVecSigmaPiLAct hwk hwn hwv).2]

lemma ctx_isSemiformulaSigmaPi {Γ wn wp : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) :
    ctxAfter Γ (mkStep W 21 ?[wn, wp]) = insert (neg LAct (piFact wn wp)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaSigmaPi : ℕ) : V) = (21 : V) := by simp [rIdx_isSemiformulaSigmaPi]
  have hstep := mkStep_isSemiformulaSigmaPi (V := V) ?[wn, wp]
  rw [hk] at hstep
  rw [hstep, show (?[wn, wp] : V) = vecOf [wn, wp] from rfl,
    ctxAfter_useHorn [wn, wp] row_isSemiformulaSigmaPi_as isSemiformula_isSemiformulaSigmaPi_c
      (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩),
    (inst_isSemiformulaSigmaPi hwn hwp).2]

lemma ctx_isUTermVecSigmaPiLAct {Γ wk wv : V} (hwk : IsSemiterm LAct 0 wk) (hwv : IsSemiterm LAct 0 wv) :
    ctxAfter Γ (mkStep W 39 ?[wk, wv]) = insert (neg LAct (utvPiFact wk wv)) Γ := by
  subst hWp
  have hk : ((rIdx_isUTermVecSigmaPiLAct : ℕ) : V) = (39 : V) := by simp [rIdx_isUTermVecSigmaPiLAct]
  have hstep := mkStep_isUTermVecSigmaPiLAct (V := V) ?[wk, wv]
  rw [hk] at hstep
  rw [hstep, show (?[wk, wv] : V) = vecOf [wk, wv] from rfl,
    ctxAfter_useHorn [wk, wv] row_isUTermVecSigmaPiLAct_as isSemiformula_isUTermVecSigmaPiLAct_c
      (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩),
    (inst_isUTermVecSigmaPiLAct hwk hwv).2]

end ctxSteps

/-! ### 0.4 Final contexts of the node lists -/

section nodeCtx

lemma finalCtx_three (Γ S a b c : V) :
    finalCtx Γ (appendV S ?[a, b, c]) = ctxAfter (ctxAfter (ctxAfter (finalCtx Γ S) a) b) c := by
  rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single]

lemma finalCtx_six (Γ S a b c d e f : V) :
    finalCtx Γ (appendV S ?[a, b, c, d, e, f]) =
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (finalCtx Γ S) a) b) c) d) e) f := by
  rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_single]

lemma mem_insert_self' {x s : V} : x ∈ insert x s := by simp
lemma mem_insert_of_mem' {x y s : V} (h : x ∈ s) : x ∈ insert y s := by simp [h]
lemma mem_setShift_of_mem {x Γ : V} (h : x ∈ Γ) : shift LAct x ∈ setShift LAct Γ :=
  mem_setShift_iff.mpr ⟨x, h, rfl⟩

end nodeCtx

/-! ### 0.5 Decomposition of a dossier: the node's shape facts and the children's dossiers -/

section decompose

lemma shiftIterV_one (f : V) : shiftIterV f 1 = shift LAct f := by
  rw [show (1 : V) = 0 + 1 by simp, shiftIterV_succ, shiftIterV_zero]
lemma shiftIterV_shift (f i : V) : shiftIterV (shift LAct f) i = shiftIterV f (i + 1) := by
  rw [add_comm, shiftIterV_add, shiftIterV_one]

/-- A fact about `&0` and closed chain numerals/vector references, read off a dossier at offset `i`. -/
lemma dossT_mem {W Γ n t i f : V} (h : DossT W Γ n t i) (hf : f ∈ finalCtx 0 (describeT W n t)) :
    shiftIterV f i ∈ Γ := h f hf
lemma dossF_mem {W Γ n r i f : V} (h : DossF W Γ n r i) (hf : f ∈ finalCtx 0 (describeF W n r)) :
    shiftIterV f i ∈ Γ := h f hf

variable {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {W : V} (hWp : W = walkPieces)
include htbl hW hWp

/-- `#z` at offset `i`: `bvarF &i (cT z)` and `tPiF (cT n) &i`. -/
theorem dossT_bvar {Γ n z i : V} (h : DossT W Γ n (^#z) i) :
    neg LAct (bvarFact (^&i) (cTV z)) ∈ Γ ∧ neg LAct (tPiFact (cTV n) (^&i)) ∈ Γ := by
  have hS := describeT_bvar W n z
  have hctx : finalCtx 0 (describeT W n (^#z)) =
      ctxAfter (ctxAfter (ctxAfter (finalCtx 0 (ltSteps W n z)) (mkStep W 2 ?[cTV z]))
        (mkStep W 3 ?[cTV n, cTV z, ^&0])) (mkStep W 4 ?[cTV n, ^&0]) := by
    rw [hS, finalCtx_three]
  have h1 : neg LAct (bvarFact (^&0) (cTV z)) ∈ finalCtx 0 (describeT W n (^#z)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermBvar hWp _)) ?_)
    rw [ctx_qqBvarTotal hWp (cTV_semiterm_LAct 0 _), termShift_cTV]
    exact mem_insert_self'
  have h2 : neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx 0 (describeT W n (^#z)) := by
    rw [hctx, ctx_isSemitermSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have e1 := dossT_mem h h1
  have e2 := dossT_mem h h2
  rw [shiftIterV_neg (isFormula_bvarFact (by simp) (cTV_semiterm_LAct 0 _)), shiftIterV_bvarFact (by simp) (cTV_semiterm_LAct 0 _),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e1
  rw [shiftIterV_neg (isFormula_tPiFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_tPiFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  exact ⟨e1, e2⟩

/-- `&x` at offset `i`: `fvarF &i (cT x)` and `tPiF (cT n) &i`. -/
theorem dossT_fvar {Γ n x i : V} (h : DossT W Γ n (^&x) i) :
    neg LAct (fvarFact (^&i) (cTV x)) ∈ Γ ∧ neg LAct (tPiFact (cTV n) (^&i)) ∈ Γ := by
  have hS := describeT_fvar W n x
  have hctx : finalCtx 0 (describeT W n (^&x)) =
      ctxAfter (ctxAfter (ctxAfter 0 (mkStep W 5 ?[cTV x])) (mkStep W 6 ?[cTV n, cTV x, ^&0])) (mkStep W 4 ?[cTV n, ^&0]) := by
    rw [hS, finalCtx_cons, finalCtx_cons, finalCtx_single]
  have h1 : neg LAct (fvarFact (^&0) (cTV x)) ∈ finalCtx 0 (describeT W n (^&x)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermFvar hWp _)) ?_)
    rw [ctx_qqFvarTotal hWp (cTV_semiterm_LAct 0 _), termShift_cTV]
    exact mem_insert_self'
  have h2 : neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx 0 (describeT W n (^&x)) := by
    rw [hctx, ctx_isSemitermSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have e1 := dossT_mem h h1
  have e2 := dossT_mem h h2
  rw [shiftIterV_neg (isFormula_fvarFact (by simp) (cTV_semiterm_LAct 0 _)), shiftIterV_fvarFact (by simp) (cTV_semiterm_LAct 0 _),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e1
  rw [shiftIterV_neg (isFormula_tPiFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_tPiFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  exact ⟨e1, e2⟩

/-- `func k f v` at offset `i`: `funcF &i (cT k) (cT f) ⟨v⟩`, `tPiF`, `utvPiF (cT k) ⟨v⟩` with
`⟨v⟩ = vRef (i + 1) k`, and the vector's dossier at `i + 1`. -/
theorem dossT_func {Γ n k f v i : V} (hkf : LAct.IsFunc k f) (hv : IsSemitermVec LAct k n v)
    (h : DossT W Γ n (^func k f v) i) :
    neg LAct (funcFact (^&i) (cTV k) (cTV f) (vRef (i + 1) k)) ∈ Γ ∧ neg LAct (tPiFact (cTV n) (^&i)) ∈ Γ ∧
    neg LAct (utvPiFact (cTV k) (vRef (i + 1) k)) ∈ Γ ∧ DossV W Γ n k v k (i + 1) := by
  have hS := describeT_func W n hkf hv.isUTerm
  set Sv := π₂ (descVecAux W n (descTVec W n k v) k) with hSv
  have hctx : finalCtx 0 (describeT W n (^func k f v)) =
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (finalCtx 0 Sv) (mkStep W (funcRow k f) 0))
        (mkStep W 7 ?[cTV k, cTV f, vRef 0 k])) (mkStep W 8 ?[cTV n, cTV k, cTV f, vRef 1 k, ^&0]))
        (mkStep W 4 ?[cTV n, ^&0])) (mkStep W 38 ?[cTV k, cTV n, vRef 1 k])) (mkStep W 39 ?[cTV k, vRef 1 k]) := by
    rw [hS, finalCtx_six]
  have hr0 : IsSemiterm LAct 0 (vRef 0 k) := isSemiterm_vRef _ _
  have hr1 : IsSemiterm LAct 0 (vRef 1 k) := isSemiterm_vRef _ _
  have h1 : neg LAct (funcFact (^&0) (cTV k) (cTV f) (vRef 1 k)) ∈ finalCtx 0 (describeT W n (^func k f v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermFunc hWp _)) ?_)))
    rw [ctx_qqFuncTotal hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr0, termShift_cTV, termShift_cTV,
      termShift_vRef, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx 0 (describeT W n (^func k f v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _)) ?_)
    rw [ctx_isSemitermSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have h3 : neg LAct (utvPiFact (cTV k) (vRef 1 k)) ∈ finalCtx 0 (describeT W n (^func k f v)) := by
    rw [hctx, ctx_isUTermVecSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) hr1]
    exact mem_insert_self'
  have h4 : ∀ g ∈ finalCtx 0 Sv, shift LAct g ∈ finalCtx 0 (describeT W n (^func k f v)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermFunc hWp _)) ?_)))
    rw [ctx_qqFuncTotal hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr0]
    exact mem_insert_of_mem' (mem_setShift_of_mem (mem_ctxAfter_of_noShift (Or.inl (tag_funcRow hWp k f _)) hg))
  have e1 := dossT_mem h h1
  have e2 := dossT_mem h h2
  have e3 := dossT_mem h h3
  rw [shiftIterV_neg (isFormula_funcFact (by simp) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr1),
    shiftIterV_funcFact (by simp) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr1,
    termShiftIterV_fvar, termShiftIterV_cTV, termShiftIterV_cTV, termShiftIterV_vRef, zero_add, add_comm 1 i] at e1
  rw [shiftIterV_neg (isFormula_tPiFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_tPiFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  rw [shiftIterV_neg (isFormula_utvPiFact (cTV_semiterm_LAct 0 _) hr1), shiftIterV_utvPiFact (cTV_semiterm_LAct 0 _) hr1,
    termShiftIterV_cTV, termShiftIterV_vRef, add_comm 1 i] at e3
  refine ⟨e1, e2, e3, ?_⟩
  intro g hg
  have := dossT_mem h (h4 g hg)
  rwa [shiftIterV_shift] at this

/-- The vector walk of `j + 1` entries at offset `i`: the entry `t := v.[k − (j+1)]` at `i + 1` (with
`ct := descCountT t` eigenvariables), the tail vector at `i + 1 + ct`, and the node's facts
`adjF &i &(i+1) (vRef (i + 1 + ct) j)`, `tvPiF (cT (j+1)) (cT n) &i`. -/
theorem dossV_succ {Γ n k v j i : V} (hv : IsSemitermVec LAct k n v) (hj : j + 1 ≤ k)
    (h : DossV W Γ n k v (j + 1) i) :
    neg LAct (adjFact (^&i) (^&(i + 1)) (vRef (i + 1 + descCountT W n v.[k - (j + 1)]) j)) ∈ Γ ∧
    neg LAct (tvPiFact (cTV (j + 1)) (cTV n) (^&i)) ∈ Γ ∧
    DossT W Γ n v.[k - (j + 1)] (i + 1) ∧
    DossV W Γ n k v j (i + 1 + descCountT W n v.[k - (j + 1)]) := by
  have hvlen : len v = k := hv.lh
  have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
  have hi : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have ht : IsSemiterm LAct n v.[k - (j + 1)] := hv.nth hi
  have hnth : nthFromEnd (descTVec W n k v) j = descT W n v.[k - (j + 1)] := by
    rw [nthFromEnd_eq (a := k - (j + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hj]),
      nth_descTVec W n hv.isUTerm hi]
  set t := v.[k - (j + 1)] with htdef
  set ct := descCountT W n t with hct
  set Sv := π₂ (descVecAux W n (descTVec W n k v) j) with hSv
  have hS : π₂ (descVecAux W n (descTVec W n k v) (j + 1)) =
      appendV Sv (appendV (describeT W n t)
        ?[mkStep W 17 ?[^&0, vRef ct j], mkStep W 18 ?[cTV j, cTV n, vRef (ct + 1) j, ^&1, ^&0],
          mkStep W 16 ?[cTV (j + 1), cTV n, ^&0]]) := by
    rw [descVecAux_succ, hnth, adjNode, pi₂_pair]; rfl
  have hctx : finalCtx 0 (π₂ (descVecAux W n (descTVec W n k v) (j + 1))) =
      ctxAfter (ctxAfter (ctxAfter (finalCtx (finalCtx 0 Sv) (describeT W n t)) (mkStep W 17 ?[^&0, vRef ct j]))
        (mkStep W 18 ?[cTV j, cTV n, vRef (ct + 1) j, ^&1, ^&0])) (mkStep W 16 ?[cTV (j + 1), cTV n, ^&0]) := by
    rw [hS, finalCtx_appendV, finalCtx_three]
  -- the term walk's facts (from the empty context)
  obtain ⟨_, hndT, hshT, _, _⟩ := describeT_ok htbl hW (n := n) (t := t) ht (E := 2 * n + 2 * termLen LAct t + 8) le_rfl
    (Γ := 0) IsFormulaSet.empty
  rw [← hWp] at hndT hshT
  have hr : IsSemiterm LAct 0 (vRef ct j) := isSemiterm_vRef _ _
  have h1 : neg LAct (adjFact (^&0) (^&1) (vRef (ct + 1) j)) ∈ finalCtx 0 (π₂ (descVecAux W n (descTVec W n k v) (j + 1))) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermVecAdjoin hWp _)) ?_)
    rw [ctx_adjoinTotal hWp (by simp) hr, termShift_fvar, zero_add, termShift_vRef]
    exact mem_insert_self'
  have h2 : neg LAct (tvPiFact (cTV (j + 1)) (cTV n) (^&0)) ∈ finalCtx 0 (π₂ (descVecAux W n (descTVec W n k v) (j + 1))) := by
    rw [hctx, ctx_isSemitermVecSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have hlift : ∀ g ∈ finalCtx (finalCtx 0 Sv) (describeT W n t),
      shift LAct g ∈ finalCtx 0 (π₂ (descVecAux W n (descTVec W n k v) (j + 1))) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermVecAdjoin hWp _)) ?_)
    rw [ctx_adjoinTotal hWp (by simp) hr]
    exact mem_insert_of_mem' (mem_setShift_of_mem hg)
  have e1 := h _ h1
  have e2 := h _ h2
  rw [shiftIterV_neg (isFormula_adjFact (by simp) (by simp) (isSemiterm_vRef _ _)),
    shiftIterV_adjFact (by simp) (by simp) (isSemiterm_vRef _ _), termShiftIterV_fvar, termShiftIterV_fvar,
    termShiftIterV_vRef, zero_add, add_comm 1 i, show ct + 1 + i = i + 1 + ct by ring] at e1
  rw [shiftIterV_neg (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (by simp)),
    shiftIterV_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_cTV, termShiftIterV_cTV, termShiftIterV_fvar, zero_add] at e2
  refine ⟨e1, e2, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ finalCtx (finalCtx 0 Sv) (describeT W n t) :=
      finalCtx_mono hndT (fun x hx ↦ by simp at hx) hg
    have := h _ (hlift g hg')
    rwa [shiftIterV_shift] at this
  · intro g hg
    have hg' : shiftIterV g ct ∈ finalCtx (finalCtx 0 Sv) (describeT W n t) := by
      have := mem_finalCtx_of_mem hndT hg
      rwa [hshT] at this
    have := h _ (hlift _ hg')
    rw [shiftIterV_shift, ← shiftIterV_add] at this
    rwa [show i + 1 + ct = ct + (i + 1) by ring]

/-! #### The formula nodes -/

theorem dossF_verum {Γ n i : V} (h : DossF W Γ n ^⊤ i) :
    neg LAct (verumFact (^&i)) ∈ Γ ∧ neg LAct (piFact (cTV n) (^&i)) ∈ Γ := by
  have hctx : finalCtx 0 (describeF W n ^⊤) =
      ctxAfter (ctxAfter (ctxAfter 0 (mkStep W 19 0)) (mkStep W 20 ?[cTV n, ^&0])) (mkStep W 21 ?[cTV n, ^&0]) := by
    rw [describeF, descFw_verum, constNode, pi₂_pair, finalCtx_cons, finalCtx_cons, finalCtx_single]
  have h1 : neg LAct (verumFact (^&0)) ∈ finalCtx 0 (describeF W n ^⊤) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaVerum hWp _)) ?_)
    rw [ctx_qqVerumTotal hWp]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n ^⊤) := by
    rw [hctx, ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  rw [shiftIterV_neg (isFormula_verumFact (by simp)), shiftIterV_verumFact (by simp), termShiftIterV_fvar, zero_add] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  exact ⟨e1, e2⟩

theorem dossF_falsum {Γ n i : V} (h : DossF W Γ n ^⊥ i) :
    neg LAct (falsumFact (^&i)) ∈ Γ ∧ neg LAct (piFact (cTV n) (^&i)) ∈ Γ := by
  have hctx : finalCtx 0 (describeF W n ^⊥) =
      ctxAfter (ctxAfter (ctxAfter 0 (mkStep W 22 0)) (mkStep W 23 ?[cTV n, ^&0])) (mkStep W 21 ?[cTV n, ^&0]) := by
    rw [describeF, descFw_falsum, constNode, pi₂_pair, finalCtx_cons, finalCtx_cons, finalCtx_single]
  have h1 : neg LAct (falsumFact (^&0)) ∈ finalCtx 0 (describeF W n ^⊥) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaFalsum hWp _)) ?_)
    rw [ctx_qqFalsumTotal hWp]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n ^⊥) := by
    rw [hctx, ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  rw [shiftIterV_neg (isFormula_falsumFact (by simp)), shiftIterV_falsumFact (by simp), termShiftIterV_fvar, zero_add] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  exact ⟨e1, e2⟩

/-- The NoDrop/shift count of a walk from the empty context. -/
lemma describeF_noDrop_shifts {n r : V} (hr : IsSemiformula LAct n r) :
    NoDrop (describeF W n r) ∧ shiftsV (describeF W n r) = descCountF W n r := by
  obtain ⟨_, hnd, hsh, _, _⟩ := describeF_ok htbl hW hr (E := 2 * n + 2 * formulaLen LAct r + 8) le_rfl (Γ := 0) IsFormulaSet.empty
  rw [← hWp] at hnd hsh
  exact ⟨hnd, hsh⟩

/-- A binary node `p ⋏ q` / `p ⋎ q` at offset `i`: `q` at `i + 1`, `p` at `i + cq + 1`, the shape fact
about `&i`, `&(i + cq + 1)`, `&(i + 1)`, and `piF (cT n) &i`. -/
theorem dossF_and {Γ n p q i : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q)
    (h : DossF W Γ n (p ^⋏ q) i) :
    neg LAct (andFact (^&i) (^&(i + descCountF W n q + 1)) (^&(i + 1))) ∈ Γ ∧
    neg LAct (piFact (cTV n) (^&i)) ∈ Γ ∧ DossF W Γ n q (i + 1) ∧ DossF W Γ n p (i + descCountF W n q + 1) := by
  set cq := descCountF W n q with hcq
  have hS : describeF W n (p ^⋏ q) = appendV (describeF W n p) (appendV (describeF W n q)
      ?[mkStep W 24 ?[^&cq, ^&0], mkStep W 25 ?[cTV n, ^&(cq + 1), ^&1, ^&0], mkStep W 21 ?[cTV n, ^&0]]) := by
    rw [describeF, descFw_and W n hp hq, binNode, pi₂_pair]; rfl
  have hctx : finalCtx 0 (describeF W n (p ^⋏ q)) =
      ctxAfter (ctxAfter (ctxAfter (finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q)) (mkStep W 24 ?[^&cq, ^&0]))
        (mkStep W 25 ?[cTV n, ^&(cq + 1), ^&1, ^&0])) (mkStep W 21 ?[cTV n, ^&0]) := by
    rw [hS, finalCtx_appendV, finalCtx_three]
  obtain ⟨hndq, hshq⟩ := describeF_noDrop_shifts htbl hW hWp hq
  have h1 : neg LAct (andFact (^&0) (^&(cq + 1)) (^&1)) ∈ finalCtx 0 (describeF W n (p ^⋏ q)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaAnd hWp _)) ?_)
    rw [ctx_qqAndTotal hWp (by simp) (by simp), termShift_fvar, termShift_fvar, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n (p ^⋏ q)) := by
    rw [hctx, ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have hlift : ∀ g ∈ finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q),
      shift LAct g ∈ finalCtx 0 (describeF W n (p ^⋏ q)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaAnd hWp _)) ?_)
    rw [ctx_qqAndTotal hWp (by simp) (by simp)]
    exact mem_insert_of_mem' (mem_setShift_of_mem hg)
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  rw [shiftIterV_neg (isFormula_andFact (by simp) (by simp) (by simp)), shiftIterV_andFact (by simp) (by simp) (by simp),
    termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, zero_add, add_comm 1 i,
    show cq + 1 + i = i + cq + 1 by ring] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  refine ⟨e1, e2, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q) :=
      finalCtx_mono hndq (fun x hx ↦ by simp at hx) hg
    have := dossF_mem h (hlift g hg')
    rwa [shiftIterV_shift] at this
  · intro g hg
    have hg' : shiftIterV g cq ∈ finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q) := by
      have := mem_finalCtx_of_mem hndq hg
      rwa [hshq] at this
    have := dossF_mem h (hlift _ hg')
    rw [shiftIterV_shift, ← shiftIterV_add] at this
    rwa [show i + cq + 1 = cq + (i + 1) by ring]

theorem dossF_or {Γ n p q i : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q)
    (h : DossF W Γ n (p ^⋎ q) i) :
    neg LAct (orFact (^&i) (^&(i + descCountF W n q + 1)) (^&(i + 1))) ∈ Γ ∧
    neg LAct (piFact (cTV n) (^&i)) ∈ Γ ∧ DossF W Γ n q (i + 1) ∧ DossF W Γ n p (i + descCountF W n q + 1) := by
  set cq := descCountF W n q with hcq
  have hS : describeF W n (p ^⋎ q) = appendV (describeF W n p) (appendV (describeF W n q)
      ?[mkStep W 26 ?[^&cq, ^&0], mkStep W 27 ?[cTV n, ^&(cq + 1), ^&1, ^&0], mkStep W 21 ?[cTV n, ^&0]]) := by
    rw [describeF, descFw_or W n hp hq, binNode, pi₂_pair]; rfl
  have hctx : finalCtx 0 (describeF W n (p ^⋎ q)) =
      ctxAfter (ctxAfter (ctxAfter (finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q)) (mkStep W 26 ?[^&cq, ^&0]))
        (mkStep W 27 ?[cTV n, ^&(cq + 1), ^&1, ^&0])) (mkStep W 21 ?[cTV n, ^&0]) := by
    rw [hS, finalCtx_appendV, finalCtx_three]
  obtain ⟨hndq, hshq⟩ := describeF_noDrop_shifts htbl hW hWp hq
  have h1 : neg LAct (orFact (^&0) (^&(cq + 1)) (^&1)) ∈ finalCtx 0 (describeF W n (p ^⋎ q)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaOr hWp _)) ?_)
    rw [ctx_qqOrTotal hWp (by simp) (by simp), termShift_fvar, termShift_fvar, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n (p ^⋎ q)) := by
    rw [hctx, ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have hlift : ∀ g ∈ finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q),
      shift LAct g ∈ finalCtx 0 (describeF W n (p ^⋎ q)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaOr hWp _)) ?_)
    rw [ctx_qqOrTotal hWp (by simp) (by simp)]
    exact mem_insert_of_mem' (mem_setShift_of_mem hg)
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  rw [shiftIterV_neg (isFormula_orFact (by simp) (by simp) (by simp)), shiftIterV_orFact (by simp) (by simp) (by simp),
    termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar, zero_add, add_comm 1 i,
    show cq + 1 + i = i + cq + 1 by ring] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  refine ⟨e1, e2, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q) :=
      finalCtx_mono hndq (fun x hx ↦ by simp at hx) hg
    have := dossF_mem h (hlift g hg')
    rwa [shiftIterV_shift] at this
  · intro g hg
    have hg' : shiftIterV g cq ∈ finalCtx (finalCtx 0 (describeF W n p)) (describeF W n q) := by
      have := mem_finalCtx_of_mem hndq hg
      rwa [hshq] at this
    have := dossF_mem h (hlift _ hg')
    rw [shiftIterV_shift, ← shiftIterV_add] at this
    rwa [show i + cq + 1 = cq + (i + 1) by ring]

/-- A quantifier node at offset `i`: the body (arity `n + 1`) at `i + 1`. -/
theorem dossF_all {Γ n p i : V} (hp : IsSemiformula LAct (n + 1) p) (h : DossF W Γ n (^∀ p) i) :
    neg LAct (allFact (^&i) (^&(i + 1))) ∈ Γ ∧ neg LAct (piFact (cTV n) (^&i)) ∈ Γ ∧ DossF W Γ (n + 1) p (i + 1) := by
  have hS : describeF W n (^∀ p) = appendV (describeF W (n + 1) p)
      ?[mkStep W 28 ?[^&0], mkStep W 29 ?[cTV n, ^&1, ^&0], mkStep W 21 ?[cTV n, ^&0]] := by
    rw [describeF, descFw_all W n hp, quantNode, pi₂_pair]; rfl
  have hctx : finalCtx 0 (describeF W n (^∀ p)) =
      ctxAfter (ctxAfter (ctxAfter (finalCtx 0 (describeF W (n + 1) p)) (mkStep W 28 ?[^&0]))
        (mkStep W 29 ?[cTV n, ^&1, ^&0])) (mkStep W 21 ?[cTV n, ^&0]) := by
    rw [hS, finalCtx_three]
  have h1 : neg LAct (allFact (^&0) (^&1)) ∈ finalCtx 0 (describeF W n (^∀ p)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaAll hWp _)) ?_)
    rw [ctx_qqAllTotal hWp (by simp), termShift_fvar, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n (^∀ p)) := by
    rw [hctx, ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have hlift : ∀ g ∈ finalCtx 0 (describeF W (n + 1) p), shift LAct g ∈ finalCtx 0 (describeF W n (^∀ p)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaAll hWp _)) ?_)
    rw [ctx_qqAllTotal hWp (by simp)]
    exact mem_insert_of_mem' (mem_setShift_of_mem hg)
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  rw [shiftIterV_neg (isFormula_allFact (by simp) (by simp)), shiftIterV_allFact (by simp) (by simp),
    termShiftIterV_fvar, termShiftIterV_fvar, zero_add, add_comm 1 i] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  refine ⟨e1, e2, ?_⟩
  intro g hg
  have := dossF_mem h (hlift g hg)
  rwa [shiftIterV_shift] at this

theorem dossF_exs {Γ n p i : V} (hp : IsSemiformula LAct (n + 1) p) (h : DossF W Γ n (^∃ p) i) :
    neg LAct (exsFact (^&i) (^&(i + 1))) ∈ Γ ∧ neg LAct (piFact (cTV n) (^&i)) ∈ Γ ∧ DossF W Γ (n + 1) p (i + 1) := by
  have hS : describeF W n (^∃ p) = appendV (describeF W (n + 1) p)
      ?[mkStep W 30 ?[^&0], mkStep W 31 ?[cTV n, ^&1, ^&0], mkStep W 21 ?[cTV n, ^&0]] := by
    rw [describeF, descFw_exs W n hp, quantNode, pi₂_pair]; rfl
  have hctx : finalCtx 0 (describeF W n (^∃ p)) =
      ctxAfter (ctxAfter (ctxAfter (finalCtx 0 (describeF W (n + 1) p)) (mkStep W 30 ?[^&0]))
        (mkStep W 31 ?[cTV n, ^&1, ^&0])) (mkStep W 21 ?[cTV n, ^&0]) := by
    rw [hS, finalCtx_three]
  have h1 : neg LAct (exsFact (^&0) (^&1)) ∈ finalCtx 0 (describeF W n (^∃ p)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaExs hWp _)) ?_)
    rw [ctx_qqExsTotal hWp (by simp), termShift_fvar, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n (^∃ p)) := by
    rw [hctx, ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have hlift : ∀ g ∈ finalCtx 0 (describeF W (n + 1) p), shift LAct g ∈ finalCtx 0 (describeF W n (^∃ p)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaExs hWp _)) ?_)
    rw [ctx_qqExsTotal hWp (by simp)]
    exact mem_insert_of_mem' (mem_setShift_of_mem hg)
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  rw [shiftIterV_neg (isFormula_exsFact (by simp) (by simp)), shiftIterV_exsFact (by simp) (by simp),
    termShiftIterV_fvar, termShiftIterV_fvar, zero_add, add_comm 1 i] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  refine ⟨e1, e2, ?_⟩
  intro g hg
  have := dossF_mem h (hlift g hg)
  rwa [shiftIterV_shift] at this

/-- An atom at offset `i`: `relF &i (cT k) (cT R) ⟨v⟩`, `piF`, `utvPiF (cT k) ⟨v⟩` with `⟨v⟩ = vRef (i + 1) k`,
and the vector's dossier at `i + 1`. -/
theorem dossF_rel {Γ n k R v i : V} (hkR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v)
    (h : DossF W Γ n (^rel k R v) i) :
    neg LAct (relFact (^&i) (cTV k) (cTV R) (vRef (i + 1) k)) ∈ Γ ∧ neg LAct (piFact (cTV n) (^&i)) ∈ Γ ∧
    neg LAct (utvPiFact (cTV k) (vRef (i + 1) k)) ∈ Γ ∧ DossV W Γ n k v k (i + 1) := by
  set Sv := π₂ (descVecAux W n (descTVec W n k v) k) with hSv
  have hS : describeF W n (^rel k R v) = appendV Sv
      ?[mkStep W (relRow R) 0, mkStep W 32 ?[cTV k, cTV R, vRef 0 k], mkStep W 33 ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0],
        mkStep W 21 ?[cTV n, ^&0], mkStep W 38 ?[cTV k, cTV n, vRef 1 k], mkStep W 39 ?[cTV k, vRef 1 k]] := by
    rw [describeF, descFw_rel W n hkR hv, atomNode, pi₂_pair]
  have hctx : finalCtx 0 (describeF W n (^rel k R v)) =
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (finalCtx 0 Sv) (mkStep W (relRow R) 0))
        (mkStep W 32 ?[cTV k, cTV R, vRef 0 k])) (mkStep W 33 ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0]))
        (mkStep W 21 ?[cTV n, ^&0])) (mkStep W 38 ?[cTV k, cTV n, vRef 1 k])) (mkStep W 39 ?[cTV k, vRef 1 k]) := by
    rw [hS, finalCtx_six]
  have hr0 : IsSemiterm LAct 0 (vRef 0 k) := isSemiterm_vRef _ _
  have hr1 : IsSemiterm LAct 0 (vRef 1 k) := isSemiterm_vRef _ _
  have h1 : neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ finalCtx 0 (describeF W n (^rel k R v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaRel hWp _)) ?_)))
    rw [ctx_qqRelTotal hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr0, termShift_cTV, termShift_cTV,
      termShift_vRef, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n (^rel k R v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _)) ?_)
    rw [ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have h3 : neg LAct (utvPiFact (cTV k) (vRef 1 k)) ∈ finalCtx 0 (describeF W n (^rel k R v)) := by
    rw [hctx, ctx_isUTermVecSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) hr1]
    exact mem_insert_self'
  have h4 : ∀ g ∈ finalCtx 0 Sv, shift LAct g ∈ finalCtx 0 (describeF W n (^rel k R v)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaRel hWp _)) ?_)))
    rw [ctx_qqRelTotal hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr0]
    exact mem_insert_of_mem' (mem_setShift_of_mem (mem_ctxAfter_of_noShift (Or.inl (tag_relRow hWp R _)) hg))
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  have e3 := dossF_mem h h3
  rw [shiftIterV_neg (isFormula_relFact (by simp) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr1),
    shiftIterV_relFact (by simp) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr1,
    termShiftIterV_fvar, termShiftIterV_cTV, termShiftIterV_cTV, termShiftIterV_vRef, zero_add, add_comm 1 i] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  rw [shiftIterV_neg (isFormula_utvPiFact (cTV_semiterm_LAct 0 _) hr1), shiftIterV_utvPiFact (cTV_semiterm_LAct 0 _) hr1,
    termShiftIterV_cTV, termShiftIterV_vRef, add_comm 1 i] at e3
  refine ⟨e1, e2, e3, ?_⟩
  intro g hg
  have := dossF_mem h (h4 g hg)
  rwa [shiftIterV_shift] at this

theorem dossF_nrel {Γ n k R v i : V} (hkR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v)
    (h : DossF W Γ n (^nrel k R v) i) :
    neg LAct (nrelFact (^&i) (cTV k) (cTV R) (vRef (i + 1) k)) ∈ Γ ∧ neg LAct (piFact (cTV n) (^&i)) ∈ Γ ∧
    neg LAct (utvPiFact (cTV k) (vRef (i + 1) k)) ∈ Γ ∧ DossV W Γ n k v k (i + 1) := by
  set Sv := π₂ (descVecAux W n (descTVec W n k v) k) with hSv
  have hS : describeF W n (^nrel k R v) = appendV Sv
      ?[mkStep W (relRow R) 0, mkStep W 34 ?[cTV k, cTV R, vRef 0 k], mkStep W 35 ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0],
        mkStep W 21 ?[cTV n, ^&0], mkStep W 38 ?[cTV k, cTV n, vRef 1 k], mkStep W 39 ?[cTV k, vRef 1 k]] := by
    rw [describeF, descFw_nrel W n hkR hv, atomNode, pi₂_pair]
  have hctx : finalCtx 0 (describeF W n (^nrel k R v)) =
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (finalCtx 0 Sv) (mkStep W (relRow R) 0))
        (mkStep W 34 ?[cTV k, cTV R, vRef 0 k])) (mkStep W 35 ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0]))
        (mkStep W 21 ?[cTV n, ^&0])) (mkStep W 38 ?[cTV k, cTV n, vRef 1 k])) (mkStep W 39 ?[cTV k, vRef 1 k]) := by
    rw [hS, finalCtx_six]
  have hr0 : IsSemiterm LAct 0 (vRef 0 k) := isSemiterm_vRef _ _
  have hr1 : IsSemiterm LAct 0 (vRef 1 k) := isSemiterm_vRef _ _
  have h1 : neg LAct (nrelFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ finalCtx 0 (describeF W n (^nrel k R v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaNRel hWp _)) ?_)))
    rw [ctx_qqNRelTotal hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr0, termShift_cTV, termShift_cTV,
      termShift_vRef, zero_add]
    exact mem_insert_self'
  have h2 : neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx 0 (describeF W n (^nrel k R v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _)) ?_)
    rw [ctx_isSemiformulaSigmaPi hWp (cTV_semiterm_LAct 0 _) (by simp)]
    exact mem_insert_self'
  have h3 : neg LAct (utvPiFact (cTV k) (vRef 1 k)) ∈ finalCtx 0 (describeF W n (^nrel k R v)) := by
    rw [hctx, ctx_isUTermVecSigmaPiLAct hWp (cTV_semiterm_LAct 0 _) hr1]
    exact mem_insert_self'
  have h4 : ∀ g ∈ finalCtx 0 Sv, shift LAct g ∈ finalCtx 0 (describeF W n (^nrel k R v)) := by
    intro g hg
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaSigmaPi hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemiformulaNRel hWp _)) ?_)))
    rw [ctx_qqNRelTotal hWp (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr0]
    exact mem_insert_of_mem' (mem_setShift_of_mem (mem_ctxAfter_of_noShift (Or.inl (tag_relRow hWp R _)) hg))
  have e1 := dossF_mem h h1
  have e2 := dossF_mem h h2
  have e3 := dossF_mem h h3
  rw [shiftIterV_neg (isFormula_nrelFact (by simp) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr1),
    shiftIterV_nrelFact (by simp) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) hr1,
    termShiftIterV_fvar, termShiftIterV_cTV, termShiftIterV_cTV, termShiftIterV_vRef, zero_add, add_comm 1 i] at e1
  rw [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at e2
  rw [shiftIterV_neg (isFormula_utvPiFact (cTV_semiterm_LAct 0 _) hr1), shiftIterV_utvPiFact (cTV_semiterm_LAct 0 _) hr1,
    termShiftIterV_cTV, termShiftIterV_vRef, add_comm 1 i] at e3
  refine ⟨e1, e2, e3, ?_⟩
  intro g hg
  have := dossF_mem h (h4 g hg)
  rwa [shiftIterV_shift] at this

end decompose

end ArithS
