import ArithS.Necessitation.Describe
import ArithS.Necessitation.NumSteps
import ArithS.Necessitation.RowInstB
import ArithS.Necessitation.CertRows
import ArithS.Necessitation.Layout
import ArithS.Necessitation.Frag1
import ArithS.Necessitation.Frag1

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

/-- The closed-symbol fact the walk emits at a `func` node, read off the dossier
(`dossT_func`'s missing fourth conjunct — the `isFuncFact` the certification rows need). -/
theorem dossT_func_isFunc {Γ n k f v i : V} (hkf : LAct.IsFunc k f) (hv : IsSemitermVec LAct k n v)
    (hSvSet : IsFormulaSet LAct (finalCtx 0 (π₂ (descVecAux W n (descTVec W n k v) k))))
    (h : DossT W Γ n (^func k f v) i) : neg LAct (isFuncFact (cTV k) (cTV f)) ∈ Γ := by
  have hS := describeT_func W n hkf hv.isUTerm
  set Sv := π₂ (descVecAux W n (descTVec W n k v) k) with hSv
  have hctx : finalCtx 0 (describeT W n (^func k f v)) =
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter (finalCtx 0 Sv) (mkStep W (funcRow k f) 0))
        (mkStep W 7 ?[cTV k, cTV f, vRef 0 k])) (mkStep W 8 ?[cTV n, cTV k, cTV f, vRef 1 k, ^&0]))
        (mkStep W 4 ?[cTV n, ^&0])) (mkStep W 38 ?[cTV k, cTV n, vRef 1 k])) (mkStep W 39 ?[cTV k, vRef 1 k]) := by
    rw [hS, finalCtx_six]
  have hr0 : IsSemiterm LAct 0 (vRef 0 k) := isSemiterm_vRef _ _
  have hr1 : IsSemiterm LAct 0 (vRef 1 k) := isSemiterm_vRef _ _
  have h1 : neg LAct (isFuncFact (cTV k) (cTV f)) ∈ finalCtx 0 (describeT W n (^func k f v)) := by
    rw [hctx]
    refine mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isUTermVecOfSemitermVecLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermSigmaPiLAct hWp _))
      (mem_ctxAfter_of_noShift (Or.inl (tag_isSemitermFunc hWp _)) ?_)))
    have hbase : neg LAct (isFuncFact (cTV k) (cTV f)) ∈
        ctxAfter (finalCtx 0 Sv) (mkStep W (funcRow k f) 0) := by
      rw [(funcConst_ok (Γ := finalCtx 0 Sv) htbl hW hWp hkf (E := (8 : V)) le_rfl hSvSet).2.2.1]
      exact mem_insert_self'
    have hsh := mem_ctxAfter_of_shift (s := mkStep W 7 ?[cTV k, cTV f, vRef 0 k])
      (Or.inl (tag_qqFuncTotal hWp _)) hbase
    rwa [shift_neg (isFormula_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)),
      shift_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _),
      termShift_cTV, termShift_cTV] at hsh
  have e1 := dossT_mem h h1
  rwa [shiftIterV_neg (isFormula_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)),
    shiftIterV_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _),
    termShiftIterV_cTV, termShiftIterV_cTV] at e1

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

/-! ## Part 1 — the term-level certification pass (shift `ν = 2` / identification otherwise)

A pass is SHIFT-FREE: a list of Horn steps (tags `0`) over two dossiers in context — the source
object's (top `&i`) and the derived object's (top `&j`), both in walk layout — certifying at each node
that the derived node is the image of the source node (`tshFact &j &i` for `ν = 2`, `eqFactB &i &j`
for every other `ν` — the IDENTIFICATION pass, used at `ν = 0` and, by the formula pass's `neg`
family, at `ν = 1`: `neg` changes no term, but the image's atoms were walked afresh, so their
vectors must be identified with the source's; `tshvFact`/`eqFactB` at the vector level). The indices of the two trees run in parallel: the
child at walk offset `o` of the source sits at `&(i + o)`, the corresponding child of the derived
object at `&(j + o)` (the images of `neg`/`shift`/identity have the walk's shape, `descCountT_termShift`).
-/

section termPass

/-- The row of a leaf certificate: `termShiftBvarCert/termShiftFvarCert` (`ν = 2`), `eqOfBvar/eqOfFvar` (else:
the identification pass, `ν = 0` or `ν = 1`). -/
noncomputable def tLeafRow (ν kind : V) : V :=
  if ν = 2 then (if kind = 0 then 118 else 119) else (if kind = 0 then 124 else 125)

def tLeafRowDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y ν kind. (ν = 2 → ((kind = 0 → y = 118) ∧ (kind ≠ 0 → y = 119))) ∧ (ν ≠ 2 → ((kind = 0 → y = 124) ∧ (kind ≠ 0 → y = 125)))”

instance tLeafRow_defined : 𝚺₀-Function₂ (tLeafRow : V → V → V) via tLeafRowDef := .mk fun v ↦ by
  simp [tLeafRowDef, tLeafRow, numeral_eq_natCast]
  by_cases hν : v 1 = 2 <;> by_cases hk : v 2 = 0 <;> simp [hν, hk]
instance tLeafRow_definable : 𝚺₀-Function₂ (tLeafRow : V → V → V) := tLeafRow_defined.to_definable

/-- The leaf certificate `[row [cT z, &i, &j]]`. -/
noncomputable def tLeafSteps (W ν kind z i j : V) : V := ?[mkStep W (tLeafRow ν kind) ?[cTV z, ^&i, ^&j]]

noncomputable def tLeafStepsDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W ν kind z i j. ∃ ρ, !tLeafRowDef ρ ν kind ∧ ∃ cz, !cTVGraph cz z ∧ ∃ fi, !qqFvarDef fi i ∧ ∃ fj, !qqFvarDef fj j ∧
    ∃ e₀, !mkVec₂Def e₀ fi fj ∧ ∃ e, !adjoinDef e cz e₀ ∧ ∃ s, !mkStepDef s W ρ e ∧ !mkVec₁Def y s”

instance tLeafSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ tLeafSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) tLeafStepsDef := .mk
  fun v ↦ by simp [tLeafStepsDef, tLeafSteps, numeral_eq_natCast, tLeafRow_defined.iff, cTV.defined.iff, mkStep_defined.iff]
instance tLeafSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ tLeafSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  tLeafSteps_defined.to_definable

/-- The function-node certificate after the vector pass `yv`: the closed symbol row, then
`eqOfFunc`/`termShiftFuncCert [&i, cT k, cT f, ⟨v⟩ᵢ, ⟨v⟩ⱼ, &j]`. -/
noncomputable def tFuncSteps (W ν k f i j yv : V) : V :=
  appendV yv ?[mkStep W (funcRow k f) 0,
    mkStep W (if ν = 2 then 120 else 126) ?[^&i, cTV k, cTV f, vRef (i + 1) k, vRef (j + 1) k, ^&j]]

noncomputable def tFuncRow (ν : V) : V := if ν = 2 then 120 else 126
def tFuncRowDef : 𝚺₀.Semisentence 2 := .mkSigma “y ν. (ν = 2 → y = 120) ∧ (ν ≠ 2 → y = 126)”
instance tFuncRow_defined : 𝚺₀-Function₁ (tFuncRow : V → V) via tFuncRowDef := .mk fun v ↦ by
  simp [tFuncRowDef, tFuncRow, numeral_eq_natCast]
  by_cases hν : v 1 = 2 <;> simp [hν]
instance tFuncRow_definable : 𝚺₀-Function₁ (tFuncRow : V → V) := tFuncRow_defined.to_definable

lemma tFuncSteps_eq (W ν k f i j yv : V) : tFuncSteps W ν k f i j yv =
    appendV yv ?[mkStep W (funcRow k f) 0, mkStep W (tFuncRow ν) ?[^&i, cTV k, cTV f, vRef (i + 1) k, vRef (j + 1) k, ^&j]] := rfl

noncomputable def tFuncStepsDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W ν k f i j yv. ∃ ρ₁, !funcRowDef ρ₁ k f ∧ ∃ s₁, !mkStepDef s₁ W ρ₁ 0 ∧ ∃ ρ₂, !tFuncRowDef ρ₂ ν ∧
    ∃ fi, !qqFvarDef fi i ∧ ∃ fj, !qqFvarDef fj j ∧ ∃ ck, !cTVGraph ck k ∧ ∃ cf, !cTVGraph cf f ∧
    ∃ ri, !vRefDef ri (i + 1) k ∧ ∃ rj, !vRefDef rj (j + 1) k ∧
    ∃ e₀, !mkVec₂Def e₀ rj fj ∧ ∃ e₁, !adjoinDef e₁ ri e₀ ∧ ∃ e₂, !adjoinDef e₂ cf e₁ ∧ ∃ e₃, !adjoinDef e₃ ck e₂ ∧
    ∃ e, !adjoinDef e fi e₃ ∧ ∃ s₂, !mkStepDef s₂ W ρ₂ e ∧ ∃ l, !mkVec₂Def l s₁ s₂ ∧ !appendVDef y yv l”

instance tFuncSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ tFuncSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) tFuncStepsDef := .mk
  fun v ↦ by
    simp [tFuncStepsDef, tFuncSteps_eq, numeral_eq_natCast, funcRow_defined.iff, tFuncRow_defined.iff, cTV.defined.iff,
      mkStep_defined.iff, vRef_defined.iff, appendV_defined.iff]
instance tFuncSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ tFuncSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  tFuncSteps_defined.to_definable

/-- The empty vector's certificate: `eqRefl [𝟎]` / `tshvNilCert [𝟎]`. -/
noncomputable def vNilRow (ν : V) : V := if ν = 2 then 116 else 121
def vNilRowDef : 𝚺₀.Semisentence 2 := .mkSigma “y ν. (ν = 2 → y = 116) ∧ (ν ≠ 2 → y = 121)”
instance vNilRow_defined : 𝚺₀-Function₁ (vNilRow : V → V) via vNilRowDef := .mk fun v ↦ by
  simp [vNilRowDef, vNilRow, numeral_eq_natCast]
  by_cases hν : v 1 = 2 <;> simp [hν]
instance vNilRow_definable : 𝚺₀-Function₁ (vNilRow : V → V) := vNilRow_defined.to_definable

noncomputable def vNilSteps (W ν : V) : V := ?[mkStep W (vNilRow ν) ?[(𝟎 : V)]]
noncomputable def vNilStepsDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y W ν. ∃ ρ, !vNilRowDef ρ ν ∧ ∃ e, !mkVec₁Def e ↑Arithmetic.zero ∧ ∃ s, !mkStepDef s W ρ e ∧ !mkVec₁Def y s”
instance vNilSteps_defined : 𝚺₁-Function₂ (vNilSteps : V → V → V) via vNilStepsDef := .mk
  fun v ↦ by simp [vNilStepsDef, vNilSteps, numeral_eq_natCast, vNilRow_defined.iff, mkStep_defined.iff]
instance vNilSteps_definable : 𝚺₁-Function₂ (vNilSteps : V → V → V) := vNilSteps_defined.to_definable

/-- The witnesses of the adjoin certificate at a vector node with `m` tail entries and the entry's count `ct`:
`tshvAdjCert [cT n, cT m, ⟨tail⟩ᵢ, &i, &(i+1), &(j+1), ⟨tail⟩ⱼ, &j]` (`ν = 2`), else
`eqOfAdj [&(i+1), ⟨tail⟩ᵢ, &i, &(j+1), ⟨tail⟩ⱼ, &j]`, with `⟨tail⟩ᵢ = vRef (i + 1 + ct) m`. -/
noncomputable def vAdjWits (ν n m ct i j : V) : V :=
  if ν = 2 then ?[cTV n, cTV m, vRef (i + 1 + ct) m, ^&i, ^&(i + 1), ^&(j + 1), vRef (j + 1 + ct) m, ^&j]
  else ?[^&(i + 1), vRef (i + 1 + ct) m, ^&i, ^&(j + 1), vRef (j + 1 + ct) m, ^&j]

noncomputable def vAdjWitsDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y ν n m ct i j. ∃ fi, !qqFvarDef fi i ∧ ∃ fi', !qqFvarDef fi' (i + 1) ∧ ∃ fj, !qqFvarDef fj j ∧ ∃ fj', !qqFvarDef fj' (j + 1) ∧
    ∃ ri, !vRefDef ri (i + 1 + ct) m ∧ ∃ rj, !vRefDef rj (j + 1 + ct) m ∧ ∃ cn, !cTVGraph cn n ∧ ∃ cm, !cTVGraph cm m ∧
    ∃ a₀, !mkVec₂Def a₀ rj fj ∧ ∃ a₁, !adjoinDef a₁ fj' a₀ ∧ ∃ a₂, !adjoinDef a₂ fi a₁ ∧ ∃ a₃, !adjoinDef a₃ ri a₂ ∧ ∃ a, !adjoinDef a fi' a₃ ∧
    ∃ b₀, !mkVec₂Def b₀ rj fj ∧ ∃ b₁, !adjoinDef b₁ fj' b₀ ∧ ∃ b₂, !adjoinDef b₂ fi' b₁ ∧ ∃ b₃, !adjoinDef b₃ fi b₂ ∧
    ∃ b₄, !adjoinDef b₄ ri b₃ ∧ ∃ b₅, !adjoinDef b₅ cm b₄ ∧ ∃ b, !adjoinDef b cn b₅ ∧
    ((ν = 2 → y = b) ∧ (ν ≠ 2 → y = a))”

instance vAdjWits_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ vAdjWits (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) vAdjWitsDef := .mk
  fun v ↦ by
    simp [vAdjWitsDef, vAdjWits, numeral_eq_natCast, cTV.defined.iff, vRef_defined.iff]
    by_cases hν : v 1 = 2 <;> simp [hν]
instance vAdjWits_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ vAdjWits (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  vAdjWits_defined.to_definable

noncomputable def vAdjRow (ν : V) : V := if ν = 2 then 117 else 127
def vAdjRowDef : 𝚺₀.Semisentence 2 := .mkSigma “y ν. (ν = 2 → y = 117) ∧ (ν ≠ 2 → y = 127)”
instance vAdjRow_defined : 𝚺₀-Function₁ (vAdjRow : V → V) via vAdjRowDef := .mk fun v ↦ by
  simp [vAdjRowDef, vAdjRow, numeral_eq_natCast]
  by_cases hν : v 1 = 2 <;> simp [hν]
instance vAdjRow_definable : 𝚺₀-Function₁ (vAdjRow : V → V) := vAdjRow_defined.to_definable

/-- The vector node's certificate: the entry's pass `yt`, the tail's pass `yv`, the tail's `utvPi` bridge
(rows 38/39 on the source tail), then the adjoin certificate. -/
noncomputable def vAdjSteps (W ν n m ct i j yt yv : V) : V :=
  appendV yt (appendV yv
    ?[mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + ct) m], mkStep W 39 ?[cTV m, vRef (i + 1 + ct) m],
      mkStep W (vAdjRow ν) (vAdjWits ν n m ct i j)])

noncomputable def vAdjStepsDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y W ν n m ct i j yt yv. ∃ cn, !cTVGraph cn n ∧ ∃ cm, !cTVGraph cm m ∧ ∃ ri, !vRefDef ri (i + 1 + ct) m ∧
    ∃ e₁₀, !mkVec₂Def e₁₀ cn ri ∧ ∃ e₁, !adjoinDef e₁ cm e₁₀ ∧ ∃ s₁, !mkStepDef s₁ W 38 e₁ ∧
    ∃ e₂, !mkVec₂Def e₂ cm ri ∧ ∃ s₂, !mkStepDef s₂ W 39 e₂ ∧
    ∃ ρ, !vAdjRowDef ρ ν ∧ ∃ e₃, !vAdjWitsDef e₃ ν n m ct i j ∧ ∃ s₃, !mkStepDef s₃ W ρ e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l, !adjoinDef l s₁ l₂ ∧
    ∃ S, !appendVDef S yv l ∧ !appendVDef y yt S”

instance vAdjSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → V ↦ vAdjSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) vAdjStepsDef := .mk
  fun v ↦ by
    simp [vAdjStepsDef, vAdjSteps, numeral_eq_natCast, cTV.defined.iff, vRef_defined.iff, mkStep_defined.iff,
      vAdjRow_defined.iff, vAdjWits_defined.iff, appendV_defined.iff]
instance vAdjSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 9 → V ↦ vAdjSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  vAdjSteps_defined.to_definable

end termPass

/-! ### 1.1 The fixpoint on `⟪tag, ν, n, x, i, j, y⟫` (`tag = 0`: term `x`; `tag = 1`: `x = ⟪k, v, m⟫`, the
last `m` entries of the vector `v` of length `k`) -/

namespace PassT

/-- The cases of the pass operator on the unpacked tuple (`tg = 0`: term `x`; `tg = 1`: `x = ⟪k, v, m⟫`),
with the bounds the blueprint carries. -/
def Cases (W : V) (C : Set V) (tg ν n x i j y : V) : Prop :=
  (tg = 0 ∧ ∃ z < x, x = ^#z ∧ y = tLeafSteps W ν 0 z i j) ∨
  (tg = 0 ∧ ∃ a < x, x = ^&a ∧ y = tLeafSteps W ν 1 a i j) ∨
  (tg = 0 ∧ ∃ k < x, ∃ f < x, ∃ w < x, x = ^func k f w ∧ ∃ yv ≤ y,
    ⟪1, ν, n, ⟪k, w, k⟫, i + 1, j + 1, yv⟫ ∈ C ∧ y = tFuncSteps W ν k f i j yv) ∨
  (tg = 1 ∧ ∃ k ≤ x, ∃ q ≤ x, x = ⟪k, q⟫ ∧ ∃ v ≤ q, ∃ m ≤ q, q = ⟪v, m⟫ ∧ m = 0 ∧ y = vNilSteps W ν) ∨
  (tg = 1 ∧ ∃ k ≤ x, ∃ q ≤ x, x = ⟪k, q⟫ ∧ ∃ v ≤ q, ∃ m ≤ q, q = ⟪v, m⟫ ∧ ∃ m' < m, m = m' + 1 ∧
    ∃ yt ≤ y, ∃ yv ≤ y, ⟪0, ν, n, nthFromEnd v m', i + 1, j + 1, yt⟫ ∈ C ∧
    ⟪1, ν, n, ⟪k, v, m'⟫, i + 1 + descCountT W n (nthFromEnd v m'), j + 1 + descCountT W n (nthFromEnd v m'), yv⟫ ∈ C ∧
    y = vAdjSteps W ν n m' (descCountT W n (nthFromEnd v m')) i j yt yv)

/-- The pass operator on the packed tuples. -/
def Phi (W : V) (C : Set V) (pr : V) : Prop :=
  ∃ tg ≤ pr, ∃ q₁ ≤ pr, pr = ⟪tg, q₁⟫ ∧ ∃ ν ≤ q₁, ∃ q₂ ≤ q₁, q₁ = ⟪ν, q₂⟫ ∧ ∃ n ≤ q₂, ∃ q₃ ≤ q₂, q₂ = ⟪n, q₃⟫ ∧
  ∃ x ≤ q₃, ∃ q₄ ≤ q₃, q₃ = ⟪x, q₄⟫ ∧ ∃ i ≤ q₄, ∃ q₅ ≤ q₄, q₄ = ⟪i, q₅⟫ ∧ ∃ j ≤ q₅, ∃ y ≤ q₅, q₅ = ⟪j, y⟫ ∧
  Cases W C tg ν n x i j y

/-- `Phi` unpacked: the tuple's components and the cases. -/
lemma phi_unpack (W : V) (C : Set V) (pr : V) :
    Phi W C pr ↔ ∃ tg ν n x i j y, pr = ⟪tg, ν, n, x, i, j, y⟫ ∧ Cases W C tg ν n x i j y := by
  constructor
  · rintro ⟨tg, _, q₁, _, rfl, ν, _, q₂, _, rfl, n, _, q₃, _, rfl, x, _, q₄, _, rfl, i, _, q₅, _, rfl, j, _, y, _, rfl, h⟩
    exact ⟨tg, ν, n, x, i, j, y, rfl, h⟩
  · rintro ⟨tg, ν, n, x, i, j, y, rfl, h⟩
    exact ⟨tg, le_pair_left _ _, _, le_pair_right _ _, rfl, ν, le_pair_left _ _, _, le_pair_right _ _, rfl,
      n, le_pair_left _ _, _, le_pair_right _ _, rfl, x, le_pair_left _ _, _, le_pair_right _ _, rfl,
      i, le_pair_left _ _, _, le_pair_right _ _, rfl, j, le_pair_left _ _, y, le_pair_right _ _, rfl, h⟩

lemma phi_of_cases {W : V} {C : Set V} {tg ν n x i j y : V} (h : Cases W C tg ν n x i j y) :
    Phi W C ⟪tg, ν, n, x, i, j, y⟫ := (phi_unpack W C _).mpr ⟨tg, ν, n, x, i, j, y, rfl, h⟩

lemma cases_of_phi {W : V} {C : Set V} {tg ν n x i j y : V} (h : Phi W C ⟪tg, ν, n, x, i, j, y⟫) :
    Cases W C tg ν n x i j y := by
  obtain ⟨tg', ν', n', x', i', j', y', e, h⟩ := (phi_unpack W C _).mp h
  rw [pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff] at e
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
  exact h

noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma “pr C W.
    ∃ tg <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr tg q₁ ∧ ∃ ν <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ ν q₂ ∧ ∃ n <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ n q₃ ∧
    ∃ x <⁺ q₃, ∃ q₄ <⁺ q₃, !pairDef q₃ x q₄ ∧ ∃ i <⁺ q₄, ∃ q₅ <⁺ q₄, !pairDef q₄ i q₅ ∧ ∃ j <⁺ q₅, ∃ y <⁺ q₅, !pairDef q₅ j y ∧
    ( (tg = 0 ∧ ∃ z < x, !qqBvarDef x z ∧ ∃ s, !tLeafStepsDef s W ν 0 z i j ∧ y = s) ∨
      (tg = 0 ∧ ∃ a < x, !qqFvarDef x a ∧ ∃ s, !tLeafStepsDef s W ν 1 a i j ∧ y = s) ∨
      (tg = 0 ∧ ∃ k < x, ∃ f < x, ∃ w < x, !qqFuncDef x k f w ∧ ∃ yv <⁺ y, ∃ x₁, !pairDef x₁ w k ∧ ∃ x₂, !pairDef x₂ k x₁ ∧
        ∃ r₅, !pairDef r₅ (j + 1) yv ∧ ∃ r₄, !pairDef r₄ (i + 1) r₅ ∧ ∃ r₃, !pairDef r₃ x₂ r₄ ∧ ∃ r₂, !pairDef r₂ n r₃ ∧
        :⟪1, ν, r₂⟫:∈ C ∧ ∃ s, !tFuncStepsDef s W ν k f i j yv ∧ y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ m = 0 ∧ ∃ s, !vNilStepsDef s W ν ∧ y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ ∃ m' < m, m = m' + 1 ∧
        ∃ yt <⁺ y, ∃ yv <⁺ y, ∃ t, !nthFromEndDef t v m' ∧ ∃ ct, !descCountTDef ct W n t ∧
        ∃ p₅, !pairDef p₅ (j + 1) yt ∧ ∃ p₄, !pairDef p₄ (i + 1) p₅ ∧ ∃ p₃, !pairDef p₃ t p₄ ∧ ∃ p₂, !pairDef p₂ n p₃ ∧
        :⟪0, ν, p₂⟫:∈ C ∧ ∃ x₁, !pairDef x₁ v m' ∧ ∃ x₂, !pairDef x₂ k x₁ ∧
        ∃ r₅, !pairDef r₅ (j + 1 + ct) yv ∧ ∃ r₄, !pairDef r₄ (i + 1 + ct) r₅ ∧ ∃ r₃, !pairDef r₃ x₂ r₄ ∧ ∃ r₂, !pairDef r₂ n r₃ ∧
        :⟪1, ν, r₂⟫:∈ C ∧ ∃ s, !vAdjStepsDef s W ν n m' ct i j yt yv ∧ y = s) )”)
  (.mkPi “pr C W.
    ∃ tg <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr tg q₁ ∧ ∃ ν <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ ν q₂ ∧ ∃ n <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ n q₃ ∧
    ∃ x <⁺ q₃, ∃ q₄ <⁺ q₃, !pairDef q₃ x q₄ ∧ ∃ i <⁺ q₄, ∃ q₅ <⁺ q₄, !pairDef q₄ i q₅ ∧ ∃ j <⁺ q₅, ∃ y <⁺ q₅, !pairDef q₅ j y ∧
    ( (tg = 0 ∧ ∃ z < x, !qqBvarDef x z ∧ ∀ s, !tLeafStepsDef s W ν 0 z i j → y = s) ∨
      (tg = 0 ∧ ∃ a < x, !qqFvarDef x a ∧ ∀ s, !tLeafStepsDef s W ν 1 a i j → y = s) ∨
      (tg = 0 ∧ ∃ k < x, ∃ f < x, ∃ w < x, !qqFuncDef x k f w ∧ ∃ yv <⁺ y, ∀ x₁, !pairDef x₁ w k → ∀ x₂, !pairDef x₂ k x₁ →
        ∀ r₅, !pairDef r₅ (j + 1) yv → ∀ r₄, !pairDef r₄ (i + 1) r₅ → ∀ r₃, !pairDef r₃ x₂ r₄ → ∀ r₂, !pairDef r₂ n r₃ →
        :⟪1, ν, r₂⟫:∈ C ∧ ∀ s, !tFuncStepsDef s W ν k f i j yv → y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ m = 0 ∧ ∀ s, !vNilStepsDef s W ν → y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ ∃ m' < m, m = m' + 1 ∧
        ∃ yt <⁺ y, ∃ yv <⁺ y, ∀ t, !nthFromEndDef t v m' → ∀ ct, !descCountTDef ct W n t →
        ∀ p₅, !pairDef p₅ (j + 1) yt → ∀ p₄, !pairDef p₄ (i + 1) p₅ → ∀ p₃, !pairDef p₃ t p₄ → ∀ p₂, !pairDef p₂ n p₃ →
        :⟪0, ν, p₂⟫:∈ C ∧ ∀ x₁, !pairDef x₁ v m' → ∀ x₂, !pairDef x₂ k x₁ →
        ∀ r₅, !pairDef r₅ (j + 1 + ct) yv → ∀ r₄, !pairDef r₄ (i + 1 + ct) r₅ → ∀ r₃, !pairDef r₃ x₂ r₄ → ∀ r₂, !pairDef r₂ n r₃ →
        :⟪1, ν, r₂⟫:∈ C ∧ ∀ s, !vAdjStepsDef s W ν n m' ct i j yt yv → y = s) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, tLeafSteps_defined.iff, tFuncSteps_defined.iff, vNilSteps_defined.iff, vAdjSteps_defined.iff,
        nthFromEnd_defined.iff, descCountT_defined.iff, numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, Cases, tLeafSteps_defined.iff, tFuncSteps_defined.iff, vNilSteps_defined.iff, vAdjSteps_defined.iff,
        nthFromEnd_defined.iff, descCountT_defined.iff, numeral_eq_natCast]
  monotone := by
    intro C C' hC w pr h
    change Phi (w 0) C pr at h
    change Phi (w 0) C' pr
    rw [phi_unpack] at h ⊢
    obtain ⟨tg, ν, n, x, i, j, y, rfl, h⟩ := h
    refine ⟨tg, ν, n, x, i, j, y, rfl, ?_⟩
    rcases h with h | h | ⟨h0, k, hk, f, hf, w', hw, rfl, yv, hyv, h₁, rfl⟩ | h |
      ⟨h1, k, hk, q, hq, rfl, v, hv, m, hm, rfl, m', hm', rfl, yt, hyt, yv, hyv, h₁, h₂, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h0, k, hk, f, hf, w', hw, rfl, yv, hyv, hC h₁, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, k, hk, _, hq, rfl, v, hv, _, hm, rfl, m', hm', rfl, yt, hyt, yv, hyv,
        hC h₁, hC h₂, rfl⟩)))

/-- Every referenced tuple is below the sum of the referenced tuples plus one. -/
instance : construction.Finite V where
  finite := by
    intro C w pr h
    change Phi (w 0) C pr at h
    change ∃ m, Phi (w 0) {y ∈ C | y < m} pr
    rw [phi_unpack] at h
    simp only [phi_unpack]
    obtain ⟨tg, ν, n, x, i, j, y, rfl, h⟩ := h
    rcases h with h | h | ⟨h0, k, hk, f, hf, w', hw, hx', yv, hyv, h₁, hy'⟩ | h |
      ⟨h1, k, hk, q, hq, hx', v, hv, m, hm, hq', m', hm', hmm, yt, hyt, yv, hyv, h₁, h₂, hy'⟩
    · exact ⟨0, tg, ν, n, x, i, j, y, rfl, Or.inl h⟩
    · exact ⟨0, tg, ν, n, x, i, j, y, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨⟪1, ν, n, ⟪k, w', k⟫, i + 1, j + 1, yv⟫ + 1, tg, ν, n, x, i, j, y, rfl,
        Or.inr (Or.inr (Or.inl ⟨h0, k, hk, f, hf, w', hw, hx', yv, hyv, ⟨h₁, lt_add_one _⟩, hy'⟩))⟩
    · exact ⟨0, tg, ν, n, x, i, j, y, rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · refine ⟨⟪0, ν, n, nthFromEnd v m', i + 1, j + 1, yt⟫ +
          ⟪1, ν, n, ⟪k, v, m'⟫, i + 1 + descCountT (w 0) n (nthFromEnd v m'), j + 1 + descCountT (w 0) n (nthFromEnd v m'), yv⟫ + 1,
        tg, ν, n, x, i, j, y, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, k, hk, q, hq, hx', v, hv, m, hm, hq', m', hm', hmm, yt, hyt, yv, hyv,
        ⟨h₁, ?_⟩, ⟨h₂, ?_⟩, hy'⟩)))⟩
      · exact lt_of_le_of_lt le_self_add (lt_add_one _)
      · exact lt_of_le_of_lt le_add_self (lt_add_one _)

/-- `Phi` at a term tuple, the bounds discharged. -/
lemma phi_term_iff (W : V) (C : Set V) (ν n t i j y : V) :
    Phi W C ⟪0, ν, n, t, i, j, y⟫ ↔
    ( (∃ z, t = ^#z ∧ y = tLeafSteps W ν 0 z i j) ∨
      (∃ a, t = ^&a ∧ y = tLeafSteps W ν 1 a i j) ∨
      (∃ k f w yv, t = ^func k f w ∧ yv ≤ y ∧ ⟪1, ν, n, ⟪k, w, k⟫, i + 1, j + 1, yv⟫ ∈ C ∧ y = tFuncSteps W ν k f i j yv) ) := by
  constructor
  · intro h
    rcases cases_of_phi h with ⟨_, z, _, rfl, rfl⟩ | ⟨_, a, _, rfl, rfl⟩ | ⟨_, k, _, f, _, w, _, rfl, yv, hyv, hmem, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl ⟨z, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨a, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨k, f, w, yv, rfl, hyv, hmem, rfl⟩)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · intro h
    refine phi_of_cases ?_
    rcases h with ⟨z, rfl, rfl⟩ | ⟨a, rfl, rfl⟩ | ⟨k, f, w, yv, rfl, hyv, hmem, rfl⟩
    · exact Or.inl ⟨rfl, z, by simp, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, a, by simp, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, k, by simp, f, by simp, w, by simp, rfl, yv, hyv, hmem, rfl⟩))

/-- `Phi` at a vector tuple, the bounds discharged. -/
lemma phi_vec_iff (W : V) (C : Set V) (ν n k v m i j y : V) :
    Phi W C ⟪1, ν, n, ⟪k, v, m⟫, i, j, y⟫ ↔
    ( (m = 0 ∧ y = vNilSteps W ν) ∨
      (∃ m' yt yv, m = m' + 1 ∧ yt ≤ y ∧ yv ≤ y ∧ ⟪0, ν, n, nthFromEnd v m', i + 1, j + 1, yt⟫ ∈ C ∧
        ⟪1, ν, n, ⟪k, v, m'⟫, i + 1 + descCountT W n (nthFromEnd v m'), j + 1 + descCountT W n (nthFromEnd v m'), yv⟫ ∈ C ∧
        y = vAdjSteps W ν n m' (descCountT W n (nthFromEnd v m')) i j yt yv) ) := by
  constructor
  · intro h
    rcases cases_of_phi h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, k', _, q, _, hx, v', _, m'', _, hq, rfl, rfl⟩ |
      ⟨_, k', _, q, _, hx, v', _, m'', _, hq, m', _, rfl, yt, hyt, yv, hyv, hmem₁, hmem₂, rfl⟩
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hx
      obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hq
      exact Or.inl ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hx
      obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hq
      exact Or.inr ⟨m', yt, yv, rfl, hyt, hyv, hmem₁, hmem₂, rfl⟩
  · intro h
    refine phi_of_cases ?_
    rcases h with ⟨rfl, rfl⟩ | ⟨m', yt, yv, rfl, hyt, hyv, hmem₁, hmem₂, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k, le_pair_left _ _, _, le_pair_right _ _, rfl, v, le_pair_left _ _, 0, le_pair_right _ _, rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k, le_pair_left _ _, _, le_pair_right _ _, rfl, v, le_pair_left _ _, m' + 1, le_pair_right _ _, rfl, m',
        lt_add_one _, rfl, yt, hyt, yv, hyv, hmem₁, hmem₂, rfl⟩)))

end PassT

/-- **The graph of the term-level pass** on packed tuples. -/
def PassGraph (W pr : V) : Prop := PassT.construction.Fixpoint ![W] pr
/-- `PassTGraph W ν n t i j y`: the pass of the term `t` (source at `&i`, image at `&j`) is the step list `y`. -/
def PassTGraph (W ν n t i j y : V) : Prop := PassGraph W ⟪0, ν, n, t, i, j, y⟫
/-- `PassVGraph W ν n k v m i j y`: the pass of the last `m` entries of the vector `v` (of length `k`). -/
def PassVGraph (W ν n k v m i j y : V) : Prop := PassGraph W ⟪1, ν, n, ⟪k, v, m⟫, i, j, y⟫

noncomputable def passGraphDef : 𝚺₁.Semisentence 2 := .mkSigma “W pr. !PassT.blueprint.fixpointDef pr W”

-- TRAP (2026-09-14): a full `simp [passGraphDef, eval_fixpointDef, PassGraph]` HANGS here (the
-- blueprint has five disjuncts with long `pairDef` chains, and `simp` unfolds all of them; the
-- same one-liner is fine for `Describe`'s smaller `DescF`). Push the substitution through with a
-- targeted `simp only`, then rewrite with `eval_fixpointDef` — 40 s.
instance passGraph_defined : 𝚺₁-Relation (PassGraph : V → V → Prop) via passGraphDef := .mk
  fun v ↦ by
    simp only [passGraphDef, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.constant_eq_singleton]
    rw [PassT.construction.eval_fixpointDef]
    rfl
instance passGraph_definable : 𝚺₁-Relation (PassGraph : V → V → Prop) := passGraph_defined.to_definable

noncomputable def passTGraphDef : 𝚺₁.Semisentence 7 := .mkSigma
  “W ν n t i j y. ∃ q₅, !pairDef q₅ j y ∧ ∃ q₄, !pairDef q₄ i q₅ ∧ ∃ q₃, !pairDef q₃ t q₄ ∧ ∃ q₂, !pairDef q₂ n q₃ ∧
    ∃ q₁, !pairDef q₁ ν q₂ ∧ ∃ pr, !pairDef pr 0 q₁ ∧ !passGraphDef W pr”
noncomputable def passVGraphDef : 𝚺₁.Semisentence 9 := .mkSigma
  “W ν n k v m i j y. ∃ x₁, !pairDef x₁ v m ∧ ∃ x, !pairDef x k x₁ ∧
    ∃ q₅, !pairDef q₅ j y ∧ ∃ q₄, !pairDef q₄ i q₅ ∧ ∃ q₃, !pairDef q₃ x q₄ ∧ ∃ q₂, !pairDef q₂ n q₃ ∧
    ∃ q₁, !pairDef q₁ ν q₂ ∧ ∃ pr, !pairDef pr 1 q₁ ∧ !passGraphDef W pr”

instance passTGraph_defined :
    𝚺₁.Defined (fun v : Fin 7 → V ↦ PassTGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) passTGraphDef := .mk
  fun v ↦ by simp [passTGraphDef, passGraph_defined.iff, PassTGraph, numeral_eq_natCast]
instance passTGraph_definable :
    𝚺₁.Definable (fun v : Fin 7 → V ↦ PassTGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  passTGraph_defined.to_definable
instance passVGraph_defined :
    𝚺₁.Defined (fun v : Fin 9 → V ↦ PassVGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) passVGraphDef := .mk
  fun v ↦ by simp [passVGraphDef, passGraph_defined.iff, PassVGraph, numeral_eq_natCast]
instance passVGraph_definable :
    𝚺₁.Definable (fun v : Fin 9 → V ↦ PassVGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  passVGraph_defined.to_definable

/-! ### 1.2 Case analysis, inversion, existence and uniqueness -/

lemma PassTGraph.case_iff {W ν n t i j y : V} :
    PassTGraph W ν n t i j y ↔
    ( (∃ z, t = ^#z ∧ y = tLeafSteps W ν 0 z i j) ∨
      (∃ a, t = ^&a ∧ y = tLeafSteps W ν 1 a i j) ∨
      (∃ k f w yv, t = ^func k f w ∧ yv ≤ y ∧ PassVGraph W ν n k w k (i + 1) (j + 1) yv ∧
        y = tFuncSteps W ν k f i j yv) ) := by
  unfold PassTGraph PassVGraph PassGraph
  rw [PassT.construction.case]
  exact PassT.phi_term_iff W _ ν n t i j y

lemma PassVGraph.case_iff {W ν n k v m i j y : V} :
    PassVGraph W ν n k v m i j y ↔
    ( (m = 0 ∧ y = vNilSteps W ν) ∨
      (∃ m' yt yv, m = m' + 1 ∧ yt ≤ y ∧ yv ≤ y ∧ PassTGraph W ν n (nthFromEnd v m') (i + 1) (j + 1) yt ∧
        PassVGraph W ν n k v m' (i + 1 + descCountT W n (nthFromEnd v m')) (j + 1 + descCountT W n (nthFromEnd v m')) yv ∧
        y = vAdjSteps W ν n m' (descCountT W n (nthFromEnd v m')) i j yt yv) ) := by
  unfold PassTGraph PassVGraph PassGraph
  rw [PassT.construction.case]
  exact PassT.phi_vec_iff W _ ν n k v m i j y

section inversion

attribute [local simp] qqBvar qqFvar qqFunc

lemma PassTGraph.bvar_iff {W ν n z i j y : V} : PassTGraph W ν n (^#z) i j y ↔ y = tLeafSteps W ν 0 z i j := by
  rw [PassTGraph.case_iff]; simp
lemma PassTGraph.fvar_iff {W ν n a i j y : V} : PassTGraph W ν n (^&a) i j y ↔ y = tLeafSteps W ν 1 a i j := by
  rw [PassTGraph.case_iff]; simp
lemma PassTGraph.func_iff {W ν n k f w i j y : V} :
    PassTGraph W ν n (^func k f w) i j y ↔
    ∃ yv, yv ≤ y ∧ PassVGraph W ν n k w k (i + 1) (j + 1) yv ∧ y = tFuncSteps W ν k f i j yv := by
  rw [PassTGraph.case_iff]; simp
lemma PassVGraph.zero_iff {W ν n k v i j y : V} : PassVGraph W ν n k v 0 i j y ↔ y = vNilSteps W ν := by
  rw [PassVGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨m', _, _, h, _⟩)
    · rfl
    · exact absurd h.symm (succ_ne_zero' m')
  · intro h; exact Or.inl ⟨rfl, h⟩
lemma PassVGraph.succ_iff {W ν n k v m i j y : V} :
    PassVGraph W ν n k v (m + 1) i j y ↔
    ∃ yt yv, yt ≤ y ∧ yv ≤ y ∧ PassTGraph W ν n (nthFromEnd v m) (i + 1) (j + 1) yt ∧
      PassVGraph W ν n k v m (i + 1 + descCountT W n (nthFromEnd v m)) (j + 1 + descCountT W n (nthFromEnd v m)) yv ∧
      y = vAdjSteps W ν n m (descCountT W n (nthFromEnd v m)) i j yt yv := by
  rw [PassVGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨m', yt, yv, h, hyt, hyv, h₁, h₂, rfl⟩)
    · exact absurd h (succ_ne_zero' m)
    · obtain rfl : m = m' := add_right_cancel h
      exact ⟨yt, yv, hyt, hyv, h₁, h₂, rfl⟩
  · rintro ⟨yt, yv, hyt, hyv, h₁, h₂, rfl⟩
    exact Or.inr ⟨m, yt, yv, rfl, hyt, hyv, h₁, h₂, rfl⟩

end inversion

lemma le_tFuncSteps (W ν k f i j yv : V) : yv ≤ tFuncSteps W ν k f i j yv := le_appendV_left _ _
lemma le_vAdjSteps_left (W ν n m ct i j yt yv : V) : yt ≤ vAdjSteps W ν n m ct i j yt yv := le_appendV_left _ _
lemma le_vAdjSteps_right (W ν n m ct i j yt yv : V) : yv ≤ vAdjSteps W ν n m ct i j yt yv :=
  le_trans (le_appendV_left _ _) (le_appendV_right _ _)

/-- **Existence**, with the offsets bounded by a parameter `B` (the motive must be Σ₁): the pass of `t` at
`(i, j)` exists whenever `i + descCountT t ≤ B` and `j + descCountT t ≤ B`. -/
lemma passTGraph_exists_bounded (W ν n B : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i ≤ B, ∀ j ≤ B, i + descCountT W n t ≤ B → j + descCountT W n t ≤ B → ∃ y, PassTGraph W ν n t i j y := by
  refine IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_
  · definability
  · intro z _ i _ j _ _ _; exact ⟨_, PassTGraph.bvar_iff.mpr rfl⟩
  · intro a i _ j _ _ _; exact ⟨_, PassTGraph.fvar_iff.mpr rfl⟩
  · intro k f v hkf hv ih i hi j hj hiB hjB
    have hk := arity_le_two hkf
    rw [descCountT_func W n hkf hv.isUTerm] at hiB hjB
    -- the vector level, by induction on the number of entries from the end
    have key : ∀ m ≤ k, ∀ i ≤ B, ∀ j ≤ B, i + π₁ (descVecAux W n (descTVec W n k v) m) ≤ B →
        j + π₁ (descVecAux W n (descTVec W n k v) m) ≤ B → ∃ yv, PassVGraph W ν n k v m i j yv := by
      intro m
      induction m using ISigma1.sigma1_succ_induction with
      | hP => definability
      | zero => intro _ i _ j _ _ _; exact ⟨_, PassVGraph.zero_iff.mpr rfl⟩
      | succ m ihm =>
        intro hm i hi j hj hiB hjB
        have hvlen : len v = k := hv.lh
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have hnth : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec W n hv.isUTerm hlt]
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        have hC : π₁ (descVecAux W n (descTVec W n k v) (m + 1)) =
            π₁ (descVecAux W n (descTVec W n k v) m) + descCountT W n v.[k - (m + 1)] + 1 := by
          rw [descVecAux_succ, hnth, adjNode, pi₁_pair]; rfl
        rw [hC] at hiB hjB
        set ct := descCountT W n v.[k - (m + 1)] with hct
        set cv := π₁ (descVecAux W n (descTVec W n k v) m) with hcv
        have hiB' : i + 1 + ct ≤ B :=
          le_trans (le_trans (le_of_eq (by rw [add_assoc, add_comm 1 ct]))
            (add_le_add (le_refl i) (add_le_add le_add_self (le_refl 1)))) hiB
        have hjB' : j + 1 + ct ≤ B :=
          le_trans (le_trans (le_of_eq (by rw [add_assoc, add_comm 1 ct]))
            (add_le_add (le_refl j) (add_le_add le_add_self (le_refl 1)))) hjB
        obtain ⟨yt, hyt⟩ := ih _ hlt (i + 1) (le_trans le_self_add hiB') (j + 1) (le_trans le_self_add hjB') hiB' hjB'
        obtain ⟨yv, hyv⟩ := ihm (le_trans le_self_add hm) (i + 1 + ct) hiB' (j + 1 + ct) hjB'
          (le_trans (le_of_eq (by
            rw [add_assoc, add_assoc, add_comm ct cv, add_comm 1 (cv + ct), ← add_assoc])) hiB)
          (le_trans (le_of_eq (by
            rw [add_assoc, add_assoc, add_comm ct cv, add_comm 1 (cv + ct), ← add_assoc])) hjB)
        refine ⟨_, PassVGraph.succ_iff.mpr ⟨yt, yv, le_vAdjSteps_left _ _ _ _ _ _ _ _ _, le_vAdjSteps_right _ _ _ _ _ _ _ _ _,
          ?_, ?_, rfl⟩⟩
        · rw [hnth']; exact hyt
        · rw [hnth']; exact hyv
    obtain ⟨yv, hyv⟩ := key k le_rfl (i + 1) (le_trans (add_le_add (le_refl i) le_add_self) hiB) (j + 1)
      (le_trans (add_le_add (le_refl j) le_add_self) hjB)
      (le_trans (le_of_eq (by rw [add_assoc, add_comm 1])) hiB)
      (le_trans (le_of_eq (by rw [add_assoc, add_comm 1])) hjB)
    exact ⟨_, PassTGraph.func_iff.mpr ⟨yv, le_tFuncSteps _ _ _ _ _ _ _, hyv, rfl⟩⟩

lemma passTGraph_exists (W ν n : V) {t : V} (ht : IsSemiterm LAct n t) (i j : V) : ∃ y, PassTGraph W ν n t i j y :=
  passTGraph_exists_bounded W ν n (i + j + descCountT W n t) t ht i (le_trans le_self_add le_self_add) j
    (le_trans le_add_self le_self_add) (add_le_add le_self_add (le_refl (descCountT W n t)))
    (add_le_add le_add_self (le_refl (descCountT W n t)))

set_option maxHeartbeats 1000000 in
/-- **Uniqueness of the pass.** The two levels are proved together: the term level by
`IsSemiterm.induction 𝚷` (the motive quantifies over both offsets and both outputs, so it is Π₁),
the vector level by an inner `pi1_succ_induction` on the number of entries still to walk. -/
lemma passTGraph_unique (W ν n : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i j y₁ y₂, PassTGraph W ν n t i j y₁ → PassTGraph W ν n t i j y₂ → y₁ = y₂ := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z _ i j y₁ y₂ h₁ h₂
    rw [PassTGraph.bvar_iff] at h₁ h₂; rw [h₁, h₂]
  · intro a i j y₁ y₂ h₁ h₂
    rw [PassTGraph.fvar_iff] at h₁ h₂; rw [h₁, h₂]
  · intro k f v hkf hv ih i j y₁ y₂ h₁ h₂
    have hvlen : len v = k := hv.lh
    have key : ∀ m ≤ k, ∀ i j z₁ z₂, PassVGraph W ν n k v m i j z₁ → PassVGraph W ν n k v m i j z₂ → z₁ = z₂ := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero =>
        intro _ i j z₁ z₂ hz₁ hz₂
        rw [PassVGraph.zero_iff] at hz₁ hz₂; rw [hz₁, hz₂]
      | succ m ihm =>
        intro hm i j z₁ z₂ hz₁ hz₂
        obtain ⟨yt, yv, _, _, ht, hvv, rfl⟩ := PassVGraph.succ_iff.mp hz₁
        obtain ⟨yt', yv', _, _, ht', hvv', rfl⟩ := PassVGraph.succ_iff.mp hz₂
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        rw [hnth'] at ht ht' hvv hvv'
        rw [ih _ hlt (i + 1) (j + 1) yt yt' ht ht',
          ihm (le_trans le_self_add hm) _ _ yv yv' hvv hvv']
    obtain ⟨yv, _, hyv, rfl⟩ := PassTGraph.func_iff.mp h₁
    obtain ⟨yv', _, hyv', rfl⟩ := PassTGraph.func_iff.mp h₂
    rw [key k le_rfl (i + 1) (j + 1) yv yv' hyv hyv']

set_option maxHeartbeats 1000000 in
/-- **Uniqueness at the vector level** (the shape the fragments use directly). -/
lemma passVGraph_unique {W ν n k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, ∀ i j y₁ y₂, PassVGraph W ν n k v m i j y₁ → PassVGraph W ν n k v m i j y₂ → y₁ = y₂ := by
  have hvlen : len v = k := hv.lh
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _ i j z₁ z₂ hz₁ hz₂
    rw [PassVGraph.zero_iff] at hz₁ hz₂; rw [hz₁, hz₂]
  | succ m ihm =>
    intro hm i j z₁ z₂ hz₁ hz₂
    obtain ⟨yt, yv, _, _, ht, hvv, rfl⟩ := PassVGraph.succ_iff.mp hz₁
    obtain ⟨yt', yv', _, _, ht', hvv', rfl⟩ := PassVGraph.succ_iff.mp hz₂
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    rw [hnth'] at ht ht' hvv hvv'
    rw [passTGraph_unique W ν n _ (hv.nth hlt) (i + 1) (j + 1) yt yt' ht ht',
      ihm (le_trans le_self_add hm) _ _ yv yv' hvv hvv']

/-- **Existence at the vector level**, from the term level. The motive must be Σ₁, so the
offsets are bounded quantifiers; as at the term level (`passTGraph_exists_bounded`) the bound `B`
must dominate the offsets the descent reaches, i.e. `i + cv ≤ B` and `j + cv ≤ B` for
`cv = π₁ (descVecAux …)` the vector's own eigenvariable count. -/
lemma passVGraph_exists_bounded (W ν n B : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, ∀ i ≤ B, ∀ j ≤ B, i + π₁ (descVecAux W n (descTVec W n k v) m) ≤ B →
      j + π₁ (descVecAux W n (descTVec W n k v) m) ≤ B → ∃ y, PassVGraph W ν n k v m i j y := by
  have hvlen : len v = k := hv.lh
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _ i _ j _ _ _; exact ⟨_, PassVGraph.zero_iff.mpr rfl⟩
  | succ m ihm =>
    intro hm i hi j hj hiB hjB
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hnth : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
      rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
        nth_descTVec W n hv.isUTerm hlt]
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    have hC : π₁ (descVecAux W n (descTVec W n k v) (m + 1)) =
        π₁ (descVecAux W n (descTVec W n k v) m) + descCountT W n v.[k - (m + 1)] + 1 := by
      rw [descVecAux_succ, hnth, adjNode, pi₁_pair]; rfl
    rw [hC] at hiB hjB
    set ct := descCountT W n v.[k - (m + 1)] with hct
    set cv := π₁ (descVecAux W n (descTVec W n k v) m) with hcv
    have hiB' : i + 1 + ct ≤ B :=
      le_trans (le_trans (le_of_eq (by rw [add_assoc, add_comm 1 ct]))
        (add_le_add (le_refl i) (add_le_add le_add_self (le_refl 1)))) hiB
    have hjB' : j + 1 + ct ≤ B :=
      le_trans (le_trans (le_of_eq (by rw [add_assoc, add_comm 1 ct]))
        (add_le_add (le_refl j) (add_le_add le_add_self (le_refl 1)))) hjB
    obtain ⟨yt, hyt⟩ := passTGraph_exists W ν n (hv.nth hlt) (i + 1) (j + 1)
    obtain ⟨yv, hyv⟩ := ihm (le_trans le_self_add hm) (i + 1 + ct) hiB' (j + 1 + ct) hjB'
      (le_trans (le_of_eq (by rw [add_assoc, add_assoc, add_comm ct cv, add_comm 1 (cv + ct), ← add_assoc])) hiB)
      (le_trans (le_of_eq (by rw [add_assoc, add_assoc, add_comm ct cv, add_comm 1 (cv + ct), ← add_assoc])) hjB)
    refine ⟨_, PassVGraph.succ_iff.mpr ⟨yt, yv, le_vAdjSteps_left _ _ _ _ _ _ _ _ _,
      le_vAdjSteps_right _ _ _ _ _ _ _ _ _, ?_, ?_, rfl⟩⟩
    · rw [hnth']; exact hyt
    · rw [hnth']; exact hyv

lemma passVGraph_exists (W ν n : V) {k v : V} (hv : IsSemitermVec LAct k n v)
    {m : V} (hm : m ≤ k) (i j : V) : ∃ y, PassVGraph W ν n k v m i j y := by
  set cv := π₁ (descVecAux W n (descTVec W n k v) m) with hcv
  exact passVGraph_exists_bounded W ν n (i + j + cv) hv m hm i (le_trans le_self_add le_self_add) j
    (le_trans le_add_self le_self_add) (add_le_add le_self_add (le_refl cv)) (add_le_add le_add_self (le_refl cv))

lemma passVGraph_existsUnique_total (W ν n k v m i j : V) :
    ∃! y, ((IsSemitermVec LAct k n v ∧ m ≤ k) → PassVGraph W ν n k v m i j y) ∧
      (¬(IsSemitermVec LAct k n v ∧ m ≤ k) → y = 0) := by
  by_cases h : IsSemitermVec LAct k n v ∧ m ≤ k
  · obtain ⟨y, hy⟩ := passVGraph_exists W ν n h.1 h.2 i j
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ passVGraph_unique h.1 m h.2 i j y' y hy' hy)
  · simp [h]

/-- **The vector-level certification pass as a function** (`0` off semiterm vectors / oversized `m`). -/
noncomputable def passV (W ν n k v m i j : V) : V :=
  Classical.choose! (passVGraph_existsUnique_total W ν n k v m i j)

theorem passV_graph {W ν n k v m i j : V} (hv : IsSemitermVec LAct k n v) (hm : m ≤ k) :
    PassVGraph W ν n k v m i j (passV W ν n k v m i j) :=
  (Classical.choose!_spec (passVGraph_existsUnique_total W ν n k v m i j)).1 ⟨hv, hm⟩

lemma passV_eq_of_graph {W ν n k v m i j y : V} (hv : IsSemitermVec LAct k n v) (hm : m ≤ k)
    (hy : PassVGraph W ν n k v m i j y) : passV W ν n k v m i j = y :=
  passVGraph_unique hv m hm i j _ _ (passV_graph hv hm) hy

noncomputable def passVDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W ν n k v m i j. ((!(isSemitermVec LAct).pi k n v ∧ m ≤ k) → !passVGraphDef W ν n k v m i j y) ∧
    ((!(isSemitermVec LAct).sigma k n v → k < m) → y = 0)”

instance passV_defined :
    𝚺₁.DefinedFunction (fun w : Fin 8 → V ↦ passV (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) passVDef := .mk
  fun w ↦ by
    simp [passVDef, HierarchySymbol.Semiformula.val_sigma, passVGraph_defined.iff,
      (IsSemitermVec.defined (L := LAct)).proper.iff', (IsSemitermVec.defined (L := LAct)).df, passV,
      Classical.choose!_eq_iff_right]

instance passV_definable :
    𝚺₁.DefinedFunction (fun w : Fin 8 → V ↦ passV (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) passVDef :=
  passV_defined

lemma passTGraph_existsUnique_total (W ν n t i j : V) :
    ∃! y, (IsSemiterm LAct n t → PassTGraph W ν n t i j y) ∧ (¬IsSemiterm LAct n t → y = 0) := by
  by_cases h : IsSemiterm LAct n t
  · obtain ⟨y, hy⟩ := passTGraph_exists W ν n h i j
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ passTGraph_unique W ν n t h i j y' y hy' hy)
  · simp [h]

/-- **The term-level certification pass as a function**: `passT W ν n t i j` is the step list the
pass `ν` (`0` = identification, `2` = shift) emits for the term `t` whose dossier sits at offset
`i` (and the output's at `j`); `0` off semiterms. -/
noncomputable def passT (W ν n t i j : V) : V := Classical.choose! (passTGraph_existsUnique_total W ν n t i j)

theorem passT_graph {W ν n t i j : V} (h : IsSemiterm LAct n t) : PassTGraph W ν n t i j (passT W ν n t i j) :=
  (Classical.choose!_spec (passTGraph_existsUnique_total W ν n t i j)).1 h

theorem passT_of_not {W ν n t i j : V} (h : ¬IsSemiterm LAct n t) : passT W ν n t i j = 0 :=
  (Classical.choose!_spec (passTGraph_existsUnique_total W ν n t i j)).2 h

lemma passT_eq_of_graph {W ν n t i j y : V} (h : IsSemiterm LAct n t) (hy : PassTGraph W ν n t i j y) :
    passT W ν n t i j = y :=
  passTGraph_unique W ν n t h i j _ _ (passT_graph h) hy

noncomputable def passTDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W ν n t i j. (!(isSemiterm LAct).pi n t → !passTGraphDef W ν n t i j y) ∧
    (¬!(isSemiterm LAct).sigma n t → y = 0)”

instance passT_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ passT (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) passTDef := .mk
  fun v ↦ by
    simp [passTDef, HierarchySymbol.Semiformula.val_sigma, passTGraph_defined.iff,
      (IsSemiterm.defined (L := LAct)).proper.iff', (IsSemiterm.defined (L := LAct)).df, passT,
      Classical.choose!_eq_iff_right]

instance passT_definable :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ passT (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) passTDef :=
  passT_defined

/-! #### The equations of `passT` -/

lemma passT_bvar (W ν n z i j : V) (hz : IsSemiterm LAct n (^#z)) :
    passT W ν n (^#z) i j = tLeafSteps W ν 0 z i j :=
  passT_eq_of_graph hz (PassTGraph.bvar_iff.mpr rfl)

lemma passT_fvar (W ν n a i j : V) : passT W ν n (^&a) i j = tLeafSteps W ν 1 a i j :=
  passT_eq_of_graph (by simp) (PassTGraph.fvar_iff.mpr rfl)

/-! ## Part 2 — the formula-level certification pass (`ν = 1`: `neg`; `ν = 2`: `shift`)

The two families have the SAME shape: at every node ONE Horn step whose antecedents are the
source dossier's shape facts (top at `&i`), the output dossier's shape facts (top at `&j`) and
the children's already-certified `negFact`/`shiftFact` pairs; at an atom the vector level is
supplied by the TERM pass of Part 1 (`ν = 2` emits `passT … 2`; `ν = 1` changes no term, so the
atom row takes the source vector on both sides and no term pass runs). The rows are the generated
`cIdx_neg*Cert` (100–107) and `cIdx_shift*Cert` (108–115) of `CertRows.lean`.
-/

section formulaPass

/-- The row of a `verum`/`falsum`/`and`/`or`/`all`/`exs`/`rel`/`nrel` node, per family
(`ν = 1` → `neg*Cert` at `100 + c`; else `shift*Cert` at `108 + c`), where `c` is the
constructor code `0 = rel, 1 = nrel, 2 = verum, 3 = falsum, 4 = and, 5 = or, 6 = all, 7 = exs`. -/
noncomputable def fRow (ν c : V) : V := if ν = 1 then 100 + c else 108 + c

def fRowDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y ν c. (ν = 1 → y = 100 + c) ∧ (ν ≠ 1 → y = 108 + c)”

instance fRow_defined : 𝚺₀-Function₂ (fRow : V → V → V) via fRowDef := .mk fun v ↦ by
  simp [fRowDef, fRow, numeral_eq_natCast]
  by_cases hν : v 1 = 1 <;> simp [hν]
instance fRow_definable : 𝚺₀-Function₂ (fRow : V → V → V) := fRow_defined.to_definable

/-- The certificate of a `verum` node: `[fRow ν 2 [&i, &j]]` (`negVerumCert`/`shiftVerumCert`). -/
noncomputable def fConstSteps (W ν c i j : V) : V := ?[mkStep W (fRow ν c) ?[^&i, ^&j]]

noncomputable def fConstStepsDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W ν c i j. ∃ ρ, !fRowDef ρ ν c ∧ ∃ fi, !qqFvarDef fi i ∧ ∃ fj, !qqFvarDef fj j ∧
    ∃ e, !mkVec₂Def e fi fj ∧ ∃ s, !mkStepDef s W ρ e ∧ !mkVec₁Def y s”

instance fConstSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ fConstSteps (v 0) (v 1) (v 2) (v 3) (v 4)) fConstStepsDef := .mk
  fun v ↦ by simp [fConstStepsDef, fConstSteps, numeral_eq_natCast, fRow_defined.iff, mkStep_defined.iff]
instance fConstSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 5 → V ↦ fConstSteps (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  fConstSteps_defined.to_definable

/-- The certificate of a binary node after the two children's passes `yp` (LEFT) and `yq` (RIGHT):
`[fRow ν c [cT n, &(i+cq+1), &(i+1), &i, &(j+dq+1), &(j+1), &j]]` — the walk puts the RIGHT child
first (offset `+1`) and the LEFT child above it, so the source's left top is `&(i+cq+1)` for
`cq = descCountF n q`, and likewise `dq` on the output side. -/
noncomputable def fBinSteps (W ν c n cq dq i j yp yq : V) : V :=
  appendV yp (appendV yq
    ?[mkStep W (fRow ν c) ?[cTV n, ^&(i + cq + 1), ^&(i + 1), ^&i, ^&(j + dq + 1), ^&(j + 1), ^&j]])

noncomputable def fBinStepsDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y W ν c n cq dq i j yp yq. ∃ ρ, !fRowDef ρ ν c ∧ ∃ cn, !cTVGraph cn n ∧
    ∃ a₁, !qqFvarDef a₁ (i + cq + 1) ∧ ∃ a₂, !qqFvarDef a₂ (i + 1) ∧ ∃ a₃, !qqFvarDef a₃ i ∧
    ∃ b₁, !qqFvarDef b₁ (j + dq + 1) ∧ ∃ b₂, !qqFvarDef b₂ (j + 1) ∧ ∃ b₃, !qqFvarDef b₃ j ∧
    ∃ e₀, !mkVec₂Def e₀ b₂ b₃ ∧ ∃ e₁, !adjoinDef e₁ b₁ e₀ ∧ ∃ e₂, !adjoinDef e₂ a₃ e₁ ∧
    ∃ e₃, !adjoinDef e₃ a₂ e₂ ∧ ∃ e₄, !adjoinDef e₄ a₁ e₃ ∧ ∃ e, !adjoinDef e cn e₄ ∧
    ∃ s, !mkStepDef s W ρ e ∧ ∃ l, !mkVec₁Def l s ∧ ∃ S, !appendVDef S yq l ∧ !appendVDef y yp S”

instance fBinSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → V ↦ fBinSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) fBinStepsDef := .mk
  fun v ↦ by
    simp [fBinStepsDef, fBinSteps, numeral_eq_natCast, fRow_defined.iff, cTV.defined.iff,
      mkStep_defined.iff, appendV_defined.iff]
instance fBinSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 10 → V ↦ fBinSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  fBinSteps_defined.to_definable

/-- The certificate of a quantifier node after the body's pass `yb`:
`[fRow ν c [cT n, &(i+1), &i, &(j+1), &j]]` (`negAllCert`/`shiftAllCert` shape). -/
noncomputable def fQuantSteps (W ν c n i j yb : V) : V :=
  appendV yb ?[mkStep W (fRow ν c) ?[cTV n, ^&(i + 1), ^&i, ^&(j + 1), ^&j]]

noncomputable def fQuantStepsDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W ν c n i j yb. ∃ ρ, !fRowDef ρ ν c ∧ ∃ cn, !cTVGraph cn n ∧
    ∃ a₁, !qqFvarDef a₁ (i + 1) ∧ ∃ a₂, !qqFvarDef a₂ i ∧ ∃ b₁, !qqFvarDef b₁ (j + 1) ∧ ∃ b₂, !qqFvarDef b₂ j ∧
    ∃ e₀, !mkVec₂Def e₀ b₁ b₂ ∧ ∃ e₁, !adjoinDef e₁ a₂ e₀ ∧ ∃ e₂, !adjoinDef e₂ a₁ e₁ ∧ ∃ e, !adjoinDef e cn e₂ ∧
    ∃ s, !mkStepDef s W ρ e ∧ ∃ l, !mkVec₁Def l s ∧ !appendVDef y yb l”

instance fQuantSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ fQuantSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) fQuantStepsDef := .mk
  fun v ↦ by
    simp [fQuantStepsDef, fQuantSteps, numeral_eq_natCast, fRow_defined.iff, cTV.defined.iff,
      mkStep_defined.iff, appendV_defined.iff]
instance fQuantSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ fQuantSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  fQuantSteps_defined.to_definable

/-- The row of the congruence step at a `neg` atom: `congNRel` (137) at a `rel` source (its image is
an `nrel`), `congRel` (136) at an `nrel` source. -/
noncomputable def congRow (c : V) : V := if c = 0 then 137 else 136
def congRowDef : 𝚺₀.Semisentence 2 := .mkSigma “y c. (c = 0 → y = 137) ∧ (c ≠ 0 → y = 136)”
instance congRow_defined : 𝚺₀-Function₁ (congRow : V → V) via congRowDef := .mk fun v ↦ by
  simp [congRowDef, congRow, numeral_eq_natCast]
  by_cases hc : v 1 = 0 <;> simp [hc]
instance congRow_definable : 𝚺₀-Function₁ (congRow : V → V) := congRow_defined.to_definable

/-- The certificate of an ATOM (`rel`/`nrel`), after the term-level vector pass `yv` at `(i+1, j+1)`:
the closed relation-symbol row (`relRow R`, delivering `isRelFact`), then the family's row.
`ν = 2` (`shift`): `yv` is the SHIFT pass (`tshvFact ⟨v⟩ⱼ (cT k) ⟨v⟩ᵢ`) and the row is
`shiftRelCert [&i, cT k, cT R, ⟨v⟩ᵢ, ⟨v⟩ⱼ, &j]`. `ν = 1` (`neg`): `neg` changes no term, but the
image's dossier was walked AFRESH, so its atom fact names the image's OWN vector `⟨v⟩ⱼ`; `yv` is
therefore the IDENTIFICATION pass (`eqFactB ⟨v⟩ᵢ ⟨v⟩ⱼ`), followed by `eqRefl [&j]` and
`congNRel/congRel [&j, cT k, cT R, ⟨v⟩ⱼ, &j, ⟨v⟩ᵢ]` (moving the image's fact onto the source's
vector), and only then `negRelCert [&i, cT k, cT R, ⟨v⟩ᵢ, &j]`. (Until 2026-09-14 the `ν = 1`
branch was the single `negRelCert` step over the source vector, whose `nrelFact &j … ⟨v⟩ᵢ`
antecedent is NOT in the image's dossier — `certNeg_ok` was unprovable as designed.) -/
noncomputable def fAtomSteps (W ν c k R i j yv : V) : V :=
  if ν = 1 then
    appendV yv ?[mkStep W (relRow R) 0, mkStep W 121 ?[^&j],
      mkStep W (congRow c) ?[^&j, cTV k, cTV R, vRef (j + 1) k, ^&j, vRef (i + 1) k],
      mkStep W (fRow ν c) ?[^&i, cTV k, cTV R, vRef (i + 1) k, ^&j]]
  else appendV yv ?[mkStep W (relRow R) 0, mkStep W (fRow ν c) ?[^&i, cTV k, cTV R, vRef (i + 1) k, vRef (j + 1) k, ^&j]]

noncomputable def fAtomStepsDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W ν c k R i j yv. ∃ ρ, !fRowDef ρ ν c ∧ ∃ ρr, !relRowDef ρr R ∧ ∃ sr, !mkStepDef sr W ρr 0 ∧ ∃ ρc, !congRowDef ρc c ∧
    ∃ ck, !cTVGraph ck k ∧ ∃ cR, !cTVGraph cR R ∧
    ∃ fi, !qqFvarDef fi i ∧ ∃ fj, !qqFvarDef fj j ∧ ∃ ri, !vRefDef ri (i + 1) k ∧ ∃ rj, !vRefDef rj (j + 1) k ∧
    ∃ a₀, !mkVec₂Def a₀ ri fj ∧ ∃ a₁, !adjoinDef a₁ cR a₀ ∧ ∃ a₂, !adjoinDef a₂ ck a₁ ∧ ∃ a, !adjoinDef a fi a₂ ∧
    ∃ sa, !mkStepDef sa W ρ a ∧
    ∃ e₀, !mkVec₁Def e₀ fj ∧ ∃ se, !mkStepDef se W 121 e₀ ∧
    ∃ g₀, !mkVec₂Def g₀ fj ri ∧ ∃ g₁, !adjoinDef g₁ rj g₀ ∧ ∃ g₂, !adjoinDef g₂ cR g₁ ∧ ∃ g₃, !adjoinDef g₃ ck g₂ ∧
    ∃ g, !adjoinDef g fj g₃ ∧ ∃ sg, !mkStepDef sg W ρc g ∧
    ∃ la₃, !mkVec₁Def la₃ sa ∧ ∃ la₂, !adjoinDef la₂ sg la₃ ∧ ∃ la₁, !adjoinDef la₁ se la₂ ∧ ∃ la, !adjoinDef la sr la₁ ∧
    ∃ A, !appendVDef A yv la ∧
    ∃ b₀, !mkVec₂Def b₀ rj fj ∧ ∃ b₁, !adjoinDef b₁ ri b₀ ∧ ∃ b₂, !adjoinDef b₂ cR b₁ ∧ ∃ b₃, !adjoinDef b₃ ck b₂ ∧
    ∃ b, !adjoinDef b fi b₃ ∧ ∃ sb, !mkStepDef sb W ρ b ∧ ∃ lb₁, !mkVec₁Def lb₁ sb ∧ ∃ lb, !adjoinDef lb sr lb₁ ∧
    ∃ B, !appendVDef B yv lb ∧
    ((ν = 1 → y = A) ∧ (ν ≠ 1 → y = B))”

instance fAtomSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ fAtomSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) fAtomStepsDef := .mk
  fun v ↦ by
    simp [fAtomStepsDef, fAtomSteps, numeral_eq_natCast, fRow_defined.iff, relRow_defined.iff, congRow_defined.iff,
      cTV.defined.iff, vRef_defined.iff, mkStep_defined.iff, appendV_defined.iff]
    by_cases hν : v 2 = 1 <;> simp [hν]
instance fAtomSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 8 → V ↦ fAtomSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  fAtomSteps_defined.to_definable

end formulaPass

/-- The image of a formula code under the pass's family: `neg` at `ν = 1`, `shift` otherwise. -/
noncomputable def imgF (ν r : V) : V := if ν = 1 then neg LAct r else shift LAct r

noncomputable def imgFDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y ν r. ∃ a, !(negGraph LAct) a r ∧ ∃ b, !(shiftGraph LAct) b r ∧ ((ν = 1 → y = a) ∧ (ν ≠ 1 → y = b))”

instance imgF_defined : 𝚺₁-Function₂ (imgF : V → V → V) via imgFDef := .mk fun v ↦ by
  simp [imgFDef, imgF, numeral_eq_natCast, neg.defined.iff, shift.defined.iff]
  by_cases hν : v 1 = 1 <;> simp [hν]
instance imgF_definable : 𝚺₁-Function₂ (imgF : V → V → V) := imgF_defined.to_definable

@[simp] lemma imgF_one (r : V) : imgF 1 r = neg LAct r := by simp [imgF]
lemma imgF_of_ne {ν : V} (h : ν ≠ 1) (r : V) : imgF ν r = shift LAct r := by simp [imgF, h]

/-- The OUTPUT-side count at a node: `descCountF W n (imgF ν r)`. -/
noncomputable def outCount (W ν n r : V) : V := descCountF W n (imgF ν r)

noncomputable def outCountDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W ν n r. ∃ z, !imgFDef z ν r ∧ !descCountFDef y W n z”

instance outCount_defined : 𝚺₁-Function₄ (outCount : V → V → V → V → V) via outCountDef := .mk fun v ↦ by
  simp [outCountDef, outCount, imgF_defined.iff, descCountF_defined.iff]
instance outCount_definable : 𝚺₁-Function₄ (outCount : V → V → V → V → V) := outCount_defined.to_definable

/-! ### 2.1 The fixpoint on `⟪ν, n, r, i, j, y⟫` -/

namespace PassF

/-- The cases of the formula pass operator (the constructor codes are those of `fRow`). -/
def Cases (W : V) (C : Set V) (ν n r i j y : V) : Prop :=
  (∃ k < r, ∃ R < r, ∃ v < r, r = ^rel k R v ∧ y = fAtomSteps W ν 0 k R i j (passV W ν n k v k (i + 1) (j + 1))) ∨
  (∃ k < r, ∃ R < r, ∃ v < r, r = ^nrel k R v ∧ y = fAtomSteps W ν 1 k R i j (passV W ν n k v k (i + 1) (j + 1))) ∨
  (r = ^⊤ ∧ y = fConstSteps W ν 2 i j) ∨
  (r = ^⊥ ∧ y = fConstSteps W ν 3 i j) ∨
  (∃ p < r, ∃ q < r, r = p ^⋏ q ∧ ∃ yp ≤ y, ∃ yq ≤ y,
    ⟪ν, n, p, i + descCountF W n q + 1, j + outCount W ν n q + 1, yp⟫ ∈ C ∧ ⟪ν, n, q, i + 1, j + 1, yq⟫ ∈ C ∧
    y = fBinSteps W ν 4 n (descCountF W n q) (outCount W ν n q) i j yp yq) ∨
  (∃ p < r, ∃ q < r, r = p ^⋎ q ∧ ∃ yp ≤ y, ∃ yq ≤ y,
    ⟪ν, n, p, i + descCountF W n q + 1, j + outCount W ν n q + 1, yp⟫ ∈ C ∧ ⟪ν, n, q, i + 1, j + 1, yq⟫ ∈ C ∧
    y = fBinSteps W ν 5 n (descCountF W n q) (outCount W ν n q) i j yp yq) ∨
  (∃ p < r, r = ^∀ p ∧ ∃ yb ≤ y, ⟪ν, n + 1, p, i + 1, j + 1, yb⟫ ∈ C ∧ y = fQuantSteps W ν 6 n i j yb) ∨
  (∃ p < r, r = ^∃ p ∧ ∃ yb ≤ y, ⟪ν, n + 1, p, i + 1, j + 1, yb⟫ ∈ C ∧ y = fQuantSteps W ν 7 n i j yb)

/-- The pass operator on the packed tuples. -/
def Phi (W : V) (C : Set V) (pr : V) : Prop :=
  ∃ ν ≤ pr, ∃ q₁ ≤ pr, pr = ⟪ν, q₁⟫ ∧ ∃ n ≤ q₁, ∃ q₂ ≤ q₁, q₁ = ⟪n, q₂⟫ ∧ ∃ r ≤ q₂, ∃ q₃ ≤ q₂, q₂ = ⟪r, q₃⟫ ∧
  ∃ i ≤ q₃, ∃ q₄ ≤ q₃, q₃ = ⟪i, q₄⟫ ∧ ∃ j ≤ q₄, ∃ y ≤ q₄, q₄ = ⟪j, y⟫ ∧ Cases W C ν n r i j y

lemma phi_unpack (W : V) (C : Set V) (pr : V) :
    Phi W C pr ↔ ∃ ν n r i j y, pr = ⟪ν, n, r, i, j, y⟫ ∧ Cases W C ν n r i j y := by
  constructor
  · rintro ⟨ν, _, q₁, _, rfl, n, _, q₂, _, rfl, r, _, q₃, _, rfl, i, _, q₄, _, rfl, j, _, y, _, rfl, h⟩
    exact ⟨ν, n, r, i, j, y, rfl, h⟩
  · rintro ⟨ν, n, r, i, j, y, rfl, h⟩
    exact ⟨ν, le_pair_left _ _, _, le_pair_right _ _, rfl, n, le_pair_left _ _, _, le_pair_right _ _, rfl,
      r, le_pair_left _ _, _, le_pair_right _ _, rfl, i, le_pair_left _ _, _, le_pair_right _ _, rfl,
      j, le_pair_left _ _, y, le_pair_right _ _, rfl, h⟩

lemma phi_of_cases {W : V} {C : Set V} {ν n r i j y : V} (h : Cases W C ν n r i j y) :
    Phi W C ⟪ν, n, r, i, j, y⟫ := (phi_unpack W C _).mpr ⟨ν, n, r, i, j, y, rfl, h⟩

lemma cases_of_phi {W : V} {C : Set V} {ν n r i j y : V} (h : Phi W C ⟪ν, n, r, i, j, y⟫) :
    Cases W C ν n r i j y := by
  obtain ⟨ν', n', r', i', j', y', e, h⟩ := (phi_unpack W C _).mp h
  rw [pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff] at e
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
  exact h

noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma “pr C W.
    ∃ ν <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr ν q₁ ∧ ∃ n <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ n q₂ ∧ ∃ r <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ r q₃ ∧
    ∃ i <⁺ q₃, ∃ q₄ <⁺ q₃, !pairDef q₃ i q₄ ∧ ∃ j <⁺ q₄, ∃ y <⁺ q₄, !pairDef q₄ j y ∧
    ( (∃ k < r, ∃ R < r, ∃ v < r, !qqRelDef r k R v ∧ ∃ yv, !passVDef yv W ν n k v k (i + 1) (j + 1) ∧
        ∃ s, !fAtomStepsDef s W ν 0 k R i j yv ∧ y = s) ∨
      (∃ k < r, ∃ R < r, ∃ v < r, !qqNRelDef r k R v ∧ ∃ yv, !passVDef yv W ν n k v k (i + 1) (j + 1) ∧
        ∃ s, !fAtomStepsDef s W ν 1 k R i j yv ∧ y = s) ∨
      (!qqVerumDef r ∧ ∃ s, !fConstStepsDef s W ν 2 i j ∧ y = s) ∨
      (!qqFalsumDef r ∧ ∃ s, !fConstStepsDef s W ν 3 i j ∧ y = s) ∨
      (∃ p < r, ∃ q < r, !qqAndDef r p q ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, ∃ cq, !descCountFDef cq W n q ∧ ∃ dq, !outCountDef dq W ν n q ∧
        ∃ a₄, !pairDef a₄ (j + dq + 1) yp ∧ ∃ a₃, !pairDef a₃ (i + cq + 1) a₄ ∧ ∃ a₂, !pairDef a₂ p a₃ ∧ ∃ a₁, !pairDef a₁ n a₂ ∧
        :⟪ν, a₁⟫:∈ C ∧ ∃ b₄, !pairDef b₄ (j + 1) yq ∧ ∃ b₃, !pairDef b₃ (i + 1) b₄ ∧ ∃ b₂, !pairDef b₂ q b₃ ∧ ∃ b₁, !pairDef b₁ n b₂ ∧
        :⟪ν, b₁⟫:∈ C ∧ ∃ s, !fBinStepsDef s W ν 4 n cq dq i j yp yq ∧ y = s) ∨
      (∃ p < r, ∃ q < r, !qqOrDef r p q ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, ∃ cq, !descCountFDef cq W n q ∧ ∃ dq, !outCountDef dq W ν n q ∧
        ∃ a₄, !pairDef a₄ (j + dq + 1) yp ∧ ∃ a₃, !pairDef a₃ (i + cq + 1) a₄ ∧ ∃ a₂, !pairDef a₂ p a₃ ∧ ∃ a₁, !pairDef a₁ n a₂ ∧
        :⟪ν, a₁⟫:∈ C ∧ ∃ b₄, !pairDef b₄ (j + 1) yq ∧ ∃ b₃, !pairDef b₃ (i + 1) b₄ ∧ ∃ b₂, !pairDef b₂ q b₃ ∧ ∃ b₁, !pairDef b₁ n b₂ ∧
        :⟪ν, b₁⟫:∈ C ∧ ∃ s, !fBinStepsDef s W ν 5 n cq dq i j yp yq ∧ y = s) ∨
      (∃ p < r, !qqAllDef r p ∧ ∃ yb <⁺ y, ∃ a₄, !pairDef a₄ (j + 1) yb ∧ ∃ a₃, !pairDef a₃ (i + 1) a₄ ∧
        ∃ a₂, !pairDef a₂ p a₃ ∧ ∃ a₁, !pairDef a₁ (n + 1) a₂ ∧ :⟪ν, a₁⟫:∈ C ∧
        ∃ s, !fQuantStepsDef s W ν 6 n i j yb ∧ y = s) ∨
      (∃ p < r, !qqExsDef r p ∧ ∃ yb <⁺ y, ∃ a₄, !pairDef a₄ (j + 1) yb ∧ ∃ a₃, !pairDef a₃ (i + 1) a₄ ∧
        ∃ a₂, !pairDef a₂ p a₃ ∧ ∃ a₁, !pairDef a₁ (n + 1) a₂ ∧ :⟪ν, a₁⟫:∈ C ∧
        ∃ s, !fQuantStepsDef s W ν 7 n i j yb ∧ y = s) )”)
  (.mkPi “pr C W.
    ∃ ν <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr ν q₁ ∧ ∃ n <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ n q₂ ∧ ∃ r <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ r q₃ ∧
    ∃ i <⁺ q₃, ∃ q₄ <⁺ q₃, !pairDef q₃ i q₄ ∧ ∃ j <⁺ q₄, ∃ y <⁺ q₄, !pairDef q₄ j y ∧
    ( (∃ k < r, ∃ R < r, ∃ v < r, !qqRelDef r k R v ∧ ∀ yv, !passVDef yv W ν n k v k (i + 1) (j + 1) →
        ∀ s, !fAtomStepsDef s W ν 0 k R i j yv → y = s) ∨
      (∃ k < r, ∃ R < r, ∃ v < r, !qqNRelDef r k R v ∧ ∀ yv, !passVDef yv W ν n k v k (i + 1) (j + 1) →
        ∀ s, !fAtomStepsDef s W ν 1 k R i j yv → y = s) ∨
      (!qqVerumDef r ∧ ∀ s, !fConstStepsDef s W ν 2 i j → y = s) ∨
      (!qqFalsumDef r ∧ ∀ s, !fConstStepsDef s W ν 3 i j → y = s) ∨
      (∃ p < r, ∃ q < r, !qqAndDef r p q ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, ∀ cq, !descCountFDef cq W n q → ∀ dq, !outCountDef dq W ν n q →
        ∀ a₄, !pairDef a₄ (j + dq + 1) yp → ∀ a₃, !pairDef a₃ (i + cq + 1) a₄ → ∀ a₂, !pairDef a₂ p a₃ → ∀ a₁, !pairDef a₁ n a₂ →
        :⟪ν, a₁⟫:∈ C ∧ ∀ b₄, !pairDef b₄ (j + 1) yq → ∀ b₃, !pairDef b₃ (i + 1) b₄ → ∀ b₂, !pairDef b₂ q b₃ → ∀ b₁, !pairDef b₁ n b₂ →
        :⟪ν, b₁⟫:∈ C ∧ ∀ s, !fBinStepsDef s W ν 4 n cq dq i j yp yq → y = s) ∨
      (∃ p < r, ∃ q < r, !qqOrDef r p q ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, ∀ cq, !descCountFDef cq W n q → ∀ dq, !outCountDef dq W ν n q →
        ∀ a₄, !pairDef a₄ (j + dq + 1) yp → ∀ a₃, !pairDef a₃ (i + cq + 1) a₄ → ∀ a₂, !pairDef a₂ p a₃ → ∀ a₁, !pairDef a₁ n a₂ →
        :⟪ν, a₁⟫:∈ C ∧ ∀ b₄, !pairDef b₄ (j + 1) yq → ∀ b₃, !pairDef b₃ (i + 1) b₄ → ∀ b₂, !pairDef b₂ q b₃ → ∀ b₁, !pairDef b₁ n b₂ →
        :⟪ν, b₁⟫:∈ C ∧ ∀ s, !fBinStepsDef s W ν 5 n cq dq i j yp yq → y = s) ∨
      (∃ p < r, !qqAllDef r p ∧ ∃ yb <⁺ y, ∀ a₄, !pairDef a₄ (j + 1) yb → ∀ a₃, !pairDef a₃ (i + 1) a₄ →
        ∀ a₂, !pairDef a₂ p a₃ → ∀ a₁, !pairDef a₁ (n + 1) a₂ → :⟪ν, a₁⟫:∈ C ∧
        ∀ s, !fQuantStepsDef s W ν 6 n i j yb → y = s) ∨
      (∃ p < r, !qqExsDef r p ∧ ∃ yb <⁺ y, ∀ a₄, !pairDef a₄ (j + 1) yb → ∀ a₃, !pairDef a₃ (i + 1) a₄ →
        ∀ a₂, !pairDef a₂ p a₃ → ∀ a₁, !pairDef a₁ (n + 1) a₂ → :⟪ν, a₁⟫:∈ C ∧
        ∀ s, !fQuantStepsDef s W ν 7 n i j yb → y = s) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, passV_defined.iff, fAtomSteps_defined.iff, fConstSteps_defined.iff,
        fBinSteps_defined.iff, fQuantSteps_defined.iff, descCountF_defined.iff, outCount_defined.iff,
        numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, Cases, passV_defined.iff, fAtomSteps_defined.iff, fConstSteps_defined.iff,
        fBinSteps_defined.iff, fQuantSteps_defined.iff, descCountF_defined.iff, outCount_defined.iff,
        numeral_eq_natCast]
  monotone := by
    intro C C' hC w pr h
    change Phi (w 0) C pr at h
    rw [phi_unpack] at h ⊢
    obtain ⟨ν, n, r, i, j, y, rfl, h⟩ := h
    refine ⟨ν, n, r, i, j, y, rfl, ?_⟩
    rcases h with h | h | h | h |
      ⟨p, hp, q, hq, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ | ⟨p, hp, q, hq, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ |
      ⟨p, hp, rfl, yb, hyb, h₁, rfl⟩ | ⟨p, hp, rfl, yb, hyb, h₁, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, rfl, yp, hyp, yq, hyq, hC h₁, hC h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, rfl, yp, hyp, yq, hyq, hC h₁, hC h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl, yb, hyb, hC h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, rfl, yb, hyb, hC h₁, rfl⟩))))))

instance : construction.Finite V where
  finite := by
    intro C w pr h
    change Phi (w 0) C pr at h
    change ∃ m, Phi (w 0) {y ∈ C | y < m} pr
    rw [phi_unpack] at h
    simp only [phi_unpack]
    obtain ⟨ν, n, r, i, j, y, rfl, h⟩ := h
    rcases h with h | h | h | h |
      ⟨p, hp, q, hq, hr, yp, hyp, yq, hyq, h₁, h₂, hy⟩ | ⟨p, hp, q, hq, hr, yp, hyp, yq, hyq, h₁, h₂, hy⟩ |
      ⟨p, hp, hr, yb, hyb, h₁, hy⟩ | ⟨p, hp, hr, yb, hyb, h₁, hy⟩
    · exact ⟨0, ν, n, r, i, j, y, rfl, Or.inl h⟩
    · exact ⟨0, ν, n, r, i, j, y, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨0, ν, n, r, i, j, y, rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨0, ν, n, r, i, j, y, rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · refine ⟨⟪ν, n, p, i + descCountF (w 0) n q + 1, j + outCount (w 0) ν n q + 1, yp⟫ +
          ⟪ν, n, q, i + 1, j + 1, yq⟫ + 1, ν, n, r, i, j, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, hr, yp, hyp, yq, hyq,
          ⟨h₁, lt_of_le_of_lt le_self_add (lt_add_one _)⟩, ⟨h₂, lt_of_le_of_lt le_add_self (lt_add_one _)⟩, hy⟩))))⟩
    · refine ⟨⟪ν, n, p, i + descCountF (w 0) n q + 1, j + outCount (w 0) ν n q + 1, yp⟫ +
          ⟪ν, n, q, i + 1, j + 1, yq⟫ + 1, ν, n, r, i, j, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, hr, yp, hyp, yq, hyq,
          ⟨h₁, lt_of_le_of_lt le_self_add (lt_add_one _)⟩, ⟨h₂, lt_of_le_of_lt le_add_self (lt_add_one _)⟩, hy⟩)))))⟩
    · exact ⟨⟪ν, n + 1, p, i + 1, j + 1, yb⟫ + 1, ν, n, r, i, j, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨p, hp, hr, yb, hyb, ⟨h₁, lt_add_one _⟩, hy⟩))))))⟩
    · exact ⟨⟪ν, n + 1, p, i + 1, j + 1, yb⟫ + 1, ν, n, r, i, j, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨p, hp, hr, yb, hyb, ⟨h₁, lt_add_one _⟩, hy⟩))))))⟩

/-- `Phi` at a tuple, the bounds discharged. -/
lemma phi_iff (W : V) (C : Set V) (ν n r i j y : V) :
    Phi W C ⟪ν, n, r, i, j, y⟫ ↔
    ( (∃ k R v, r = ^rel k R v ∧ y = fAtomSteps W ν 0 k R i j (passV W ν n k v k (i + 1) (j + 1))) ∨
      (∃ k R v, r = ^nrel k R v ∧ y = fAtomSteps W ν 1 k R i j (passV W ν n k v k (i + 1) (j + 1))) ∨
      (r = ^⊤ ∧ y = fConstSteps W ν 2 i j) ∨
      (r = ^⊥ ∧ y = fConstSteps W ν 3 i j) ∨
      (∃ p q yp yq, r = p ^⋏ q ∧ yp ≤ y ∧ yq ≤ y ∧
        ⟪ν, n, p, i + descCountF W n q + 1, j + outCount W ν n q + 1, yp⟫ ∈ C ∧ ⟪ν, n, q, i + 1, j + 1, yq⟫ ∈ C ∧
        y = fBinSteps W ν 4 n (descCountF W n q) (outCount W ν n q) i j yp yq) ∨
      (∃ p q yp yq, r = p ^⋎ q ∧ yp ≤ y ∧ yq ≤ y ∧
        ⟪ν, n, p, i + descCountF W n q + 1, j + outCount W ν n q + 1, yp⟫ ∈ C ∧ ⟪ν, n, q, i + 1, j + 1, yq⟫ ∈ C ∧
        y = fBinSteps W ν 5 n (descCountF W n q) (outCount W ν n q) i j yp yq) ∨
      (∃ p yb, r = ^∀ p ∧ yb ≤ y ∧ ⟪ν, n + 1, p, i + 1, j + 1, yb⟫ ∈ C ∧ y = fQuantSteps W ν 6 n i j yb) ∨
      (∃ p yb, r = ^∃ p ∧ yb ≤ y ∧ ⟪ν, n + 1, p, i + 1, j + 1, yb⟫ ∈ C ∧ y = fQuantSteps W ν 7 n i j yb) ) := by
  rw [show Phi W C ⟪ν, n, r, i, j, y⟫ ↔ Cases W C ν n r i j y from
    ⟨cases_of_phi, phi_of_cases⟩]
  unfold Cases
  constructor
  · rintro (⟨k, _, R, _, v, _, rfl, rfl⟩ | ⟨k, _, R, _, v, _, rfl, rfl⟩ | h | h |
      ⟨p, _, q, _, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ | ⟨p, _, q, _, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ |
      ⟨p, _, rfl, yb, hyb, h₁, rfl⟩ | ⟨p, _, rfl, yb, hyb, h₁, rfl⟩)
    · exact Or.inl ⟨k, R, v, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k, R, v, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, yb, rfl, hyb, h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, yb, rfl, hyb, h₁, rfl⟩))))))
  · rintro (⟨k, R, v, rfl, rfl⟩ | ⟨k, R, v, rfl, rfl⟩ | h | h |
      ⟨p, q, yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩ | ⟨p, q, yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩ |
      ⟨p, yb, rfl, hyb, h₁, rfl⟩ | ⟨p, yb, rfl, hyb, h₁, rfl⟩)
    · exact Or.inl ⟨k, by simp, R, by simp, v, by simp, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k, by simp, R, by simp, v, by simp, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, yb, hyb, h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, by simp, rfl, yb, hyb, h₁, rfl⟩))))))

end PassF

/-- The fixpoint on the PACKED tuples (kept separate so that instance search never unfolds it —
the `PassGraph` pattern of Part 1). -/
def PassFPacked (W pr : V) : Prop := PassF.construction.Fixpoint ![W] pr

/-- **The graph of the formula-level certification pass**. -/
def PassFGraph (W ν n r i j y : V) : Prop := PassFPacked W ⟪ν, n, r, i, j, y⟫

noncomputable def passFPackedDef : 𝚺₁.Semisentence 2 := .mkSigma “W pr. !PassF.blueprint.fixpointDef pr W”

-- TRAP (2026-09-14): the full `simp [passFPackedDef, eval_fixpointDef, PassFPacked]` HANGS (the
-- eight-disjunct blueprint); the fixed pattern is the one at `passGraph_defined` above.
instance passFPacked_defined : 𝚺₁-Relation (PassFPacked : V → V → Prop) via passFPackedDef := .mk
  fun v ↦ by
    simp only [passFPackedDef, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.constant_eq_singleton]
    rw [PassF.construction.eval_fixpointDef]
    rfl
instance passFPacked_definable : 𝚺₁-Relation (PassFPacked : V → V → Prop) := passFPacked_defined.to_definable

noncomputable def passFGraphDef : 𝚺₁.Semisentence 7 := .mkSigma
  “W ν n r i j y. ∃ q₄, !pairDef q₄ j y ∧ ∃ q₃, !pairDef q₃ i q₄ ∧ ∃ q₂, !pairDef q₂ r q₃ ∧
    ∃ q₁, !pairDef q₁ n q₂ ∧ ∃ pr, !pairDef pr ν q₁ ∧ !passFPackedDef W pr”

instance passFGraph_defined :
    𝚺₁.Defined (fun v : Fin 7 → V ↦ PassFGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) passFGraphDef := .mk
  fun v ↦ by simp [passFGraphDef, passFPacked_defined.iff, PassFGraph]
instance passFGraph_definable :
    𝚺₁.Definable (fun v : Fin 7 → V ↦ PassFGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  passFGraph_defined.to_definable

/-! ### 2.1b The missing `descCountF` equations and the OUTPUT-side counts -/

lemma descCountF_or (W n : V) {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) :
    descCountF W n (p ^⋎ q) = descCountF W n p + descCountF W n q + 1 := by
  rw [descCountF, descFw_or W n hp hq, binNode, pi₁_pair]; rfl
lemma descCountF_exs (W n : V) {p : V} (hp : IsSemiformula LAct (n + 1) p) :
    descCountF W n (^∃ p) = descCountF W (n + 1) p + 1 := by
  rw [descCountF, descFw_exs W n hp, quantNode, pi₁_pair]; rfl
lemma descCountF_falsum (W n : V) : descCountF W n ^⊥ = 1 := by
  rw [descCountF, descFw_falsum, constNode, pi₁_pair]
lemma descCountF_rel (W n : V) {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) :
    descCountF W n (^rel k R v) = π₁ (descVecAux W n (descTVec W n k v) k) + 1 := by
  rw [descCountF, descFw_rel W n hR hv, atomNode, pi₁_pair]
lemma descCountF_nrel (W n : V) {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) :
    descCountF W n (^nrel k R v) = π₁ (descVecAux W n (descTVec W n k v) k) + 1 := by
  rw [descCountF, descFw_nrel W n hR hv, atomNode, pi₁_pair]

/-- The image of an `and` under the pass's family is a binary node with the corresponding children. -/
lemma outCount_and {W ν n p q : V} (hν : ν = 1 ∨ ν = 2) (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) :
    outCount W ν n (p ^⋏ q) = outCount W ν n p + outCount W ν n q + 1 := by
  rcases hν with rfl | rfl
  · simp only [outCount, imgF_one, neg_and hp.isUFormula hq.isUFormula]
    exact descCountF_or W n hp.neg hq.neg
  · simp only [outCount, imgF_of_ne (V := V) (ν := 2) (by simp), shift_and hp.isUFormula hq.isUFormula]
    exact descCountF_and W n hp.shift hq.shift

lemma outCount_or {W ν n p q : V} (hν : ν = 1 ∨ ν = 2) (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) :
    outCount W ν n (p ^⋎ q) = outCount W ν n p + outCount W ν n q + 1 := by
  rcases hν with rfl | rfl
  · simp only [outCount, imgF_one, neg_or hp.isUFormula hq.isUFormula]
    exact descCountF_and W n hp.neg hq.neg
  · simp only [outCount, imgF_of_ne (V := V) (ν := 2) (by simp), shift_or hp.isUFormula hq.isUFormula]
    exact descCountF_or W n hp.shift hq.shift

lemma outCount_all {W ν n p : V} (hν : ν = 1 ∨ ν = 2) (hp : IsSemiformula LAct (n + 1) p) :
    outCount W ν n (^∀ p) = outCount W ν (n + 1) p + 1 := by
  rcases hν with rfl | rfl
  · simp only [outCount, imgF_one, neg_all hp.isUFormula]
    exact descCountF_exs W n hp.neg
  · simp only [outCount, imgF_of_ne (V := V) (ν := 2) (by simp), shift_all hp.isUFormula]
    exact descCountF_all W n hp.shift

lemma outCount_exs {W ν n p : V} (hν : ν = 1 ∨ ν = 2) (hp : IsSemiformula LAct (n + 1) p) :
    outCount W ν n (^∃ p) = outCount W ν (n + 1) p + 1 := by
  rcases hν with rfl | rfl
  · simp only [outCount, imgF_one, neg_ex hp.isUFormula]
    exact descCountF_all W n hp.neg
  · simp only [outCount, imgF_of_ne (V := V) (ν := 2) (by simp), shift_exs hp.isUFormula]
    exact descCountF_exs W n hp.shift

/-! ### 2.2 Case analysis and inversion -/

lemma PassFGraph.case_iff {W ν n r i j y : V} :
    PassFGraph W ν n r i j y ↔
    ( (∃ k R v, r = ^rel k R v ∧ y = fAtomSteps W ν 0 k R i j (passV W ν n k v k (i + 1) (j + 1))) ∨
      (∃ k R v, r = ^nrel k R v ∧ y = fAtomSteps W ν 1 k R i j (passV W ν n k v k (i + 1) (j + 1))) ∨
      (r = ^⊤ ∧ y = fConstSteps W ν 2 i j) ∨
      (r = ^⊥ ∧ y = fConstSteps W ν 3 i j) ∨
      (∃ p q yp yq, r = p ^⋏ q ∧ yp ≤ y ∧ yq ≤ y ∧
        PassFGraph W ν n p (i + descCountF W n q + 1) (j + outCount W ν n q + 1) yp ∧
        PassFGraph W ν n q (i + 1) (j + 1) yq ∧
        y = fBinSteps W ν 4 n (descCountF W n q) (outCount W ν n q) i j yp yq) ∨
      (∃ p q yp yq, r = p ^⋎ q ∧ yp ≤ y ∧ yq ≤ y ∧
        PassFGraph W ν n p (i + descCountF W n q + 1) (j + outCount W ν n q + 1) yp ∧
        PassFGraph W ν n q (i + 1) (j + 1) yq ∧
        y = fBinSteps W ν 5 n (descCountF W n q) (outCount W ν n q) i j yp yq) ∨
      (∃ p yb, r = ^∀ p ∧ yb ≤ y ∧ PassFGraph W ν (n + 1) p (i + 1) (j + 1) yb ∧ y = fQuantSteps W ν 6 n i j yb) ∨
      (∃ p yb, r = ^∃ p ∧ yb ≤ y ∧ PassFGraph W ν (n + 1) p (i + 1) (j + 1) yb ∧ y = fQuantSteps W ν 7 n i j yb) ) := by
  unfold PassFGraph PassFPacked
  rw [PassF.construction.case]
  exact PassF.phi_iff W _ ν n r i j y

section finversion

attribute [local simp] qqRel qqNRel qqVerum qqFalsum qqAnd qqOr qqAll qqExs

lemma PassFGraph.rel_iff {W ν n k R v i j y : V} :
    PassFGraph W ν n (^rel k R v) i j y ↔ y = fAtomSteps W ν 0 k R i j (passV W ν n k v k (i + 1) (j + 1)) := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.nrel_iff {W ν n k R v i j y : V} :
    PassFGraph W ν n (^nrel k R v) i j y ↔ y = fAtomSteps W ν 1 k R i j (passV W ν n k v k (i + 1) (j + 1)) := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.verum_iff {W ν n i j y : V} :
    PassFGraph W ν n ^⊤ i j y ↔ y = fConstSteps W ν 2 i j := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.falsum_iff {W ν n i j y : V} :
    PassFGraph W ν n ^⊥ i j y ↔ y = fConstSteps W ν 3 i j := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.and_iff {W ν n p q i j y : V} :
    PassFGraph W ν n (p ^⋏ q) i j y ↔
    ∃ yp yq, yp ≤ y ∧ yq ≤ y ∧
      PassFGraph W ν n p (i + descCountF W n q + 1) (j + outCount W ν n q + 1) yp ∧
      PassFGraph W ν n q (i + 1) (j + 1) yq ∧
      y = fBinSteps W ν 4 n (descCountF W n q) (outCount W ν n q) i j yp yq := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.or_iff {W ν n p q i j y : V} :
    PassFGraph W ν n (p ^⋎ q) i j y ↔
    ∃ yp yq, yp ≤ y ∧ yq ≤ y ∧
      PassFGraph W ν n p (i + descCountF W n q + 1) (j + outCount W ν n q + 1) yp ∧
      PassFGraph W ν n q (i + 1) (j + 1) yq ∧
      y = fBinSteps W ν 5 n (descCountF W n q) (outCount W ν n q) i j yp yq := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.all_iff {W ν n p i j y : V} :
    PassFGraph W ν n (^∀ p) i j y ↔
    ∃ yb, yb ≤ y ∧ PassFGraph W ν (n + 1) p (i + 1) (j + 1) yb ∧ y = fQuantSteps W ν 6 n i j yb := by
  rw [PassFGraph.case_iff]; simp
lemma PassFGraph.exs_iff {W ν n p i j y : V} :
    PassFGraph W ν n (^∃ p) i j y ↔
    ∃ yb, yb ≤ y ∧ PassFGraph W ν (n + 1) p (i + 1) (j + 1) yb ∧ y = fQuantSteps W ν 7 n i j yb := by
  rw [PassFGraph.case_iff]; simp

end finversion

lemma le_fBinSteps_left (W ν c n cq dq i j yp yq : V) : yp ≤ fBinSteps W ν c n cq dq i j yp yq :=
  le_appendV_left _ _
lemma le_fBinSteps_right (W ν c n cq dq i j yp yq : V) : yq ≤ fBinSteps W ν c n cq dq i j yp yq :=
  le_trans (le_appendV_left _ _) (le_appendV_right _ _)
lemma le_fQuantSteps (W ν c n i j yb : V) : yb ≤ fQuantSteps W ν c n i j yb := le_appendV_left _ _

/-! ### 2.3 Existence, uniqueness, and the function `passF` -/

set_option maxHeartbeats 1000000 in
/-- **Existence**, with the offsets bounded by a parameter `B` (the motive must be Σ₁). -/
lemma passFGraph_exists_bounded (W B : V) {ν : V} (hν : ν = 1 ∨ ν = 2) :
    ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i ≤ B, ∀ j ≤ B, i + descCountF W n r ≤ B → j + outCount W ν n r ≤ B →
      ∃ y, PassFGraph W ν n r i j y := by
  intro n r
  apply IsSemiformula.sigma1_structural_induction
    (P := fun n r ↦ ∀ i ≤ B, ∀ j ≤ B, i + descCountF W n r ≤ B → j + outCount W ν n r ≤ B →
      ∃ y, PassFGraph W ν n r i j y)
  · definability
  · intro n k R v _ _ i _ j _ _ _; exact ⟨_, PassFGraph.rel_iff.mpr rfl⟩
  · intro n k R v _ _ i _ j _ _ _; exact ⟨_, PassFGraph.nrel_iff.mpr rfl⟩
  · intro n i _ j _ _ _; exact ⟨_, PassFGraph.verum_iff.mpr rfl⟩
  · intro n i _ j _ _ _; exact ⟨_, PassFGraph.falsum_iff.mpr rfl⟩
  · intro n p q hp hq ihp ihq i hi j hj hiB hjB
    rw [descCountF_and W n hp hq] at hiB
    rw [outCount_and hν hp hq] at hjB
    set cp := descCountF W n p with hcp
    set cq := descCountF W n q with hcq
    set dp := outCount W ν n p with hdp
    set dq := outCount W ν n q with hdq
    have hcq1 : cq + 1 ≤ cp + cq + 1 := add_le_add le_add_self (le_refl 1)
    have hdq1 : dq + 1 ≤ dp + dq + 1 := add_le_add le_add_self (le_refl 1)
    have hiq : i + 1 + cq ≤ B := le_trans (le_trans (le_of_eq (show i + 1 + cq = i + (cq + 1) by ring))
      (add_le_add (le_refl i) hcq1)) hiB
    have hjq : j + 1 + dq ≤ B := le_trans (le_trans (le_of_eq (show j + 1 + dq = j + (dq + 1) by ring))
      (add_le_add (le_refl j) hdq1)) hjB
    have hip : i + cq + 1 + cp ≤ B := le_trans (le_of_eq (show i + cq + 1 + cp = i + (cp + cq + 1) by ring)) hiB
    have hjp : j + dq + 1 + dp ≤ B := le_trans (le_of_eq (show j + dq + 1 + dp = j + (dp + dq + 1) by ring)) hjB
    obtain ⟨yq, hyq⟩ := ihq (i + 1) (le_trans le_self_add hiq) (j + 1) (le_trans le_self_add hjq) hiq hjq
    obtain ⟨yp, hyp⟩ := ihp (i + cq + 1) (le_trans le_self_add hip) (j + dq + 1) (le_trans le_self_add hjp) hip hjp
    exact ⟨_, PassFGraph.and_iff.mpr ⟨yp, yq, le_fBinSteps_left _ _ _ _ _ _ _ _ _ _,
      le_fBinSteps_right _ _ _ _ _ _ _ _ _ _, hyp, hyq, rfl⟩⟩
  · intro n p q hp hq ihp ihq i hi j hj hiB hjB
    rw [descCountF_or W n hp hq] at hiB
    rw [outCount_or hν hp hq] at hjB
    set cp := descCountF W n p with hcp
    set cq := descCountF W n q with hcq
    set dp := outCount W ν n p with hdp
    set dq := outCount W ν n q with hdq
    have hcq1 : cq + 1 ≤ cp + cq + 1 := add_le_add le_add_self (le_refl 1)
    have hdq1 : dq + 1 ≤ dp + dq + 1 := add_le_add le_add_self (le_refl 1)
    have hiq : i + 1 + cq ≤ B := le_trans (le_trans (le_of_eq (show i + 1 + cq = i + (cq + 1) by ring))
      (add_le_add (le_refl i) hcq1)) hiB
    have hjq : j + 1 + dq ≤ B := le_trans (le_trans (le_of_eq (show j + 1 + dq = j + (dq + 1) by ring))
      (add_le_add (le_refl j) hdq1)) hjB
    have hip : i + cq + 1 + cp ≤ B := le_trans (le_of_eq (show i + cq + 1 + cp = i + (cp + cq + 1) by ring)) hiB
    have hjp : j + dq + 1 + dp ≤ B := le_trans (le_of_eq (show j + dq + 1 + dp = j + (dp + dq + 1) by ring)) hjB
    obtain ⟨yq, hyq⟩ := ihq (i + 1) (le_trans le_self_add hiq) (j + 1) (le_trans le_self_add hjq) hiq hjq
    obtain ⟨yp, hyp⟩ := ihp (i + cq + 1) (le_trans le_self_add hip) (j + dq + 1) (le_trans le_self_add hjp) hip hjp
    exact ⟨_, PassFGraph.or_iff.mpr ⟨yp, yq, le_fBinSteps_left _ _ _ _ _ _ _ _ _ _,
      le_fBinSteps_right _ _ _ _ _ _ _ _ _ _, hyp, hyq, rfl⟩⟩
  · intro n p hp ih i hi j hj hiB hjB
    rw [descCountF_all W n hp] at hiB
    rw [outCount_all hν hp] at hjB
    have hiB' : i + 1 + descCountF W (n + 1) p ≤ B :=
      le_trans (le_of_eq (show i + 1 + descCountF W (n + 1) p = i + (descCountF W (n + 1) p + 1) by ring)) hiB
    have hjB' : j + 1 + outCount W ν (n + 1) p ≤ B :=
      le_trans (le_of_eq (show j + 1 + outCount W ν (n + 1) p = j + (outCount W ν (n + 1) p + 1) by ring)) hjB
    obtain ⟨yb, hyb⟩ := ih (i + 1) (le_trans le_self_add hiB') (j + 1) (le_trans le_self_add hjB') hiB' hjB'
    exact ⟨_, PassFGraph.all_iff.mpr ⟨yb, le_fQuantSteps _ _ _ _ _ _ _, hyb, rfl⟩⟩
  · intro n p hp ih i hi j hj hiB hjB
    rw [descCountF_exs W n hp] at hiB
    rw [outCount_exs hν hp] at hjB
    have hiB' : i + 1 + descCountF W (n + 1) p ≤ B :=
      le_trans (le_of_eq (show i + 1 + descCountF W (n + 1) p = i + (descCountF W (n + 1) p + 1) by ring)) hiB
    have hjB' : j + 1 + outCount W ν (n + 1) p ≤ B :=
      le_trans (le_of_eq (show j + 1 + outCount W ν (n + 1) p = j + (outCount W ν (n + 1) p + 1) by ring)) hjB
    obtain ⟨yb, hyb⟩ := ih (i + 1) (le_trans le_self_add hiB') (j + 1) (le_trans le_self_add hjB') hiB' hjB'
    exact ⟨_, PassFGraph.exs_iff.mpr ⟨yb, le_fQuantSteps _ _ _ _ _ _ _, hyb, rfl⟩⟩

lemma passFGraph_exists (W : V) {ν : V} (hν : ν = 1 ∨ ν = 2) {n r : V} (hr : IsSemiformula LAct n r)
    (i j : V) : ∃ y, PassFGraph W ν n r i j y :=
  passFGraph_exists_bounded W (i + descCountF W n r + (j + outCount W ν n r)) hν hr
    i (le_trans le_self_add le_self_add) j (le_trans le_self_add le_add_self) le_self_add le_add_self

set_option maxHeartbeats 1000000 in
/-- **Uniqueness** of the formula pass (the motive is Π₁: `PassFGraph` is Σ₁ and appears only
in antecedents). -/
lemma passFGraph_unique (W ν : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i j y₁ y₂, PassFGraph W ν n r i j y₁ → PassFGraph W ν n r i j y₂ → y₁ = y₂ := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i j y₁ y₂, PassFGraph W ν n r i j y₁ → PassFGraph W ν n r i j y₂ → y₁ = y₂)
  · definability
  · intro n k R v _ _ i j y₁ y₂ h₁ h₂; rw [PassFGraph.rel_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n k R v _ _ i j y₁ y₂ h₁ h₂; rw [PassFGraph.nrel_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n i j y₁ y₂ h₁ h₂; rw [PassFGraph.verum_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n i j y₁ y₂ h₁ h₂; rw [PassFGraph.falsum_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n p q _ _ ihp ihq i j y₁ y₂ h₁ h₂
    obtain ⟨yp, yq, _, _, hp₁, hq₁, rfl⟩ := PassFGraph.and_iff.mp h₁
    obtain ⟨yp', yq', _, _, hp₂, hq₂, rfl⟩ := PassFGraph.and_iff.mp h₂
    rw [ihp _ _ yp yp' hp₁ hp₂, ihq _ _ yq yq' hq₁ hq₂]
  · intro n p q _ _ ihp ihq i j y₁ y₂ h₁ h₂
    obtain ⟨yp, yq, _, _, hp₁, hq₁, rfl⟩ := PassFGraph.or_iff.mp h₁
    obtain ⟨yp', yq', _, _, hp₂, hq₂, rfl⟩ := PassFGraph.or_iff.mp h₂
    rw [ihp _ _ yp yp' hp₁ hp₂, ihq _ _ yq yq' hq₁ hq₂]
  · intro n p _ ih i j y₁ y₂ h₁ h₂
    obtain ⟨yb, _, hb₁, rfl⟩ := PassFGraph.all_iff.mp h₁
    obtain ⟨yb', _, hb₂, rfl⟩ := PassFGraph.all_iff.mp h₂
    rw [ih _ _ yb yb' hb₁ hb₂]
  · intro n p _ ih i j y₁ y₂ h₁ h₂
    obtain ⟨yb, _, hb₁, rfl⟩ := PassFGraph.exs_iff.mp h₁
    obtain ⟨yb', _, hb₂, rfl⟩ := PassFGraph.exs_iff.mp h₂
    rw [ih _ _ yb yb' hb₁ hb₂]

lemma passFGraph_existsUnique_total (W ν n r i j : V) :
    ∃! y, ((IsSemiformula LAct n r ∧ (ν = 1 ∨ ν = 2)) → PassFGraph W ν n r i j y) ∧
      (¬(IsSemiformula LAct n r ∧ (ν = 1 ∨ ν = 2)) → y = 0) := by
  by_cases h : IsSemiformula LAct n r ∧ (ν = 1 ∨ ν = 2)
  · obtain ⟨y, hy⟩ := passFGraph_exists W h.2 h.1 i j
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ passFGraph_unique W ν h.1 i j y' y hy' hy)
  · simp [h]

/-- **The formula-level certification pass as a function**: for `ν ∈ {1, 2}` (`neg`, `shift`),
the step list certifying `imgF ν r` against `r` when `r`'s dossier is at offset `i` and
`imgF ν r`'s at offset `j`; `0` off semiformulas and off the two families. -/
noncomputable def passF (W ν n r i j : V) : V := Classical.choose! (passFGraph_existsUnique_total W ν n r i j)

theorem passF_graph {W ν n r i j : V} (hν : ν = 1 ∨ ν = 2) (hr : IsSemiformula LAct n r) :
    PassFGraph W ν n r i j (passF W ν n r i j) :=
  (Classical.choose!_spec (passFGraph_existsUnique_total W ν n r i j)).1 ⟨hr, hν⟩

theorem passF_of_not {W ν n r i j : V} (h : ¬(IsSemiformula LAct n r ∧ (ν = 1 ∨ ν = 2))) :
    passF W ν n r i j = 0 :=
  (Classical.choose!_spec (passFGraph_existsUnique_total W ν n r i j)).2 h

lemma passF_eq_of_graph {W ν n r i j y : V} (hν : ν = 1 ∨ ν = 2) (hr : IsSemiformula LAct n r)
    (hy : PassFGraph W ν n r i j y) : passF W ν n r i j = y :=
  passFGraph_unique W ν hr i j _ _ (passF_graph hν hr) hy

noncomputable def passFDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W ν n r i j. ((!(isSemiformula LAct).pi n r ∧ (ν = 1 ∨ ν = 2)) → !passFGraphDef W ν n r i j y) ∧
    ((!(isSemiformula LAct).sigma n r → (ν ≠ 1 ∧ ν ≠ 2)) → y = 0)”

instance passF_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ passF (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) passFDef := .mk
  fun v ↦ by
    simp [passFDef, HierarchySymbol.Semiformula.val_sigma, passFGraph_defined.iff,
      (IsSemiformula.defined (L := LAct)).proper.iff', (IsSemiformula.defined (L := LAct)).df, passF,
      Classical.choose!_eq_iff_right]

instance passF_definable :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ passF (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) passFDef :=
  passF_defined

/-! ### 2.4 The equations of `passF` -/

section passFeq

variable {W ν n : V}

lemma passF_rel (hν : ν = 1 ∨ ν = 2) {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) (i j : V) :
    passF W ν n (^rel k R v) i j = fAtomSteps W ν 0 k R i j (passV W ν n k v k (i + 1) (j + 1)) :=
  passF_eq_of_graph hν (by simp [hR, hv]) (PassFGraph.rel_iff.mpr rfl)

lemma passF_nrel (hν : ν = 1 ∨ ν = 2) {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) (i j : V) :
    passF W ν n (^nrel k R v) i j = fAtomSteps W ν 1 k R i j (passV W ν n k v k (i + 1) (j + 1)) :=
  passF_eq_of_graph hν (by simp [hR, hv]) (PassFGraph.nrel_iff.mpr rfl)

lemma passF_verum (hν : ν = 1 ∨ ν = 2) (i j : V) : passF W ν n ^⊤ i j = fConstSteps W ν 2 i j :=
  passF_eq_of_graph hν (by simp) (PassFGraph.verum_iff.mpr rfl)

lemma passF_falsum (hν : ν = 1 ∨ ν = 2) (i j : V) : passF W ν n ^⊥ i j = fConstSteps W ν 3 i j :=
  passF_eq_of_graph hν (by simp) (PassFGraph.falsum_iff.mpr rfl)

lemma passF_and (hν : ν = 1 ∨ ν = 2) {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) (i j : V) :
    passF W ν n (p ^⋏ q) i j = fBinSteps W ν 4 n (descCountF W n q) (outCount W ν n q) i j
      (passF W ν n p (i + descCountF W n q + 1) (j + outCount W ν n q + 1)) (passF W ν n q (i + 1) (j + 1)) :=
  passF_eq_of_graph hν (by simp [hp, hq]) (PassFGraph.and_iff.mpr
    ⟨_, _, le_fBinSteps_left _ _ _ _ _ _ _ _ _ _, le_fBinSteps_right _ _ _ _ _ _ _ _ _ _,
      passF_graph hν hp, passF_graph hν hq, rfl⟩)

lemma passF_or (hν : ν = 1 ∨ ν = 2) {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) (i j : V) :
    passF W ν n (p ^⋎ q) i j = fBinSteps W ν 5 n (descCountF W n q) (outCount W ν n q) i j
      (passF W ν n p (i + descCountF W n q + 1) (j + outCount W ν n q + 1)) (passF W ν n q (i + 1) (j + 1)) :=
  passF_eq_of_graph hν (by simp [hp, hq]) (PassFGraph.or_iff.mpr
    ⟨_, _, le_fBinSteps_left _ _ _ _ _ _ _ _ _ _, le_fBinSteps_right _ _ _ _ _ _ _ _ _ _,
      passF_graph hν hp, passF_graph hν hq, rfl⟩)

lemma passF_all (hν : ν = 1 ∨ ν = 2) {p : V} (hp : IsSemiformula LAct (n + 1) p) (i j : V) :
    passF W ν n (^∀ p) i j = fQuantSteps W ν 6 n i j (passF W ν (n + 1) p (i + 1) (j + 1)) :=
  passF_eq_of_graph hν (by simp [hp]) (PassFGraph.all_iff.mpr ⟨_, le_fQuantSteps _ _ _ _ _ _ _, passF_graph hν hp, rfl⟩)

lemma passF_exs (hν : ν = 1 ∨ ν = 2) {p : V} (hp : IsSemiformula LAct (n + 1) p) (i j : V) :
    passF W ν n (^∃ p) i j = fQuantSteps W ν 7 n i j (passF W ν (n + 1) p (i + 1) (j + 1)) :=
  passF_eq_of_graph hν (by simp [hp]) (PassFGraph.exs_iff.mpr ⟨_, le_fQuantSteps _ _ _ _ _ _ _, passF_graph hν hp, rfl⟩)

end passFeq

/-! ### 2.5 The two named producers: `certNeg` and `certShift` (§3.6) -/

/-- **`certNeg W n r i j`** — the certification pass of `neg r` (§3.6): with `r`'s walk dossier at
offset `i` and `neg r`'s at offset `j`, the step list whose final context holds `negFact &j &i`. -/
noncomputable def certNeg (W n r i j : V) : V := passF W 1 n r i j

/-- **`certShift W n r i j`** — the certification pass of `shift r` (§3.6): with `r`'s walk dossier
at offset `i` and `shift r`'s at offset `j`, the step list whose final context holds
`shiftFact &j &i`. -/
noncomputable def certShift (W n r i j : V) : V := passF W 2 n r i j

@[simp] lemma certNeg_eq (W n r i j : V) : certNeg W n r i j = passF W 1 n r i j := rfl
@[simp] lemma certShift_eq (W n r i j : V) : certShift W n r i j = passF W 2 n r i j := rfl

lemma certNeg_graph {W n r i j : V} (hr : IsSemiformula LAct n r) :
    PassFGraph W 1 n r i j (certNeg W n r i j) := passF_graph (Or.inl rfl) hr
lemma certShift_graph {W n r i j : V} (hr : IsSemiformula LAct n r) :
    PassFGraph W 2 n r i j (certShift W n r i j) := passF_graph (Or.inr rfl) hr

/-! ### 2.6 The structural invariant: the pass is SHIFT-FREE (`NoDrop`, `shiftsV = 0`)

Every step of a pass is a Horn step (tag `0`), so contexts only grow and the offsets never move.
-/

section passStruct

/-- Every row the formula pass emits is a Horn row (tag `0`). -/
lemma ctag_fRow {W : V} (hWp : W = certPieces) {ν c : V} (hν : ν = 1 ∨ ν = 2)
    (hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7) (ev : V) :
    sTag (mkStep W (fRow ν c) ev) = 0 := by
  have hf : fRow ν c = 100 ∨ fRow ν c = 101 ∨ fRow ν c = 102 ∨ fRow ν c = 103 ∨ fRow ν c = 104 ∨
      fRow ν c = 105 ∨ fRow ν c = 106 ∨ fRow ν c = 107 ∨ fRow ν c = 108 ∨ fRow ν c = 109 ∨
      fRow ν c = 110 ∨ fRow ν c = 111 ∨ fRow ν c = 112 ∨ fRow ν c = 113 ∨ fRow ν c = 114 ∨ fRow ν c = 115 := by
    rcases hν with rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fRow] <;> norm_num
  rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact ctag_negRelCert hWp ev
  · exact ctag_negNRelCert hWp ev
  · exact ctag_negVerumCert hWp ev
  · exact ctag_negFalsumCert hWp ev
  · exact ctag_negAndCert hWp ev
  · exact ctag_negOrCert hWp ev
  · exact ctag_negAllCert hWp ev
  · exact ctag_negExsCert hWp ev
  · exact ctag_shiftRelCert hWp ev
  · exact ctag_shiftNRelCert hWp ev
  · exact ctag_shiftVerumCert hWp ev
  · exact ctag_shiftFalsumCert hWp ev
  · exact ctag_shiftAndCert hWp ev
  · exact ctag_shiftOrCert hWp ev
  · exact ctag_shiftAllCert hWp ev
  · exact ctag_shiftExsCert hWp ev

/-- The two term-level closed-symbol / vector rows the ATOM case appends are Horn rows too. -/
lemma ctag_vNilRow {W : V} (hWp : W = certPieces) {ν : V} (hν : ν = 1 ∨ ν = 2) (ev : V) :
    sTag (mkStep W (vNilRow ν) ev) = 0 := by
  rcases hν with rfl | rfl
  · rw [show vNilRow (1 : V) = 121 by norm_num [vNilRow]]; exact ctag_eqRefl hWp ev
  · rw [show vNilRow (2 : V) = 116 by norm_num [vNilRow]]; exact ctag_tshvNilCert hWp ev

/-- The rows of the TERM-level pass are Horn rows too (whatever `ν`). -/
lemma ctag_tLeafRow {W : V} (hWp : W = certPieces) (ν kind ev : V) :
    sTag (mkStep W (tLeafRow ν kind) ev) = 0 := by
  have hf : tLeafRow ν kind = 124 ∨ tLeafRow ν kind = 125 ∨ tLeafRow ν kind = 118 ∨ tLeafRow ν kind = 119 := by
    unfold tLeafRow
    by_cases hν : ν = 2 <;> by_cases hk : kind = 0 <;> simp [hν, hk]
  rcases hf with h | h | h | h <;> rw [h]
  · exact ctag_eqOfBvar hWp ev
  · exact ctag_eqOfFvar hWp ev
  · exact ctag_termShiftBvarCert hWp ev
  · exact ctag_termShiftFvarCert hWp ev

lemma ctag_tFuncRow {W : V} (hWp : W = certPieces) (ν ev : V) : sTag (mkStep W (tFuncRow ν) ev) = 0 := by
  have hf : tFuncRow ν = 126 ∨ tFuncRow ν = 120 := by
    unfold tFuncRow; by_cases hν : ν = 2 <;> simp [hν]
  rcases hf with h | h <;> rw [h]
  · exact ctag_eqOfFunc hWp ev
  · exact ctag_termShiftFuncCert hWp ev

lemma ctag_vNilRow' {W : V} (hWp : W = certPieces) (ν ev : V) : sTag (mkStep W (vNilRow ν) ev) = 0 := by
  have hf : vNilRow ν = 121 ∨ vNilRow ν = 116 := by
    unfold vNilRow; by_cases hν : ν = 2 <;> simp [hν]
  rcases hf with h | h <;> rw [h]
  · exact ctag_eqRefl hWp ev
  · exact ctag_tshvNilCert hWp ev

lemma ctag_vAdjRow {W : V} (hWp : W = certPieces) (ν ev : V) : sTag (mkStep W (vAdjRow ν) ev) = 0 := by
  have hf : vAdjRow ν = 127 ∨ vAdjRow ν = 117 := by
    unfold vAdjRow; by_cases hν : ν = 2 <;> simp [hν]
  rcases hf with h | h <;> rw [h]
  · exact ctag_eqOfAdj hWp ev
  · exact ctag_tshvAdjCert hWp ev

/-- The walk's two `utvPi` bridge rows and the closed-symbol rows, read from `certPieces`. -/
lemma ctag_cert38 {W : V} (hWp : W = certPieces) (ev : V) : sTag (mkStep W (38 : V) ev) = 0 := by
  subst hWp
  rw [show (38 : V) = ((38 : ℕ) : V) by simp, mkStep_certPieces_lt 38 (by decide)]
  exact tag_isUTermVecOfSemitermVecLAct rfl ev
lemma ctag_cert39 {W : V} (hWp : W = certPieces) (ev : V) : sTag (mkStep W (39 : V) ev) = 0 := by
  subst hWp
  rw [show (39 : V) = ((39 : ℕ) : V) by simp, mkStep_certPieces_lt 39 (by decide)]
  exact tag_isUTermVecSigmaPiLAct rfl ev
lemma ctag_certFuncRow {W : V} (hWp : W = certPieces) (k f ev : V) : sTag (mkStep W (funcRow k f) ev) = 0 := by
  subst hWp
  have hf : ∃ m : ℕ, m < walkRowCount ∧ funcRow k f = (m : V) := by
    unfold funcRow
    by_cases h1 : k = 0
    · by_cases h2 : f = 0
      · exact ⟨9, by decide, by simp [h1, h2]⟩
      by_cases h3 : f = 1
      · exact ⟨10, by decide, by simp [h1, h2, h3]⟩
      by_cases h4 : f = 2
      · exact ⟨13, by decide, by simp [h1, h2, h3, h4]⟩
      · exact ⟨14, by decide, by simp [h1, h2, h3, h4]⟩
    · by_cases h2 : f = 0
      · exact ⟨11, by decide, by simp [h1, h2]⟩
      · exact ⟨12, by decide, by simp [h1, h2]⟩
  obtain ⟨m, hm, hfm⟩ := hf
  rw [hfm, mkStep_certPieces_lt m hm, ← hfm]
  exact tag_funcRow rfl k f ev
lemma ctag_certRelRow {W : V} (hWp : W = certPieces) (R ev : V) : sTag (mkStep W (relRow R) ev) = 0 := by
  subst hWp
  by_cases hR : R = 0
  · rw [relRow, if_pos hR, show (36 : V) = ((36 : ℕ) : V) by simp, mkStep_certPieces_lt 36 (by decide)]
    exact tag_isRelConst_eq rfl ev
  · rw [relRow, if_neg hR, show (37 : V) = ((37 : ℕ) : V) by simp, mkStep_certPieces_lt 37 (by decide)]
    exact tag_isRelConst_lt rfl ev
lemma ctag_congRow {W : V} (hWp : W = certPieces) (c ev : V) : sTag (mkStep W (congRow c) ev) = 0 := by
  by_cases hc : c = 0
  · rw [congRow, if_pos hc]; exact ctag_congNRel hWp ev
  · rw [congRow, if_neg hc]; exact ctag_congRel hWp ev

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **The term pass drops nothing and introduces no eigenvariable.** Stated over the GRAPH (the
function `passT` inside a Π₁ motive makes `definability` diverge — TRAP). -/
lemma passTGraph_noDrop_shifts (W ν n : V) (hWp : W = certPieces) : ∀ t, IsSemiterm LAct n t →
    ∀ i j y : V, PassTGraph W ν n t i j y → NoDrop y ∧ shiftsV y = 0 := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z hz i j y hy
    rw [PassTGraph.bvar_iff.mp hy, tLeafSteps]
    exact ⟨noDrop_single (Or.inl (ctag_tLeafRow hWp _ _ _)),
      by rw [shiftsV_single, if_neg (by rw [ctag_tLeafRow hWp]; simp)]⟩
  · intro a i j y hy
    rw [PassTGraph.fvar_iff.mp hy, tLeafSteps]
    exact ⟨noDrop_single (Or.inl (ctag_tLeafRow hWp _ _ _)),
      by rw [shiftsV_single, if_neg (by rw [ctag_tLeafRow hWp]; simp)]⟩
  · intro k f v hkf hv ih i j y hy
    have key : ∀ m ≤ k, ∀ i j z : V, PassVGraph W ν n k v m i j z → NoDrop z ∧ shiftsV z = 0 := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero =>
        intro _ i j z hz
        rw [PassVGraph.zero_iff.mp hz, vNilSteps]
        exact ⟨noDrop_single (Or.inl (ctag_vNilRow' hWp _ _)),
          by rw [shiftsV_single, if_neg (by rw [ctag_vNilRow' hWp]; simp)]⟩
      | succ m ihm =>
        intro hm i j z hz
        obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := PassVGraph.succ_iff.mp hz
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hv.lh, tsub_add_cancel_of_le hm])
        set ct := descCountT W n (nthFromEnd v m) with hct
        rw [hnth'] at hyt
        obtain ⟨hnt, hst⟩ := ih _ hlt (i + 1) (j + 1) yt hyt
        obtain ⟨hnv, hsv⟩ := ihm (le_trans le_self_add hm) (i + 1 + ct) (j + 1 + ct) yv hyv
        rw [vAdjSteps]
        refine ⟨noDrop_appendV hnt (noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_cert38 hWp _))
          (noDrop_cons (Or.inl (ctag_cert39 hWp _)) (noDrop_single (Or.inl (ctag_vAdjRow hWp _ _)))))), ?_⟩
        rw [shiftsV_appendV, shiftsV_appendV, hst, hsv]
        have h3 : shiftsV (?[mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + ct) m], mkStep W 39 ?[cTV m, vRef (i + 1 + ct) m],
            mkStep W (vAdjRow ν) (vAdjWits ν n m ct i j)] : V) = 0 := by
          rw [shiftsV_cons, if_neg (by rw [ctag_cert38 hWp]; simp), shiftsV_cons,
            if_neg (by rw [ctag_cert39 hWp]; simp), shiftsV_single,
            if_neg (by rw [ctag_vAdjRow hWp]; simp)]
          simp
        rw [h3]
        simp
    obtain ⟨yv, _, hyv, rfl⟩ := PassTGraph.func_iff.mp hy
    obtain ⟨hnv, hsv⟩ := key k le_rfl (i + 1) (j + 1) yv hyv
    rw [tFuncSteps_eq]
    refine ⟨noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_certFuncRow hWp _ _ _))
      (noDrop_single (Or.inl (ctag_tFuncRow hWp _ _)))), ?_⟩
    rw [shiftsV_appendV, hsv, shiftsV_cons, if_neg (by rw [ctag_certFuncRow hWp]; simp),
      shiftsV_single, if_neg (by rw [ctag_tFuncRow hWp]; simp)]
    simp

/-- The same at the vector level. -/
lemma passVGraph_noDrop_shifts {W ν n : V} (hWp : W = certPieces) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, ∀ i j z : V, PassVGraph W ν n k v m i j z → NoDrop z ∧ shiftsV z = 0 := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _ i j z hz
    rw [PassVGraph.zero_iff.mp hz, vNilSteps]
    exact ⟨noDrop_single (Or.inl (ctag_vNilRow' hWp _ _)),
      by rw [shiftsV_single, if_neg (by rw [ctag_vNilRow' hWp]; simp)]⟩
  | succ m ihm =>
    intro hm i j z hz
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := PassVGraph.succ_iff.mp hz
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hv.lh, tsub_add_cancel_of_le hm])
    set ct := descCountT W n (nthFromEnd v m) with hct
    have hyt' : PassTGraph W ν n v.[k - (m + 1)] (i + 1) (j + 1) yt := hnth' ▸ hyt
    obtain ⟨hnt, hst⟩ := passTGraph_noDrop_shifts W ν n hWp _ (hv.nth hlt) (i + 1) (j + 1) yt hyt'
    obtain ⟨hnv, hsv⟩ := ihm (le_trans le_self_add hm) (i + 1 + ct) (j + 1 + ct) yv hyv
    rw [vAdjSteps]
    refine ⟨noDrop_appendV hnt (noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_cert38 hWp _))
      (noDrop_cons (Or.inl (ctag_cert39 hWp _)) (noDrop_single (Or.inl (ctag_vAdjRow hWp _ _)))))), ?_⟩
    rw [shiftsV_appendV, shiftsV_appendV, hst, hsv]
    have h3 : shiftsV (?[mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + ct) m], mkStep W 39 ?[cTV m, vRef (i + 1 + ct) m],
        mkStep W (vAdjRow ν) (vAdjWits ν n m ct i j)] : V) = 0 := by
      rw [shiftsV_cons, if_neg (by rw [ctag_cert38 hWp]; simp), shiftsV_cons,
        if_neg (by rw [ctag_cert39 hWp]; simp), shiftsV_single,
        if_neg (by rw [ctag_vAdjRow hWp]; simp)]
      simp
    rw [h3]
    simp

set_option maxHeartbeats 2000000 in
/-- **The formula pass drops nothing and introduces no eigenvariable.** -/
lemma passFGraph_noDrop_shifts (W : V) {ν : V} (hν : ν = 1 ∨ ν = 2) (hWp : W = certPieces) :
    ∀ {n r : V}, IsSemiformula LAct n r → ∀ i j y : V, PassFGraph W ν n r i j y → NoDrop y ∧ shiftsV y = 0 := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i j y : V, PassFGraph W ν n r i j y → NoDrop y ∧ shiftsV y = 0)
  · definability
  · intro n k R v hR hv i j y hy
    rw [PassFGraph.rel_iff.mp hy]
    obtain ⟨hnv, hsv⟩ := passVGraph_noDrop_shifts hWp hv k le_rfl (i + 1) (j + 1) _ (passV_graph hv le_rfl)
    unfold fAtomSteps
    by_cases hν1 : ν = 1
    · rw [if_pos hν1]
      refine ⟨noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_certRelRow hWp _ _)) (noDrop_cons (Or.inl (ctag_eqRefl hWp _))
        (noDrop_cons (Or.inl (ctag_congRow hWp _ _)) (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inl rfl) _)))))), ?_⟩
      rw [shiftsV_appendV, hsv, shiftsV_cons, if_neg (by rw [ctag_certRelRow hWp]; simp), shiftsV_cons,
        if_neg (by rw [ctag_eqRefl hWp]; simp), shiftsV_cons, if_neg (by rw [ctag_congRow hWp]; simp),
        shiftsV_single, if_neg (by rw [ctag_fRow hWp hν (Or.inl rfl)]; simp)]
      simp
    · rw [if_neg hν1]
      refine ⟨noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_certRelRow hWp _ _))
        (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inl rfl) _)))), ?_⟩
      rw [shiftsV_appendV, hsv, shiftsV_cons, if_neg (by rw [ctag_certRelRow hWp]; simp), shiftsV_single,
        if_neg (by rw [ctag_fRow hWp hν (Or.inl rfl)]; simp)]
      simp
  · intro n k R v hR hv i j y hy
    rw [PassFGraph.nrel_iff.mp hy]
    obtain ⟨hnv, hsv⟩ := passVGraph_noDrop_shifts hWp hv k le_rfl (i + 1) (j + 1) _ (passV_graph hv le_rfl)
    unfold fAtomSteps
    by_cases hν1 : ν = 1
    · rw [if_pos hν1]
      refine ⟨noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_certRelRow hWp _ _)) (noDrop_cons (Or.inl (ctag_eqRefl hWp _))
        (noDrop_cons (Or.inl (ctag_congRow hWp _ _)) (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inl rfl)) _)))))), ?_⟩
      rw [shiftsV_appendV, hsv, shiftsV_cons, if_neg (by rw [ctag_certRelRow hWp]; simp), shiftsV_cons,
        if_neg (by rw [ctag_eqRefl hWp]; simp), shiftsV_cons, if_neg (by rw [ctag_congRow hWp]; simp),
        shiftsV_single, if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inl rfl))]; simp)]
      simp
    · rw [if_neg hν1]
      refine ⟨noDrop_appendV hnv (noDrop_cons (Or.inl (ctag_certRelRow hWp _ _))
        (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inl rfl)) _)))), ?_⟩
      rw [shiftsV_appendV, hsv, shiftsV_cons, if_neg (by rw [ctag_certRelRow hWp]; simp), shiftsV_single,
        if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inl rfl))]; simp)]
      simp
  · intro n i j y hy
    rw [PassFGraph.verum_iff.mp hy, fConstSteps]
    exact ⟨noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inr (Or.inl rfl))) _)),
      by rw [shiftsV_single, if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inr (Or.inl rfl)))]; simp)]⟩
  · intro n i j y hy
    rw [PassFGraph.falsum_iff.mp hy, fConstSteps]
    exact ⟨noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _)),
      by rw [shiftsV_single, if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; simp)]⟩
  · intro n p q _ _ ihp ihq i j y hy
    obtain ⟨yp, yq, _, _, hp, hq, rfl⟩ := PassFGraph.and_iff.mp hy
    obtain ⟨hnp, hsp⟩ := ihp _ _ yp hp
    obtain ⟨hnq, hsq⟩ := ihq _ _ yq hq
    rw [fBinSteps]
    refine ⟨noDrop_appendV hnp (noDrop_appendV hnq
      (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _)))), ?_⟩
    rw [shiftsV_appendV, shiftsV_appendV, hsp, hsq, shiftsV_single,
      if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; simp)]
    simp
  · intro n p q _ _ ihp ihq i j y hy
    obtain ⟨yp, yq, _, _, hp, hq, rfl⟩ := PassFGraph.or_iff.mp hy
    obtain ⟨hnp, hsp⟩ := ihp _ _ yp hp
    obtain ⟨hnq, hsq⟩ := ihq _ _ yq hq
    rw [fBinSteps]
    refine ⟨noDrop_appendV hnp (noDrop_appendV hnq
      (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) _)))), ?_⟩
    rw [shiftsV_appendV, shiftsV_appendV, hsp, hsq, shiftsV_single,
      if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]; simp)]
    simp
  · intro n p _ ih i j y hy
    obtain ⟨yb, _, hb, rfl⟩ := PassFGraph.all_iff.mp hy
    obtain ⟨hnb, hsb⟩ := ih _ _ yb hb
    rw [fQuantSteps]
    refine ⟨noDrop_appendV hnb
      (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) _))), ?_⟩
    rw [shiftsV_appendV, hsb, shiftsV_single,
      if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))]; simp)]
    simp
  · intro n p _ ih i j y hy
    obtain ⟨yb, _, hb, rfl⟩ := PassFGraph.exs_iff.mp hy
    obtain ⟨hnb, hsb⟩ := ih _ _ yb hb
    rw [fQuantSteps]
    refine ⟨noDrop_appendV hnb
      (noDrop_single (Or.inl (ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) _))), ?_⟩
    rw [shiftsV_appendV, hsb, shiftsV_single,
      if_neg (by rw [ctag_fRow hWp hν (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]; simp)]
    simp

/-- **`certShift` and `certNeg` drop nothing and introduce no eigenvariable** — so a pass runs in a
FIXED context layout: the offsets `i` and `j` never move. -/
theorem certShift_noDrop_shifts {W n r i j : V} (hWp : W = certPieces) (hr : IsSemiformula LAct n r) :
    NoDrop (certShift W n r i j) ∧ shiftsV (certShift W n r i j) = 0 :=
  passFGraph_noDrop_shifts W (Or.inr rfl) hWp hr i j _ (certShift_graph hr)

theorem certNeg_noDrop_shifts {W n r i j : V} (hWp : W = certPieces) (hr : IsSemiformula LAct n r) :
    NoDrop (certNeg W n r i j) ∧ shiftsV (certNeg W n r i j) = 0 :=
  passFGraph_noDrop_shifts W (Or.inl rfl) hWp hr i j _ (certNeg_graph hr)

end passStruct

/-! ### 2.7 Length bounds (the cost prerequisite)

A pass emits ONE Horn step per formula node, plus at an atom the term pass (one step per term
node, three per vector entry). The `len_describe*_le` bounds of `Describe.lean` are the template.
-/

section passLen

lemma len_tLeafSteps (W ν kind z i j : V) : len (tLeafSteps W ν kind z i j) = 1 := by
  simp [tLeafSteps]
lemma len_vNilSteps (W ν : V) : len (vNilSteps W ν) = 1 := by simp [vNilSteps]
lemma len_tFuncSteps (W ν k f i j yv : V) : len (tFuncSteps W ν k f i j yv) = len yv + 2 := by
  rw [tFuncSteps_eq, len_appendV]; simp; norm_num
lemma len_vAdjSteps (W ν n m ct i j yt yv : V) :
    len (vAdjSteps W ν n m ct i j yt yv) = len yt + (len yv + 3) := by
  rw [vAdjSteps, len_appendV, len_appendV]; simp; norm_num
lemma len_fConstSteps (W ν c i j : V) : len (fConstSteps W ν c i j) = 1 := by simp [fConstSteps]
lemma len_fBinSteps (W ν c n cq dq i j yp yq : V) :
    len (fBinSteps W ν c n cq dq i j yp yq) = len yp + (len yq + 1) := by
  rw [fBinSteps, len_appendV, len_appendV]; simp
lemma len_fQuantSteps (W ν c n i j yb : V) : len (fQuantSteps W ν c n i j yb) = len yb + 1 := by
  rw [fQuantSteps, len_appendV]; simp
lemma len_fAtomSteps_of_ne {ν : V} (h : ν ≠ 1) (W c k R i j yv : V) :
    len (fAtomSteps W ν c k R i j yv) = len yv + 2 := by
  rw [fAtomSteps, if_neg h, len_appendV]; simp; norm_num
lemma len_fAtomSteps_one {ν : V} (h : ν = 1) (W c k R i j yv : V) :
    len (fAtomSteps W ν c k R i j yv) = len yv + 4 := by
  rw [fAtomSteps, if_pos h, len_appendV]; simp; norm_num

set_option maxHeartbeats 1000000 in
/-- **The term pass has `≤ 12|t|` steps** (the same shape as the walk). -/
lemma len_passTGraph_le (W ν n : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i j y : V, PassTGraph W ν n t i j y → len y + 4 ≤ 12 * termLen LAct t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z hz i j y hy
    rw [PassTGraph.bvar_iff.mp hy, len_tLeafSteps, termLen_bvar]
    calc (1 : V) + 4 = 5 := by norm_num
      _ ≤ 12 := by norm_num
      _ ≤ 12 * z + 12 := le_add_self
      _ = 12 * (z + 1) := by ring
  · intro a i j y hy
    rw [PassTGraph.fvar_iff.mp hy, len_tLeafSteps, termLen_fvar]
    calc (1 : V) + 4 = 5 := by norm_num
      _ ≤ 12 := by norm_num
      _ ≤ 12 * a + 12 := le_add_self
      _ = 12 * (a + 1) := by ring
  · intro k f v hkf hv ih i j y hy
    have key : ∀ m ≤ k, ∀ i j z : V, PassVGraph W ν n k v m i j z →
        IsUTermVec LAct m (takeLast v m) ∧
        len z + 2 ≤ 12 * listSum (termLenVec LAct m (takeLast v m)) + 4 := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero =>
        intro _ i j z hz
        refine ⟨by simp, ?_⟩
        rw [PassVGraph.zero_iff.mp hz, len_vNilSteps]
        simp; norm_num
      | succ m ihm =>
        intro hm i j z hz
        obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := PassVGraph.succ_iff.mp hz
        have hvlen : len v = k := hv.lh
        have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        rw [hnth'] at hyt
        obtain ⟨hU, hl⟩ := ihm (le_trans le_self_add hm) _ _ yv hyv
        have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
          rw [takeLast_succ_of_lt hjk, hvlen]
        refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
        have h1 := ih _ hlt (i + 1) (j + 1) yt hyt
        rw [len_vAdjSteps, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
        calc len yt + (len yv + 3) + 2
            ≤ (len yv + 2) + (len yt + 4) := by
              rw [show (len yv + 2) + (len yt + 4) = len yt + (len yv + 3) + 2 + 1 by ring]
              exact le_self_add
          _ ≤ (12 * listSum (termLenVec LAct m (takeLast v m)) + 4) + 12 * termLen LAct v.[k - (m + 1)] :=
            add_le_add hl h1
          _ = 12 * termLen LAct v.[k - (m + 1)] + 12 * listSum (termLenVec LAct m (takeLast v m)) + 4 := by ring
    obtain ⟨yv, _, hyv, rfl⟩ := PassTGraph.func_iff.mp hy
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨_, h⟩ := key k le_rfl (i + 1) (j + 1) yv hyv
    rw [htl] at h
    rw [len_tFuncSteps, termLen_func hkf hv.isUTerm]
    calc len yv + 2 + 4 = (len yv + 2) + 4 := by ring
      _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 4 := add_le_add h le_rfl
      _ = 12 * listSum (termLenVec LAct k v) + 8 := by ring
      _ ≤ 12 * listSum (termLenVec LAct k v) + 12 := add_le_add le_rfl (by norm_num)
      _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring

set_option maxHeartbeats 1000000 in
/-- The vector level of the term pass, as a standalone bound. -/
lemma len_passVGraph_le_aux (W ν n : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i j z : V, PassVGraph W ν n k v m i j z →
      len z + 2 ≤ 12 * listSum (termLenVec LAct m (takeLast v m)) + 4 := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i j z hz
    rw [PassVGraph.zero_iff.mp hz, len_vNilSteps]
    simp; norm_num
  | succ m ihm =>
    intro hm
    have hvlen : len v = k := hv.lh
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    obtain ⟨hU, hl⟩ := ihm (le_trans le_self_add hm)
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    intro i j z hz
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := PassVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    rw [hnth'] at hyt
    have h1 := len_passTGraph_le W ν n _ ht (i + 1) (j + 1) yt hyt
    have h2 := hl _ _ yv hyv
    rw [len_vAdjSteps, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
    calc len yt + (len yv + 3) + 2
        ≤ (len yv + 2) + (len yt + 4) := by
          rw [show (len yv + 2) + (len yt + 4) = len yt + (len yv + 3) + 2 + 1 by ring]
          exact le_self_add
      _ ≤ (12 * listSum (termLenVec LAct m (takeLast v m)) + 4) + 12 * termLen LAct v.[k - (m + 1)] :=
        add_le_add h2 h1
      _ = 12 * termLen LAct v.[k - (m + 1)] + 12 * listSum (termLenVec LAct m (takeLast v m)) + 4 := by ring

lemma len_passVGraph_le (W ν n : V) {k v : V} (hv : IsSemitermVec LAct k n v) {m : V} (hm : m ≤ k)
    (i j z : V) (hz : PassVGraph W ν n k v m i j z) :
    len z + 2 ≤ 12 * listSum (termLenVec LAct m (takeLast v m)) + 4 :=
  (len_passVGraph_le_aux W ν n hv m hm).2 i j z hz

set_option maxHeartbeats 1000000 in
/-- **The formula pass has `≤ 12|r|` steps.** -/
lemma len_passFGraph_le (W : V) {ν : V} (hν : ν = 1 ∨ ν = 2) :
    ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i j y : V, PassFGraph W ν n r i j y → len y + 4 ≤ 12 * formulaLen LAct r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i j y : V, PassFGraph W ν n r i j y → len y + 4 ≤ 12 * formulaLen LAct r)
  · definability
  · intro n k R v hkR hv i j y hy
    rw [PassFGraph.rel_iff.mp hy, formulaLen_rel hkR hv.isUTerm]
    have hb := len_passVGraph_le W ν n hv (le_refl k) (i + 1) (j + 1) _ (passV_graph hv le_rfl)
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hb
    by_cases hν1 : ν = 1
    · rw [len_fAtomSteps_one hν1]
      calc len (passV W ν n k v k (i + 1) (j + 1)) + 4 + 4
          = (len (passV W ν n k v k (i + 1) (j + 1)) + 2) + 6 := by ring
        _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 6 := add_le_add hb le_rfl
        _ = 12 * listSum (termLenVec LAct k v) + 10 := by ring
        _ ≤ 12 * listSum (termLenVec LAct k v) + 12 := add_le_add le_rfl (by norm_num)
        _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring
    · rw [len_fAtomSteps_of_ne hν1]
      calc len (passV W ν n k v k (i + 1) (j + 1)) + 2 + 4
          = (len (passV W ν n k v k (i + 1) (j + 1)) + 2) + 4 := by ring
        _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 4 := add_le_add hb le_rfl
        _ = 12 * listSum (termLenVec LAct k v) + 8 := by ring
        _ ≤ 12 * listSum (termLenVec LAct k v) + 12 := add_le_add le_rfl (by norm_num)
        _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n k R v hkR hv i j y hy
    rw [PassFGraph.nrel_iff.mp hy, formulaLen_nrel hkR hv.isUTerm]
    have hb := len_passVGraph_le W ν n hv (le_refl k) (i + 1) (j + 1) _ (passV_graph hv le_rfl)
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hb
    by_cases hν1 : ν = 1
    · rw [len_fAtomSteps_one hν1]
      calc len (passV W ν n k v k (i + 1) (j + 1)) + 4 + 4
          = (len (passV W ν n k v k (i + 1) (j + 1)) + 2) + 6 := by ring
        _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 6 := add_le_add hb le_rfl
        _ = 12 * listSum (termLenVec LAct k v) + 10 := by ring
        _ ≤ 12 * listSum (termLenVec LAct k v) + 12 := add_le_add le_rfl (by norm_num)
        _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring
    · rw [len_fAtomSteps_of_ne hν1]
      calc len (passV W ν n k v k (i + 1) (j + 1)) + 2 + 4
          = (len (passV W ν n k v k (i + 1) (j + 1)) + 2) + 4 := by ring
        _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 4 := add_le_add hb le_rfl
        _ = 12 * listSum (termLenVec LAct k v) + 8 := by ring
        _ ≤ 12 * listSum (termLenVec LAct k v) + 12 := add_le_add le_rfl (by norm_num)
        _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n i j y hy
    rw [PassFGraph.verum_iff.mp hy, len_fConstSteps, formulaLen_verum]; norm_num
  · intro n i j y hy
    rw [PassFGraph.falsum_iff.mp hy, len_fConstSteps, formulaLen_falsum]; norm_num
  · intro n p q hp hq ihp ihq i j y hy
    obtain ⟨yp, yq, _, _, h₁, h₂, rfl⟩ := PassFGraph.and_iff.mp hy
    rw [len_fBinSteps, formulaLen_and hp.isUFormula hq.isUFormula]
    calc len yp + (len yq + 1) + 4 ≤ (len yp + 4) + (len yq + 4) := by
          rw [show (len yp + 4) + (len yq + 4) = len yp + (len yq + 1) + 4 + 3 by ring]; exact le_self_add
      _ ≤ 12 * formulaLen LAct p + 12 * formulaLen LAct q := add_le_add (ihp _ _ yp h₁) (ihq _ _ yq h₂)
      _ ≤ 12 * (formulaLen LAct p + formulaLen LAct q + 1) := by
          rw [show 12 * (formulaLen LAct p + formulaLen LAct q + 1)
            = 12 * formulaLen LAct p + 12 * formulaLen LAct q + 12 by ring]; exact le_self_add
  · intro n p q hp hq ihp ihq i j y hy
    obtain ⟨yp, yq, _, _, h₁, h₂, rfl⟩ := PassFGraph.or_iff.mp hy
    rw [len_fBinSteps, formulaLen_or hp.isUFormula hq.isUFormula]
    calc len yp + (len yq + 1) + 4 ≤ (len yp + 4) + (len yq + 4) := by
          rw [show (len yp + 4) + (len yq + 4) = len yp + (len yq + 1) + 4 + 3 by ring]; exact le_self_add
      _ ≤ 12 * formulaLen LAct p + 12 * formulaLen LAct q := add_le_add (ihp _ _ yp h₁) (ihq _ _ yq h₂)
      _ ≤ 12 * (formulaLen LAct p + formulaLen LAct q + 1) := by
          rw [show 12 * (formulaLen LAct p + formulaLen LAct q + 1)
            = 12 * formulaLen LAct p + 12 * formulaLen LAct q + 12 by ring]; exact le_self_add
  · intro n p hp ih i j y hy
    obtain ⟨yb, _, h₁, rfl⟩ := PassFGraph.all_iff.mp hy
    rw [len_fQuantSteps, formulaLen_all hp.isUFormula]
    calc len yb + 1 + 4 ≤ (len yb + 4) + 1 := le_of_eq (by ring)
      _ ≤ 12 * formulaLen LAct p + 1 := add_le_add (ih _ _ yb h₁) le_rfl
      _ ≤ 12 * (formulaLen LAct p + 1) := by
          rw [show 12 * (formulaLen LAct p + 1) = 12 * formulaLen LAct p + 12 by ring]
          exact add_le_add le_rfl (by norm_num)
  · intro n p hp ih i j y hy
    obtain ⟨yb, _, h₁, rfl⟩ := PassFGraph.exs_iff.mp hy
    rw [len_fQuantSteps, formulaLen_exs hp.isUFormula]
    calc len yb + 1 + 4 ≤ (len yb + 4) + 1 := le_of_eq (by ring)
      _ ≤ 12 * formulaLen LAct p + 1 := add_le_add (ih _ _ yb h₁) le_rfl
      _ ≤ 12 * (formulaLen LAct p + 1) := by
          rw [show 12 * (formulaLen LAct p + 1) = 12 * formulaLen LAct p + 12 by ring]
          exact add_le_add le_rfl (by norm_num)

/-- **`certShift`/`certNeg` have `≤ 12|r|` steps.** -/
theorem len_certShift_le {W n r i j : V} (hr : IsSemiformula LAct n r) :
    len (certShift W n r i j) + 4 ≤ 12 * formulaLen LAct r :=
  len_passFGraph_le W (Or.inr rfl) hr i j _ (certShift_graph hr)

theorem len_certNeg_le {W n r i j : V} (hr : IsSemiformula LAct n r) :
    len (certNeg W n r i j) + 4 ≤ 12 * formulaLen LAct r :=
  len_passFGraph_le W (Or.inl rfl) hr i j _ (certNeg_graph hr)

end passLen

/-! ## Part 3 — the bridge to `Layout.lean`'s identification template

`Layout.lean` (`:53`) records the bridge from the walk's final context to `DossierAt` as NOT in
that file. Its first half — that the two recursions count the SAME number of eigenvariables,
`eqCount r = descCountF W n r` — is proved here: the identification template `eqFT`
(`Layout.lean:4560ff`) and the walk `descFw` (`Describe.lean:3439ff`) have the same node arities
(`bvarT/fvarT/constT` emit `1`, `binT` `π₁ yp + π₁ yq + 1`, `quantT`/`atomT`/`funcT` `π₁ + 1`,
`nilT` `0`, `adjT` `π₁ ih + π₁ p + 1` — exactly `descCountT`/`descCountF`'s arities).
-/

section countBridge

lemma pi1_bvarT (z : V) : π₁ (bvarT z) = 1 := by rw [bvarT, pi₁_pair]
lemma pi1_fvarT (x : V) : π₁ (fvarT x) = 1 := by rw [fvarT, pi₁_pair]
lemma pi1_funcT (k f d : V) : π₁ (funcT k f d) = π₁ d + 1 := by rw [funcT, pi₁_pair]
lemma pi1_nilT (w : V) : π₁ (nilT w) = 0 := by rw [nilT, pi₁_pair]
lemma pi1_adjT (j p ih : V) : π₁ (adjT j p ih) = π₁ ih + π₁ p + 1 := by rw [adjT, pi₁_pair]
lemma pi1_constT (kind row : V) : π₁ (constT kind row) = 1 := by rw [constT, pi₁_pair]
lemma pi1_binT (kind row yp yq : V) : π₁ (binT kind row yp yq) = π₁ yp + π₁ yq + 1 := by
  rw [binT, pi₁_pair]
lemma pi1_quantT (kind row yp : V) : π₁ (quantT kind row yp) = π₁ yp + 1 := by rw [quantT, pi₁_pair]
lemma pi1_atomT (kind row k R d : V) : π₁ (atomT kind row k R d) = π₁ d + 1 := by rw [atomT, pi₁_pair]

/-- **The two term recursions have the same count.** -/
lemma pi1_eqT_eq_descCountT (W n : V) : ∀ t, IsSemiterm LAct n t → π₁ (eqT t) = descCountT W n t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z _; rw [eqT_bvar, pi1_bvarT, descCountT_bvar]
  · intro a; rw [eqT_fvar, pi1_fvarT, descCountT_fvar]
  · intro k f v hkf hv ih
    have key : ∀ m ≤ k, π₁ (eqVecAux (eqTVec k v) m) = π₁ (descVecAux W n (descTVec W n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _; rw [eqVecAux_zero, pi1_nilT, descVecAux_zero, nilNode, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : nthFromEnd (eqTVec k v) m = eqT v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_eqTVec hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_eqTVec hv.isUTerm hlt]
        have h2 : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec W n hv.isUTerm hlt]
        rw [eqVecAux_succ, h1, pi1_adjT, descVecAux_succ, h2, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm), ih _ hlt]
        rfl
    rw [eqT_func hkf hv.isUTerm, pi1_funcT, descCountT_func W n hkf hv.isUTerm, key k le_rfl]

/-- **The bridge: the identification template and the walk introduce the same number of
eigenvariables** (`Layout.lean:53`'s missing half). -/
theorem eqCount_eq_descCountF (W : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    eqCount r = descCountF W n r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction (P := fun n r ↦ eqCount r = descCountF W n r)
  · definability
  · intro n k R v hkR hv
    have key : ∀ m ≤ k, π₁ (eqVecAux (eqTVec k v) m) = π₁ (descVecAux W n (descTVec W n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _; rw [eqVecAux_zero, pi1_nilT, descVecAux_zero, nilNode, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : nthFromEnd (eqTVec k v) m = eqT v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_eqTVec hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_eqTVec hv.isUTerm hlt]
        have h2 : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec W n hv.isUTerm hlt]
        rw [eqVecAux_succ, h1, pi1_adjT, descVecAux_succ, h2, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm), pi1_eqT_eq_descCountT W n _ (hv.nth hlt)]
        rfl
    rw [eqCount, eqFT_rel hkR hv.isUTerm, pi1_atomT, descCountF_rel W n hkR hv, key k le_rfl]
  · intro n k R v hkR hv
    have key : ∀ m ≤ k, π₁ (eqVecAux (eqTVec k v) m) = π₁ (descVecAux W n (descTVec W n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _; rw [eqVecAux_zero, pi1_nilT, descVecAux_zero, nilNode, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : nthFromEnd (eqTVec k v) m = eqT v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_eqTVec hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_eqTVec hv.isUTerm hlt]
        have h2 : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec W n hv.isUTerm hlt]
        rw [eqVecAux_succ, h1, pi1_adjT, descVecAux_succ, h2, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm), pi1_eqT_eq_descCountT W n _ (hv.nth hlt)]
        rfl
    rw [eqCount, eqFT_nrel hkR hv.isUTerm, pi1_atomT, descCountF_nrel W n hkR hv, key k le_rfl]
  · intro n; rw [eqCount, eqFT_verum, pi1_constT, descCountF_verum]
  · intro n; rw [eqCount, eqFT_falsum, pi1_constT, descCountF_falsum]
  · intro n p q hp hq ihp ihq
    rw [eqCount, eqFT_and hp.isUFormula hq.isUFormula, pi1_binT, descCountF_and W n hp hq]
    rw [eqCount] at ihp ihq
    rw [ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [eqCount, eqFT_or hp.isUFormula hq.isUFormula, pi1_binT, descCountF_or W n hp hq]
    rw [eqCount] at ihp ihq
    rw [ihp, ihq]
  · intro n p hp ih
    rw [eqCount, eqFT_all hp.isUFormula, pi1_quantT, descCountF_all W n hp]
    rw [eqCount] at ih
    rw [ih]
  · intro n p hp ih
    rw [eqCount, eqFT_exs hp.isUFormula, pi1_quantT, descCountF_exs W n hp]
    rw [eqCount] at ih
    rw [ih]

end countBridge

/-! ## Part 4 — applicability: the pass runs and leaves the root fact

The remaining two conjuncts of `certShift_ok`. The pass runs in a context holding BOTH dossiers —
the source `t` at offset `i` and the image `termShift t` at offset `j` — and every emitted row's
antecedents are exactly the shape facts the `dossT_*`/`dossV_*` decomposition lemmas read off
them. Every step is then applicable and the final context holds `tshFact &j &i`.

**Two piece tables.** The dossiers are the WALK's output, so they are stated at `Wd = walkPieces`
(`dossT_*` demand it); the pass's own steps are read from `W = certPieces`. The offsets and the
`describeT` counts belong to `Wd`.

**`M = 9`.** `CertRows.lean`'s convention: `cok_tsvAdjCert` is stated at `M = 9`, every other
`cok_` at `M = 8`; the siblings are lifted with `StepOK.mono`/`ListOK.mono` through `h89`.
-/

/-! ### 4.-1 The walk is the same over `certPieces` as over `walkPieces`

The walk only ever names rows `< walkRowCount`, and `certPieces` extends `walkPieces` entrywise
(`mkStep_certPieces_lt`), so every walk object — `descT`, `descTVec`, `descVecAux`, `descFw` and
hence `describeT`/`describeF`/`descCountT`/`descCountF` — is UNCHANGED. The pass may therefore run
over ONE piece table, `certPieces`, with the dossiers stated at `walkPieces` and transported here.
-/

section pieceInvariance

/-- The walk's counts are the same over the two piece tables. -/
theorem descCountT_certPieces (n : V) : ∀ t, IsSemiterm LAct n t →
    descCountT (certPieces : V) n t = descCountT (walkPieces : V) n t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z _; rw [descCountT_bvar, descCountT_bvar]
  · intro a; rw [descCountT_fvar, descCountT_fvar]
  · intro k f v hkf hv ih
    have key : ∀ m ≤ k, π₁ (descVecAux (certPieces : V) n (descTVec (certPieces : V) n k v) m) =
        π₁ (descVecAux (walkPieces : V) n (descTVec (walkPieces : V) n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero =>
        intro _
        rw [descVecAux_zero, descVecAux_zero, nilNode, nilNode, pi₁_pair, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : ∀ Wx : V, nthFromEnd (descTVec Wx n k v) m = descT Wx n v.[k - (m + 1)] := fun Wx ↦ by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wx n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wx n hv.isUTerm hlt]
        rw [descVecAux_succ, h1, adjNode, pi₁_pair, descVecAux_succ, h1, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm)]
        have := ih _ hlt
        rw [descCountT, descCountT] at this
        rw [this]
    rw [descCountT_func _ n hkf hv.isUTerm, descCountT_func _ n hkf hv.isUTerm, key k le_rfl]

end pieceInvariance

/-! ### 4.0 Count preservation under `termShift`

The source and the image are walked in PARALLEL, so the two dossiers' offsets must advance in
lock-step: the walk of `termShift t` introduces exactly as many eigenvariables as the walk of `t`
(`termShift` is structure-preserving; only the `fvar` leaves change, and a leaf costs `1` either
way).
-/

section shiftCount

set_option maxHeartbeats 1000000 in
/-- **The walk of `termShift t` has the same eigenvariable count as the walk of `t`.** -/
theorem descCountT_termShift (Wd n : V) : ∀ t, IsSemiterm LAct n t →
    descCountT Wd n (termShift LAct t) = descCountT Wd n t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z hz; rw [termShift_bvar]
  · intro a; rw [termShift_fvar, descCountT_fvar, descCountT_fvar]
  · intro k f v hkf hv ih
    have hvs : IsSemitermVec LAct k n (termShiftVec LAct k v) := hv.termShiftVec
    have key : ∀ m ≤ k, π₁ (descVecAux Wd n (descTVec Wd n k (termShiftVec LAct k v)) m) =
        π₁ (descVecAux Wd n (descTVec Wd n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _; rw [descVecAux_zero, descVecAux_zero, nilNode, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : nthFromEnd (descTVec Wd n k (termShiftVec LAct k v)) m =
            descT Wd n (termShiftVec LAct k v).[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wd n hvs.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wd n hvs.isUTerm hlt]
        have h2 : nthFromEnd (descTVec Wd n k v) m = descT Wd n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wd n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wd n hv.isUTerm hlt]
        have h3 : (termShiftVec LAct k v).[k - (m + 1)] = termShift LAct v.[k - (m + 1)] :=
          nth_termShiftVec hv.isUTerm hlt
        rw [descVecAux_succ, h1, h3, adjNode, pi₁_pair, descVecAux_succ, h2, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm)]
        have := ih _ hlt
        rw [descCountT, descCountT] at this
        rw [this]
    rw [termShift_func hkf hv.isUTerm, descCountT_func Wd n hkf hvs.isUTerm,
      descCountT_func Wd n hkf hv.isUTerm, key k le_rfl]

set_option maxHeartbeats 1000000 in
/-- **The walk of `shift r` has the same eigenvariable count as the walk of `r`** — the formula-level
twin, i.e. `outCount Wd 2 n r = descCountF Wd n r`, so the shift pass's two offsets advance in
lock-step. -/
theorem descCountF_shift (Wd : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    descCountF Wd n (shift LAct r) = descCountF Wd n r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ descCountF Wd n (shift LAct r) = descCountF Wd n r)
  · definability
  · intro n k R v hkR hv
    have hvs : IsSemitermVec LAct k n (termShiftVec LAct k v) := hv.termShiftVec
    have key : ∀ m ≤ k, π₁ (descVecAux Wd n (descTVec Wd n k (termShiftVec LAct k v)) m) =
        π₁ (descVecAux Wd n (descTVec Wd n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _; rw [descVecAux_zero, descVecAux_zero, nilNode, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : nthFromEnd (descTVec Wd n k (termShiftVec LAct k v)) m =
            descT Wd n (termShiftVec LAct k v).[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wd n hvs.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wd n hvs.isUTerm hlt]
        have h2 : nthFromEnd (descTVec Wd n k v) m = descT Wd n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wd n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wd n hv.isUTerm hlt]
        have h3 : (termShiftVec LAct k v).[k - (m + 1)] = termShift LAct v.[k - (m + 1)] :=
          nth_termShiftVec hv.isUTerm hlt
        rw [descVecAux_succ, h1, h3, adjNode, pi₁_pair, descVecAux_succ, h2, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm)]
        have := descCountT_termShift Wd n _ (hv.nth hlt)
        rw [descCountT, descCountT] at this
        rw [this]
    rw [shift_rel hkR hv.isUTerm, descCountF_rel Wd n hkR hvs, descCountF_rel Wd n hkR hv, key k le_rfl]
  · intro n k R v hkR hv
    have hvs : IsSemitermVec LAct k n (termShiftVec LAct k v) := hv.termShiftVec
    have key : ∀ m ≤ k, π₁ (descVecAux Wd n (descTVec Wd n k (termShiftVec LAct k v)) m) =
        π₁ (descVecAux Wd n (descTVec Wd n k v) m) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => definability
      | zero => intro _; rw [descVecAux_zero, descVecAux_zero, nilNode, pi₁_pair]
      | succ m ihm =>
        intro hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have h1 : nthFromEnd (descTVec Wd n k (termShiftVec LAct k v)) m =
            descT Wd n (termShiftVec LAct k v).[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wd n hvs.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wd n hvs.isUTerm hlt]
        have h2 : nthFromEnd (descTVec Wd n k v) m = descT Wd n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1))
            (by rw [len_descTVec Wd n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec Wd n hv.isUTerm hlt]
        have h3 : (termShiftVec LAct k v).[k - (m + 1)] = termShift LAct v.[k - (m + 1)] :=
          nth_termShiftVec hv.isUTerm hlt
        rw [descVecAux_succ, h1, h3, adjNode, pi₁_pair, descVecAux_succ, h2, adjNode, pi₁_pair,
          ihm (le_trans le_self_add hm)]
        have := descCountT_termShift Wd n _ (hv.nth hlt)
        rw [descCountT, descCountT] at this
        rw [this]
    rw [shift_nrel hkR hv.isUTerm, descCountF_nrel Wd n hkR hvs, descCountF_nrel Wd n hkR hv, key k le_rfl]
  · intro n; rw [shift_verum]
  · intro n; rw [shift_falsum]
  · intro n p q hp hq ihp ihq
    rw [shift_and hp.isUFormula hq.isUFormula, descCountF_and Wd n hp.shift hq.shift,
      descCountF_and Wd n hp hq, ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [shift_or hp.isUFormula hq.isUFormula, descCountF_or Wd n hp.shift hq.shift,
      descCountF_or Wd n hp hq, ihp, ihq]
  · intro n p hp ih
    rw [shift_all hp.isUFormula, descCountF_all Wd n hp.shift, descCountF_all Wd n hp, ih]
  · intro n p hp ih
    rw [shift_exs hp.isUFormula, descCountF_exs Wd n hp.shift, descCountF_exs Wd n hp, ih]

/-- The shift pass's offsets advance in lock-step: `outCount Wd 2 n r = descCountF Wd n r`. -/
theorem outCount_shift {Wd n r : V} (hr : IsSemiformula LAct n r) :
    outCount Wd 2 n r = descCountF Wd n r := by
  rw [outCount, imgF_of_ne (V := V) (ν := 2) (by simp), descCountF_shift Wd hr]

end shiftCount

section certOK

/-- The `M = 8 ≤ 9` coercion the mixed-arity certification table needs. -/
lemma h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)

end certOK

/-! ### 4.1 Helpers: constructor-independent dossier facts, the count bridges, the E-bounds

The applicability proofs read three kinds of facts off the dossiers: the per-constructor shape
facts (`dossT_*`/`dossF_*`/`dossV_succ`), the constructor-INDEPENDENT `tPiFact`/`piFact` of every
node (`dossT_tPi`/`dossF_pi`, from the walk's own root fact) and the vector-level `tvPiFact`
(`dossV_tvPi`, uniform over the empty and the non-empty vector: `vRef i 0 = 𝟎 = cT 0`). The pass's
own offsets are computed over `certPieces` while the dossiers count over `walkPieces`
(`descCountF_certPieces` completes `descCountT_certPieces`), and the `neg` family's output side
counts like its input (`descCountF_neg`).
-/

section certHelpers

variable {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {Wd : V} (hWd : Wd = walkPieces)
include htbl hW hWd

/-- Every term dossier holds `tPiF (cT n) &i` (the walk's root fact, transported). -/
lemma dossT_tPi {Γ n t i : V} (ht : IsSemiterm LAct n t) (h : DossT Wd Γ n t i) :
    neg LAct (tPiFact (cTV n) (^&i)) ∈ Γ := by
  obtain ⟨_, _, _, _, hmem⟩ := describeT_ok htbl hW ht (E := 2 * n + 2 * termLen LAct t + 8) le_rfl (Γ := 0) IsFormulaSet.empty
  rw [← hWd] at hmem
  have := h _ hmem
  rwa [shiftIterV_neg (isFormula_tPiFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_tPiFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at this

/-- Every formula dossier holds `piF (cT n) &i`. -/
lemma dossF_pi {Γ n r i : V} (hr : IsSemiformula LAct n r) (h : DossF Wd Γ n r i) :
    neg LAct (piFact (cTV n) (^&i)) ∈ Γ := by
  obtain ⟨_, _, _, _, hmem⟩ := describeF_ok htbl hW hr (E := 2 * n + 2 * formulaLen LAct r + 8) le_rfl (Γ := 0) IsFormulaSet.empty
  rw [← hWd] at hmem
  have := h _ hmem
  rwa [shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)), shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp),
    termShiftIterV_fvar, termShiftIterV_cTV, zero_add] at this

/-- The walk's eigenvariable counts are bounded by the lengths (read off `describeT_ok`/`describeF_ok`). -/
lemma descCountT_walk_le {n t : V} (ht : IsSemiterm LAct n t) : descCountT Wd n t + 1 ≤ 2 * termLen LAct t := by
  have := (describeT_ok htbl hW ht (E := 2 * n + 2 * termLen LAct t + 8) le_rfl (Γ := 0) IsFormulaSet.empty).2.2.2.1
  rwa [← hWd] at this
lemma descCountF_walk_le {n r : V} (hr : IsSemiformula LAct n r) : descCountF Wd n r + 1 ≤ 2 * formulaLen LAct r := by
  have := (describeF_ok htbl hW hr (E := 2 * n + 2 * formulaLen LAct r + 8) le_rfl (Γ := 0) IsFormulaSet.empty).2.2.2.1
  rwa [← hWd] at this

/-- The empty vector's dossier: `tvPiF (cT 0) (cT n) (cT 0)` (the `nilNode`'s bridge row). -/
lemma dossV_zero {Γ n k v i : V} (h : DossV Wd Γ n k v 0 i) :
    neg LAct (tvPiFact (cTV 0) (cTV n) (cTV 0)) ∈ Γ := by
  have h2 : neg LAct (tvPiFact (cTV 0) (cTV n) (cTV 0)) ∈ finalCtx 0 (π₂ (descVecAux Wd n (descTVec Wd n k v) 0)) := by
    rw [descVecAux_zero, nilNode, pi₂_pair, finalCtx_cons, finalCtx_single,
      ctx_isSemitermVecSigmaPiLAct hWd (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)]
    exact mem_insert_self'
  have := h _ h2
  rwa [shiftIterV_neg (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)),
    shiftIterV_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _),
    termShiftIterV_cTV, termShiftIterV_cTV] at this

/-- The vector-level `tvPiF (cT m) (cT n) ⟨v⟩` of a vector dossier, uniformly in `m`. -/
lemma dossV_tvPi {Γ n k v m i : V} (hv : IsSemitermVec LAct k n v) (hm : m ≤ k) (h : DossV Wd Γ n k v m i) :
    neg LAct (tvPiFact (cTV m) (cTV n) (vRef i m)) ∈ Γ := by
  rcases zero_or_succ m with rfl | ⟨m, rfl⟩
  · rw [vRef_zero, ← cTV_zero]; exact dossV_zero htbl hW hWd h
  · rw [vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))]
    exact (dossV_succ htbl hW hWd hv hm h).2.1

end certHelpers

section countBridges

/-- The vector walk's count is the same over the two piece tables. -/
theorem descVecAux_count_certPieces (n : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, π₁ (descVecAux (certPieces : V) n (descTVec (certPieces : V) n k v) m) =
      π₁ (descVecAux (walkPieces : V) n (descTVec (walkPieces : V) n k v) m) := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    rw [descVecAux_zero, descVecAux_zero, nilNode, nilNode, pi₁_pair, pi₁_pair]
  | succ m ihm =>
    intro hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have h1 : ∀ Wx : V, nthFromEnd (descTVec Wx n k v) m = descT Wx n v.[k - (m + 1)] := fun Wx ↦ by
      rw [nthFromEnd_eq (a := k - (m + 1))
        (by rw [len_descTVec Wx n hv.isUTerm, tsub_add_cancel_of_le hm]),
        nth_descTVec Wx n hv.isUTerm hlt]
    rw [descVecAux_succ, h1, adjNode, pi₁_pair, descVecAux_succ, h1, adjNode, pi₁_pair,
      ihm (le_trans le_self_add hm)]
    have := descCountT_certPieces n _ (hv.nth hlt)
    rw [descCountT, descCountT] at this
    rw [this]

/-- The formula walk's count is the same over the two piece tables. -/
theorem descCountF_certPieces : ∀ {n r : V}, IsSemiformula LAct n r →
    descCountF (certPieces : V) n r = descCountF (walkPieces : V) n r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ descCountF (certPieces : V) n r = descCountF (walkPieces : V) n r)
  · definability
  · intro n k R v hkR hv
    rw [descCountF_rel _ n hkR hv, descCountF_rel _ n hkR hv, descVecAux_count_certPieces n hv k le_rfl]
  · intro n k R v hkR hv
    rw [descCountF_nrel _ n hkR hv, descCountF_nrel _ n hkR hv, descVecAux_count_certPieces n hv k le_rfl]
  · intro n; rw [descCountF_verum, descCountF_verum]
  · intro n; rw [descCountF_falsum, descCountF_falsum]
  · intro n p q hp hq ihp ihq
    rw [descCountF_and _ n hp hq, descCountF_and _ n hp hq, ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [descCountF_or _ n hp hq, descCountF_or _ n hp hq, ihp, ihq]
  · intro n p hp ih
    rw [descCountF_all _ n hp, descCountF_all _ n hp, ih]
  · intro n p hp ih
    rw [descCountF_exs _ n hp, descCountF_exs _ n hp, ih]

/-- **The walk of `neg r` has the same eigenvariable count as the walk of `r`** (`neg` swaps
constructors pairwise and leaves the atoms' vectors alone). -/
theorem descCountF_neg (Wd : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    descCountF Wd n (neg LAct r) = descCountF Wd n r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ descCountF Wd n (neg LAct r) = descCountF Wd n r)
  · definability
  · intro n k R v hkR hv
    rw [neg_rel hkR hv.isUTerm, descCountF_nrel Wd n hkR hv, descCountF_rel Wd n hkR hv]
  · intro n k R v hkR hv
    rw [neg_nrel hkR hv.isUTerm, descCountF_rel Wd n hkR hv, descCountF_nrel Wd n hkR hv]
  · intro n; rw [neg_verum, descCountF_falsum, descCountF_verum]
  · intro n; rw [neg_falsum, descCountF_verum, descCountF_falsum]
  · intro n p q hp hq ihp ihq
    rw [neg_and hp.isUFormula hq.isUFormula, descCountF_or Wd n hp.neg hq.neg, descCountF_and Wd n hp hq, ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [neg_or hp.isUFormula hq.isUFormula, descCountF_and Wd n hp.neg hq.neg, descCountF_or Wd n hp hq, ihp, ihq]
  · intro n p hp ih
    rw [neg_all hp.isUFormula, descCountF_exs Wd n hp.neg, descCountF_all Wd n hp, ih]
  · intro n p hp ih
    rw [neg_ex hp.isUFormula, descCountF_all Wd n hp.neg, descCountF_exs Wd n hp, ih]

/-- The neg pass's offsets advance in lock-step too: `outCount Wd 1 n r = descCountF Wd n r`. -/
theorem outCount_neg {Wd n r : V} (hr : IsSemiformula LAct n r) :
    outCount Wd 1 n r = descCountF Wd n r := by
  rw [outCount, imgF_one, descCountF_neg Wd hr]

/-- A shift-free non-dropping list only grows its context. -/
lemma subset_finalCtx_of_shiftsV_zero {Γ S : V} (hS : NoDrop S) (h0 : shiftsV S = 0) : Γ ⊆ finalCtx Γ S := by
  intro x hx
  have := mem_finalCtx_of_mem hS hx
  rwa [h0, shiftIterV_zero] at this

/-- The walk's closed-symbol and bridge rows, read from `certPieces`, are the walk's own steps. -/
lemma mkStep_certPieces_funcRow (k f ev : V) :
    mkStep (certPieces : V) (funcRow k f) ev = mkStep walkPieces (funcRow k f) ev := by
  have hf : ∃ m : ℕ, m < walkRowCount ∧ funcRow k f = (m : V) := by
    unfold funcRow
    by_cases h1 : k = 0
    · by_cases h2 : f = 0
      · exact ⟨9, by decide, by simp [h1, h2]⟩
      by_cases h3 : f = 1
      · exact ⟨10, by decide, by simp [h1, h2, h3]⟩
      by_cases h4 : f = 2
      · exact ⟨13, by decide, by simp [h1, h2, h3, h4]⟩
      · exact ⟨14, by decide, by simp [h1, h2, h3, h4]⟩
    · by_cases h2 : f = 0
      · exact ⟨11, by decide, by simp [h1, h2]⟩
      · exact ⟨12, by decide, by simp [h1, h2]⟩
  obtain ⟨m, hm, hfm⟩ := hf
  rw [hfm, mkStep_certPieces_lt m hm]
lemma mkStep_certPieces_relRow (R ev : V) :
    mkStep (certPieces : V) (relRow R) ev = mkStep walkPieces (relRow R) ev := by
  by_cases hR : R = 0
  · rw [relRow, if_pos hR, show (36 : V) = ((36 : ℕ) : V) by simp, mkStep_certPieces_lt 36 (by decide)]
  · rw [relRow, if_neg hR, show (37 : V) = ((37 : ℕ) : V) by simp, mkStep_certPieces_lt 37 (by decide)]
lemma mkStep_certPieces_38 (ev : V) : mkStep (certPieces : V) 38 ev = mkStep walkPieces 38 ev := by
  rw [show (38 : V) = ((38 : ℕ) : V) by simp, mkStep_certPieces_lt 38 (by decide)]
lemma mkStep_certPieces_39 (ev : V) : mkStep (certPieces : V) 39 ev = mkStep walkPieces 39 ev := by
  rw [show (39 : V) = ((39 : ℕ) : V) by simp, mkStep_certPieces_lt 39 (by decide)]

end countBridges

section eBounds

/-! The witness-length side conditions of the `cok_` lemmas, from the two offset bounds
`i + D + 1 ≤ E` (source) / `j + D + 1 ≤ E` (image) and the arity bound `2n + D + 8 ≤ E`. -/

lemma E_eight {n D E : V} (h : 2 * n + D + 8 ≤ E) : (8 : V) ≤ E := le_trans le_add_self h
lemma E_cT_n {n D E : V} (h : 2 * n + D + 8 ≤ E) : termLen LAct (cTV n) ≤ E :=
  termLen_cTV_le (le_trans (add_le_add (le_self_add : 2 * n ≤ 2 * n + D) (by norm_num : (1 : V) ≤ 8)) h)
lemma E_cT_le_two {m E : V} (hm : m ≤ 2) (h8 : (8 : V) ≤ E) : termLen LAct (cTV m) ≤ E :=
  termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left hm zero_le) (le_refl (1 : V)))
    (le_trans (by norm_num) h8))
lemma E_cT_leaf {x n E : V} (h : 2 * n + 2 * (x + 1) + 8 ≤ E) : termLen LAct (cTV x) ≤ E :=
  termLen_cTV_le (le_trans (show 2 * x + 1 ≤ 2 * (x + 1) by
      rw [mul_add, mul_one]; exact add_le_add (le_refl (2 * x)) (by norm_num))
    (le_trans le_add_self (le_trans le_self_add h)))
lemma E_fvar {i D E : V} (h : i + D + 1 ≤ E) : termLen LAct (^&i : V) ≤ E :=
  termLen_fvar_le (le_trans (add_le_add (le_self_add : i ≤ i + D) (le_refl (1 : V))) h)
lemma E_fvar_succ {i D E : V} (hD : 1 ≤ D) (h : i + D + 1 ≤ E) : termLen LAct (^&(i + 1) : V) ≤ E :=
  termLen_fvar_le (le_trans (add_le_add (add_le_add (le_refl i) hD) (le_refl (1 : V))) h)
lemma E_vRef_succ {i D E m : V} (hD : 1 ≤ D) (h : i + D + 1 ≤ E) : termLen LAct (vRef (i + 1) m) ≤ E :=
  termLen_vRef_le (le_trans (add_le_add (add_le_add (le_refl i) hD) (le_refl (1 : V))) h)
lemma E_vRef_ct {i ct D E m : V} (hct : ct + 1 ≤ D) (h : i + D + 1 ≤ E) :
    termLen LAct (vRef (i + 1 + ct) m) ≤ E :=
  termLen_vRef_le (le_trans (le_of_eq (show i + 1 + ct + 1 = i + (ct + 1) + 1 by ring))
    (le_trans (add_le_add (add_le_add (le_refl i) hct) (le_refl (1 : V))) h))
lemma E_zero_term {E : V} (h8 : (8 : V) ≤ E) : termLen LAct (𝟎 : V) ≤ E := by
  rw [← cTV_zero]; exact E_cT_le_two (by norm_num) h8
lemma isSemiterm_zero_LAct : IsSemiterm LAct 0 (𝟎 : V) := by
  rw [← cTV_zero]; exact cTV_semiterm_LAct 0 0

end eBounds


/-! ### 4.2 The term-level SHIFT pass is applicable and certifies `tshFact &j &i`

The invariant is stated over the GRAPH and quantifies the offsets, the cap `E` and the context.
`PassPre D n i j E Γ` packages the side conditions: `E` bounds the arity part (`2n + D + 8`, the
walk's own shape) and the two offset parts (`i + D + 1`, `j + D + 1`) — with `D = 2|t|` for a term
and `D = 2Σ|entries| + 1` for a vector, the deepest eigenvariable a pass names sits
`descCount < 2|·|` above the root. `PassPost tbl E Γ y F` is the conclusion: the list is applicable
at cap `8`, Horn-only, and leaves `neg F` in its final context. (The two packages exist because
`definability` on the inlined 8-conjunct motive times out at `whnf` — the `GoalOK` lesson.)
The dossiers live at `Wd = walkPieces`, the pass at `W = certPieces`.
-/

section termShiftOK

/-- The side conditions of a pass: the cap `E` bounds the arity part and both offset parts. -/
def PassPre (D n i j E Γ : V) : Prop :=
  2 * n + D + 8 ≤ E ∧ i + D + 1 ≤ E ∧ j + D + 1 ≤ E ∧ IsFormulaSet LAct Γ
instance passPre_definable : 𝚫₁.Definable (fun v : Fin 6 → V ↦ PassPre (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold PassPre; definability

/-- The conclusion of a pass: applicable at cap `8`, Horn-only, `neg F` in the final context. -/
def PassPost (tbl E Γ y F : V) : Prop := ListOK tbl E ((8 : ℕ) : V) Γ y ∧ HornOnly y ∧ neg LAct F ∈ finalCtx Γ y
instance passPost_definable : 𝚫₁-Relation₅ (PassPost : V → V → V → V → V → Prop) := by
  unfold PassPost; definability

/-- The term-level invariant of the shift pass (the Π₁ motive of the structural induction). -/
def TShiftOK (tbl Wd W n t : V) : Prop :=
  ∀ i j y E Γ : V, PassTGraph W 2 n t i j y → PassPre (2 * termLen LAct t) n i j E Γ →
    DossT Wd Γ n t i → DossT Wd Γ n (termShift LAct t) j → PassPost tbl E Γ y (tshFact (^&j) (^&i))
instance tShiftOK_definable : 𝚷₁-Relation₅ (TShiftOK : V → V → V → V → V → Prop) := by
  unfold TShiftOK; definability

set_option maxHeartbeats 4000000 in
/-- **The vector-level shift pass is applicable**, tail first (the entries' invariant as a hypothesis,
the `descVecAux_ok` pattern): it certifies `tshvFact ⟨v⟩ⱼ (cT m) ⟨v⟩ᵢ` for the last `m` entries. -/
lemma passVGraph_shift_ok_aux {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (n : V) {k v : V} (hk : k ≤ 2)
    (hv : IsSemitermVec LAct k n v) (ih : ∀ a < k, TShiftOK tbl Wd W n v.[a]) :
    ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i j z E Γ : V, PassVGraph W 2 n k v m i j z →
      PassPre (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) n i j E Γ →
      DossV Wd Γ n k v m i → DossV Wd Γ n k (termShiftVec LAct k v) m j →
      PassPost tbl E Γ z (tshvFact (vRef j m) (cTV m) (vRef i m)) := by
  have hW : WalkTable tbl := hC.walkTable
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i j z E Γ hz hP hDi hDj
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    -- TRAP: never hand `𝟎` to a `cok_` witness — `isDefEq` on the closed constant times out; name it `cTV 0`
    rw [PassVGraph.zero_iff.mp hz, vNilSteps, vNilRow, if_pos rfl, ← cTV_zero]
    have h8 : (8 : V) ≤ E := E_eight hE
    obtain ⟨hok, htag, hctx⟩ := cok_tshvNilCert htbl hC hWp hΓ (wx := cTV 0) (cTV_semiterm_LAct 0 0)
      (E_cT_le_two (by norm_num) h8)
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx, vRef_zero, vRef_zero, cTV_zero]
    exact mem_insert_self'
  | succ m ihm =>
    intro hm
    have hvlen : len v = k := hv.lh
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    obtain ⟨hU, hrest⟩ := ihm (le_trans le_self_add hm)
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    intro i j z E Γ hz hP hDi hDj
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := PassVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    have hct : descCountT W n (nthFromEnd v m) = descCountT Wd n v.[k - (m + 1)] := by
      rw [hnth', hWp, hWd]; exact descCountT_certPieces n _ ht
    rw [hnth'] at hyt
    rw [hct] at hyv ⊢
    rw [htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    have hct_le : descCountT Wd n v.[k - (m + 1)] + 1 ≤ 2 * termLen LAct v.[k - (m + 1)] :=
      descCountT_walk_le htbl hW hWd ht
    have h8 : (8 : V) ≤ E := E_eight hE
    have hmk : m ≤ k := le_trans le_self_add hm
    -- the dossiers' node facts (source and image)
    obtain ⟨hadjI, htvI, hDt, hDv⟩ := dossV_succ htbl hW hWd hv hm hDi
    have hvs : IsSemitermVec LAct k n (termShiftVec LAct k v) := hv.termShiftVec
    obtain ⟨hadjJ, htvJ, hDt', hDv'⟩ := dossV_succ htbl hW hWd hvs hm hDj
    rw [nth_termShiftVec hv.isUTerm hlt] at hadjJ hDt' hDv'
    rw [descCountT_termShift Wd n _ ht] at hadjJ hDv'
    -- the arithmetic of the bounds
    have h2t : 2 * termLen LAct v.[k - (m + 1)] ≤
        2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) :=
      mul_le_mul_of_nonneg_left le_self_add zero_le
    have hD1 : (1 : V) ≤ 2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1 := le_add_self
    have hctD : descCountT Wd n v.[k - (m + 1)] + 1 ≤
        2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1 :=
      le_trans hct_le (le_trans h2t le_self_add)
    -- the entry's pass
    obtain ⟨hokT, hhT, hfT⟩ := ih _ hlt (i + 1) (j + 1) yt E Γ hyt
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (le_trans h2t le_self_add)) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + 2 * termLen LAct v.[k - (m + 1)] + 1 = i + (2 * termLen LAct v.[k - (m + 1)] + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) (add_le_add h2t (le_refl (1 : V)))) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * termLen LAct v.[k - (m + 1)] + 1 = j + (2 * termLen LAct v.[k - (m + 1)] + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) (add_le_add h2t (le_refl (1 : V)))) (le_refl (1 : V))) hEj),
       hΓ⟩ hDt hDt'
    obtain ⟨hndT, hsT⟩ := passTGraph_noDrop_shifts W 2 n hWp _ ht (i + 1) (j + 1) yt hyt
    have hsub₁ : Γ ⊆ finalCtx Γ yt := subset_finalCtx_of_shiftsV_zero hndT hsT
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yt) := finalCtx_isFormulaSet 8 htbl hΓ hokT
    -- the tail's pass
    have hSig : 2 * listSum (termLenVec LAct m (takeLast v m)) + 1 ≤
        2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left le_add_self zero_le) (le_refl (1 : V))
    obtain ⟨hokV, hhV, hfV⟩ := hrest (i + 1 + descCountT Wd n v.[k - (m + 1)]) (j + 1 + descCountT Wd n v.[k - (m + 1)])
      yv E (finalCtx Γ yt) hyv
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + descCountT Wd n v.[k - (m + 1)] + (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
          i + (descCountT Wd n v.[k - (m + 1)] + 1 + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i)
            (add_le_add (add_le_add hct_le (le_refl (2 * listSum (termLenVec LAct m (takeLast v m))))) (le_refl (1 : V))))
          (le_refl (1 : V)))
          (le_trans (le_of_eq (show i + (2 * termLen LAct v.[k - (m + 1)] + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
            i + (2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1) + 1 by ring)) hEi)),
       le_trans (le_of_eq (show j + 1 + descCountT Wd n v.[k - (m + 1)] + (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
          j + (descCountT Wd n v.[k - (m + 1)] + 1 + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j)
            (add_le_add (add_le_add hct_le (le_refl (2 * listSum (termLenVec LAct m (takeLast v m))))) (le_refl (1 : V))))
          (le_refl (1 : V)))
          (le_trans (le_of_eq (show j + (2 * termLen LAct v.[k - (m + 1)] + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
            j + (2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1) + 1 by ring)) hEj)),
       hΓ₁⟩ (hDv.mono hsub₁) (hDv'.mono hsub₁)
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts hWp hv m hmk _ _ yv hyv
    have hsub₂ : finalCtx Γ yt ⊆ finalCtx (finalCtx Γ yt) yv := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₂ : IsFormulaSet LAct (finalCtx (finalCtx Γ yt) yv) := finalCtx_isFormulaSet 8 htbl hΓ₁ hokV
    -- the witness lengths
    have hcTm : termLen LAct (cTV m) ≤ E := E_cT_le_two (le_trans hmk hk) h8
    have hcTn : termLen LAct (cTV n) ≤ E := E_cT_n hE
    have hrI : termLen LAct (vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m) ≤ E := E_vRef_ct hctD hEi
    have hrJ : termLen LAct (vRef (j + 1 + descCountT Wd n v.[k - (m + 1)]) m) ≤ E := E_vRef_ct hctD hEj
    -- row 38 then row 39 on the source tail: `utvPiFact (cT m) ⟨tail⟩ᵢ`
    have e38 : mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] =
        mkStep walkPieces 38 ?[cTV m, cTV n, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] := by
      rw [hWp, mkStep_certPieces_38]
    have htv : neg LAct (tvPiFact (cTV m) (cTV n) (vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m)) ∈
        finalCtx (finalCtx Γ yt) yv :=
      hsub₂ (hsub₁ (dossV_tvPi htbl hW hWd hv hmk hDv))
    obtain ⟨ok38, tag38, ctx38⟩ := ok_isUTermVecOfSemitermVecLAct htbl hW rfl hΓ₂ (cTV_semiterm_LAct 0 _) hcTm
      (cTV_semiterm_LAct 0 _) hcTn (isSemiterm_vRef _ _) hrI htv
    rw [← e38] at ok38 tag38 ctx38
    have hΓ₃ := isFormulaSet_ctxAfter 8 htbl ok38
    have e39 : mkStep W 39 ?[cTV m, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] =
        mkStep walkPieces 39 ?[cTV m, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] := by
      rw [hWp, mkStep_certPieces_39]
    obtain ⟨ok39, tag39, ctx39⟩ := ok_isUTermVecSigmaPiLAct htbl hW rfl hΓ₃ (cTV_semiterm_LAct 0 _) hcTm
      (isSemiterm_vRef _ _) hrI (by rw [ctx38]; exact mem_insert_self')
    rw [← e39] at ok39 tag39 ctx39
    have hΓ₄ := isFormulaSet_ctxAfter 8 htbl ok39
    have hlift : ∀ x, x ∈ finalCtx (finalCtx Γ yt) yv →
        x ∈ ctxAfter (ctxAfter (finalCtx (finalCtx Γ yt) yv)
          (mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m]))
          (mkStep W 39 ?[cTV m, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m]) := by
      intro x hx; rw [ctx39, ctx38]; exact mem_insert_of_mem' (mem_insert_of_mem' hx)
    -- the adjoin certificate
    obtain ⟨okA, tagA, ctxA⟩ := cok_tshvAdjCert htbl hC hWp hΓ₄
      (cTV_semiterm_LAct 0 _) hcTn (cTV_semiterm_LAct 0 _) hcTm (isSemiterm_vRef _ _) hrI
      (by simp) (E_fvar hEi) (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar_succ hD1 hEj)
      (isSemiterm_vRef _ _) hrJ (by simp) (E_fvar hEj)
      (hlift _ (hsub₂ (hsub₁ (dossT_tPi htbl hW hWd ht hDt))))
      (by rw [ctx39]; exact mem_insert_self')
      (hlift _ (hsub₂ hfT))
      (hlift _ hfV)
      (hlift _ (hsub₂ (hsub₁ hadjI)))
      (hlift _ (hsub₂ (hsub₁ hadjJ)))
    rw [vAdjSteps, vAdjRow, if_pos rfl, vAdjWits, if_pos rfl]
    refine ⟨listOK_appendV hokT (listOK_appendV hokV (listOK_cons ok38 (listOK_cons ok39 (listOK_single okA)))),
      hornOnly_appendV hhT (hornOnly_appendV hhV (hornOnly_cons (Or.inl tag38)
        (hornOnly_cons (Or.inl tag39) (hornOnly_single (Or.inl tagA))))), ?_⟩
    rw [finalCtx_appendV, finalCtx_three, ctxA,
      vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)),
      vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)), cTV_succ]
    exact mem_insert_self'

set_option maxHeartbeats 4000000 in
/-- **The term-level shift pass is applicable and certifies `tshFact &j &i`.** -/
theorem passTGraph_shift_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (n : V) :
    ∀ t, IsSemiterm LAct n t → TShiftOK tbl Wd W n t := by
  have hW : WalkTable tbl := hC.walkTable
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z _ i j y E Γ hy hP hDi hDj
    rw [termLen_bvar] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassTGraph.bvar_iff.mp hy, tLeafSteps, tLeafRow, if_pos rfl, if_pos rfl]
    rw [termShift_bvar] at hDj
    obtain ⟨hbI, _⟩ := dossT_bvar htbl hW hWd hDi
    obtain ⟨hbJ, _⟩ := dossT_bvar htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_termShiftBvarCert htbl hC hWp hΓ (cTV_semiterm_LAct 0 _) (E_cT_leaf hE)
      (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hbI hbJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · intro a i j y E Γ hy hP hDi hDj
    rw [termLen_fvar] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassTGraph.fvar_iff.mp hy, tLeafSteps, tLeafRow, if_pos rfl, if_neg (by simp)]
    rw [termShift_fvar] at hDj
    obtain ⟨hfI, _⟩ := dossT_fvar htbl hW hWd hDi
    obtain ⟨hfJ, _⟩ := dossT_fvar htbl hW hWd hDj
    rw [cTV_succ] at hfJ
    obtain ⟨hok, htag, hctx⟩ := cok_termShiftFvarCert htbl hC hWp hΓ (cTV_semiterm_LAct 0 _) (E_cT_leaf hE)
      (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hfI hfJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · intro k f v hkf hv ih i j y E Γ hy hP hDi hDj
    rw [termLen_func hkf hv.isUTerm] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yv, _, hyv, rfl⟩ := PassTGraph.func_iff.mp hy
    rw [tFuncSteps_eq, tFuncRow, if_pos rfl]
    have h8 : (8 : V) ≤ E := E_eight hE
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨hfI, _, huI, hDvI⟩ := dossT_func htbl hW hWd hkf hv hDi
    rw [termShift_func hkf hv.isUTerm] at hDj
    obtain ⟨hfJ, _, _, hDvJ⟩ := dossT_func htbl hW hWd hkf hv.termShiftVec hDj
    obtain ⟨_, hrest⟩ := passVGraph_shift_ok_aux htbl hC hWd hWp n (arity_le_two hkf) hv ih k le_rfl
    rw [htl] at hrest
    have hSig : 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * (listSum (termLenVec LAct k v) + 1) := by
      rw [mul_add, mul_one]; exact add_le_add (le_refl _) (by norm_num)
    obtain ⟨hokV, hhV, hfV⟩ := hrest (i + 1) (j + 1) yv E Γ hyv
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEi,
       le_trans (le_of_eq (show j + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = j + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEj,
       hΓ⟩ hDvI hDvJ
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts hWp hv k le_rfl _ _ yv hyv
    have hsub₁ : Γ ⊆ finalCtx Γ yv := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yv) := finalCtx_isFormulaSet 8 htbl hΓ hokV
    have ef : mkStep W (funcRow k f) 0 = mkStep walkPieces (funcRow k f) 0 := by rw [hWp, mkStep_certPieces_funcRow]
    obtain ⟨okF, tagF, ctxF, hEk, hEf⟩ := funcConst_ok htbl hW rfl hkf h8 hΓ₁
    rw [← ef] at okF tagF ctxF
    have hΓ₂ := isFormulaSet_ctxAfter 8 htbl okF
    have hD1 : (1 : V) ≤ 2 * (listSum (termLenVec LAct k v) + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    obtain ⟨okS, tagS, ctxS⟩ := cok_termShiftFuncCert htbl hC hWp hΓ₂ (by simp) (E_fvar hEi) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hEf (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi) (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEj)
      (by simp) (E_fvar hEj)
      (by rw [ctxF]; exact mem_insert_self')
      (by rw [ctxF]; exact mem_insert_of_mem' (hsub₁ huI))
      (by rw [ctxF]; exact mem_insert_of_mem' (hsub₁ hfI))
      (by rw [ctxF]; exact mem_insert_of_mem' hfV)
      (by rw [ctxF]; exact mem_insert_of_mem' (hsub₁ hfJ))
    refine ⟨listOK_appendV hokV (listOK_cons okF (listOK_single okS)),
      hornOnly_appendV hhV (hornOnly_cons (Or.inl tagF) (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_cons, finalCtx_single, ctxS]
    exact mem_insert_self'

/-- The vector-level shift pass, standalone. -/
theorem passVGraph_shift_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (n : V) {k v : V} (hk : k ≤ 2)
    (hv : IsSemitermVec LAct k n v) {m : V} (hm : m ≤ k) :
    ∀ i j z E Γ : V, PassVGraph W 2 n k v m i j z →
      PassPre (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) n i j E Γ →
      DossV Wd Γ n k v m i → DossV Wd Γ n k (termShiftVec LAct k v) m j →
      PassPost tbl E Γ z (tshvFact (vRef j m) (cTV m) (vRef i m)) :=
  (passVGraph_shift_ok_aux htbl hC hWd hWp n hk hv
    (fun a ha ↦ passTGraph_shift_ok htbl hC hWd hWp n _ (hv.nth ha)) m hm).2

end termShiftOK


/-! ### 4.3 The term-level IDENTIFICATION pass is applicable and certifies `eqFactB &i &j`

The same induction at every `ν ≠ 2`: two dossiers of the SAME term (at `i` and at `j`), the
`eqOf*` rows, conclusion `eqFactB &i &j` (`eqFactB ⟨v⟩ᵢ ⟨v⟩ⱼ` at the vector level). The formula
pass's `neg` family runs it at `ν = 1` under every atom.
-/

section termEqOK

/-- The term-level invariant of the identification pass. -/
def TEqOK (tbl Wd W ν n t : V) : Prop :=
  ∀ i j y E Γ : V, PassTGraph W ν n t i j y → PassPre (2 * termLen LAct t) n i j E Γ →
    DossT Wd Γ n t i → DossT Wd Γ n t j → PassPost tbl E Γ y (eqFactB (^&i) (^&j))
instance tEqOK_definable : 𝚷₁.Definable (fun v : Fin 6 → V ↦ TEqOK (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold TEqOK; definability

set_option maxHeartbeats 4000000 in
/-- **The vector-level identification pass is applicable**, tail first. -/
lemma passVGraph_eq_ok_aux {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {ν : V} (hν : ν ≠ 2) (n : V) {k v : V} (hk : k ≤ 2)
    (hv : IsSemitermVec LAct k n v) (ih : ∀ a < k, TEqOK tbl Wd W ν n v.[a]) :
    ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i j z E Γ : V, PassVGraph W ν n k v m i j z →
      PassPre (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) n i j E Γ →
      DossV Wd Γ n k v m i → DossV Wd Γ n k v m j →
      PassPost tbl E Γ z (eqFactB (vRef i m) (vRef j m)) := by
  have hW : WalkTable tbl := hC.walkTable
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i j z E Γ hz hP hDi hDj
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassVGraph.zero_iff.mp hz, vNilSteps, vNilRow, if_neg hν, vRef_zero, vRef_zero, ← cTV_zero]
    have h8 : (8 : V) ≤ E := E_eight hE
    obtain ⟨hok, htag, hctx⟩ := cok_eqRefl htbl hC hWp hΓ (wx := cTV 0) (cTV_semiterm_LAct 0 0)
      (E_cT_le_two (by norm_num) h8)
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]
    exact mem_insert_self'
  | succ m ihm =>
    intro hm
    have hvlen : len v = k := hv.lh
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    obtain ⟨hU, hrest⟩ := ihm (le_trans le_self_add hm)
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    intro i j z E Γ hz hP hDi hDj
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := PassVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    have hct : descCountT W n (nthFromEnd v m) = descCountT Wd n v.[k - (m + 1)] := by
      rw [hnth', hWp, hWd]; exact descCountT_certPieces n _ ht
    rw [hnth'] at hyt
    rw [hct] at hyv ⊢
    rw [htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    have hct_le : descCountT Wd n v.[k - (m + 1)] + 1 ≤ 2 * termLen LAct v.[k - (m + 1)] :=
      descCountT_walk_le htbl hW hWd ht
    have h8 : (8 : V) ≤ E := E_eight hE
    have hmk : m ≤ k := le_trans le_self_add hm
    -- the dossiers' node facts (the same vector at `i` and at `j`)
    obtain ⟨hadjI, htvI, hDt, hDv⟩ := dossV_succ htbl hW hWd hv hm hDi
    obtain ⟨hadjJ, htvJ, hDt', hDv'⟩ := dossV_succ htbl hW hWd hv hm hDj
    -- the arithmetic of the bounds
    have h2t : 2 * termLen LAct v.[k - (m + 1)] ≤
        2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) :=
      mul_le_mul_of_nonneg_left le_self_add zero_le
    have hD1 : (1 : V) ≤ 2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1 := le_add_self
    have hctD : descCountT Wd n v.[k - (m + 1)] + 1 ≤
        2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1 :=
      le_trans hct_le (le_trans h2t le_self_add)
    -- the entry's pass
    obtain ⟨hokT, hhT, hfT⟩ := ih _ hlt (i + 1) (j + 1) yt E Γ hyt
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (le_trans h2t le_self_add)) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + 2 * termLen LAct v.[k - (m + 1)] + 1 = i + (2 * termLen LAct v.[k - (m + 1)] + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) (add_le_add h2t (le_refl (1 : V)))) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * termLen LAct v.[k - (m + 1)] + 1 = j + (2 * termLen LAct v.[k - (m + 1)] + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) (add_le_add h2t (le_refl (1 : V)))) (le_refl (1 : V))) hEj),
       hΓ⟩ hDt hDt'
    obtain ⟨hndT, hsT⟩ := passTGraph_noDrop_shifts W ν n hWp _ ht (i + 1) (j + 1) yt hyt
    have hsub₁ : Γ ⊆ finalCtx Γ yt := subset_finalCtx_of_shiftsV_zero hndT hsT
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yt) := finalCtx_isFormulaSet 8 htbl hΓ hokT
    -- the tail's pass
    have hSig : 2 * listSum (termLenVec LAct m (takeLast v m)) + 1 ≤
        2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left le_add_self zero_le) (le_refl (1 : V))
    obtain ⟨hokV, hhV, hfV⟩ := hrest (i + 1 + descCountT Wd n v.[k - (m + 1)]) (j + 1 + descCountT Wd n v.[k - (m + 1)])
      yv E (finalCtx Γ yt) hyv
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + descCountT Wd n v.[k - (m + 1)] + (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
          i + (descCountT Wd n v.[k - (m + 1)] + 1 + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i)
            (add_le_add (add_le_add hct_le (le_refl (2 * listSum (termLenVec LAct m (takeLast v m))))) (le_refl (1 : V))))
          (le_refl (1 : V)))
          (le_trans (le_of_eq (show i + (2 * termLen LAct v.[k - (m + 1)] + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
            i + (2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1) + 1 by ring)) hEi)),
       le_trans (le_of_eq (show j + 1 + descCountT Wd n v.[k - (m + 1)] + (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
          j + (descCountT Wd n v.[k - (m + 1)] + 1 + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j)
            (add_le_add (add_le_add hct_le (le_refl (2 * listSum (termLenVec LAct m (takeLast v m))))) (le_refl (1 : V))))
          (le_refl (1 : V)))
          (le_trans (le_of_eq (show j + (2 * termLen LAct v.[k - (m + 1)] + 2 * listSum (termLenVec LAct m (takeLast v m)) + 1) + 1 =
            j + (2 * (termLen LAct v.[k - (m + 1)] + listSum (termLenVec LAct m (takeLast v m))) + 1) + 1 by ring)) hEj)),
       hΓ₁⟩ (hDv.mono hsub₁) (hDv'.mono hsub₁)
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts hWp hv m hmk _ _ yv hyv
    have hsub₂ : finalCtx Γ yt ⊆ finalCtx (finalCtx Γ yt) yv := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₂ : IsFormulaSet LAct (finalCtx (finalCtx Γ yt) yv) := finalCtx_isFormulaSet 8 htbl hΓ₁ hokV
    -- the witness lengths
    have hcTm : termLen LAct (cTV m) ≤ E := E_cT_le_two (le_trans hmk hk) h8
    have hcTn : termLen LAct (cTV n) ≤ E := E_cT_n hE
    have hrI : termLen LAct (vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m) ≤ E := E_vRef_ct hctD hEi
    have hrJ : termLen LAct (vRef (j + 1 + descCountT Wd n v.[k - (m + 1)]) m) ≤ E := E_vRef_ct hctD hEj
    -- rows 38/39 on the source tail (emitted by the shared `vAdjSteps`; their facts are unused here)
    have e38 : mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] =
        mkStep walkPieces 38 ?[cTV m, cTV n, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] := by
      rw [hWp, mkStep_certPieces_38]
    have htv : neg LAct (tvPiFact (cTV m) (cTV n) (vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m)) ∈
        finalCtx (finalCtx Γ yt) yv :=
      hsub₂ (hsub₁ (dossV_tvPi htbl hW hWd hv hmk hDv))
    obtain ⟨ok38, tag38, ctx38⟩ := ok_isUTermVecOfSemitermVecLAct htbl hW rfl hΓ₂ (cTV_semiterm_LAct 0 _) hcTm
      (cTV_semiterm_LAct 0 _) hcTn (isSemiterm_vRef _ _) hrI htv
    rw [← e38] at ok38 tag38 ctx38
    have hΓ₃ := isFormulaSet_ctxAfter 8 htbl ok38
    have e39 : mkStep W 39 ?[cTV m, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] =
        mkStep walkPieces 39 ?[cTV m, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m] := by
      rw [hWp, mkStep_certPieces_39]
    obtain ⟨ok39, tag39, ctx39⟩ := ok_isUTermVecSigmaPiLAct htbl hW rfl hΓ₃ (cTV_semiterm_LAct 0 _) hcTm
      (isSemiterm_vRef _ _) hrI (by rw [ctx38]; exact mem_insert_self')
    rw [← e39] at ok39 tag39 ctx39
    have hΓ₄ := isFormulaSet_ctxAfter 8 htbl ok39
    have hlift : ∀ x, x ∈ finalCtx (finalCtx Γ yt) yv →
        x ∈ ctxAfter (ctxAfter (finalCtx (finalCtx Γ yt) yv)
          (mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m]))
          (mkStep W 39 ?[cTV m, vRef (i + 1 + descCountT Wd n v.[k - (m + 1)]) m]) := by
      intro x hx; rw [ctx39, ctx38]; exact mem_insert_of_mem' (mem_insert_of_mem' hx)
    -- the adjoin identification
    obtain ⟨okA, tagA, ctxA⟩ := cok_eqOfAdj htbl hC hWp hΓ₄
      (by simp) (E_fvar_succ hD1 hEi) (isSemiterm_vRef _ _) hrI (by simp) (E_fvar hEi)
      (by simp) (E_fvar_succ hD1 hEj) (isSemiterm_vRef _ _) hrJ (by simp) (E_fvar hEj)
      (hlift _ (hsub₂ (hsub₁ hadjI)))
      (hlift _ (hsub₂ (hsub₁ hadjJ)))
      (hlift _ (hsub₂ hfT))
      (hlift _ hfV)
    rw [vAdjSteps, vAdjRow, if_neg hν, vAdjWits, if_neg hν]
    refine ⟨listOK_appendV hokT (listOK_appendV hokV (listOK_cons ok38 (listOK_cons ok39 (listOK_single okA)))),
      hornOnly_appendV hhT (hornOnly_appendV hhV (hornOnly_cons (Or.inl tag38)
        (hornOnly_cons (Or.inl tag39) (hornOnly_single (Or.inl tagA))))), ?_⟩
    rw [finalCtx_appendV, finalCtx_three, ctxA,
      vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)),
      vRef_of_ne (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))]
    exact mem_insert_self'

set_option maxHeartbeats 4000000 in
/-- **The term-level identification pass is applicable and certifies `eqFactB &i &j`.** -/
theorem passTGraph_eq_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {ν : V} (hν : ν ≠ 2) (n : V) :
    ∀ t, IsSemiterm LAct n t → TEqOK tbl Wd W ν n t := by
  have hW : WalkTable tbl := hC.walkTable
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · definability
  · intro z _ i j y E Γ hy hP hDi hDj
    rw [termLen_bvar] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassTGraph.bvar_iff.mp hy, tLeafSteps, tLeafRow, if_neg hν, if_pos rfl]
    obtain ⟨hbI, _⟩ := dossT_bvar htbl hW hWd hDi
    obtain ⟨hbJ, _⟩ := dossT_bvar htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_eqOfBvar htbl hC hWp hΓ (cTV_semiterm_LAct 0 _) (E_cT_leaf hE)
      (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hbI hbJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · intro a i j y E Γ hy hP hDi hDj
    rw [termLen_fvar] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassTGraph.fvar_iff.mp hy, tLeafSteps, tLeafRow, if_neg hν, if_neg (by simp)]
    obtain ⟨hfI, _⟩ := dossT_fvar htbl hW hWd hDi
    obtain ⟨hfJ, _⟩ := dossT_fvar htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_eqOfFvar htbl hC hWp hΓ (cTV_semiterm_LAct 0 _) (E_cT_leaf hE)
      (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hfI hfJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · intro k f v hkf hv ih i j y E Γ hy hP hDi hDj
    rw [termLen_func hkf hv.isUTerm] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yv, _, hyv, rfl⟩ := PassTGraph.func_iff.mp hy
    rw [tFuncSteps_eq, tFuncRow, if_neg hν]
    have h8 : (8 : V) ≤ E := E_eight hE
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨hfI, _, _, hDvI⟩ := dossT_func htbl hW hWd hkf hv hDi
    obtain ⟨hfJ, _, _, hDvJ⟩ := dossT_func htbl hW hWd hkf hv hDj
    obtain ⟨_, hrest⟩ := passVGraph_eq_ok_aux htbl hC hWd hWp hν n (arity_le_two hkf) hv ih k le_rfl
    rw [htl] at hrest
    have hSig : 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * (listSum (termLenVec LAct k v) + 1) := by
      rw [mul_add, mul_one]; exact add_le_add (le_refl _) (by norm_num)
    obtain ⟨hokV, hhV, hfV⟩ := hrest (i + 1) (j + 1) yv E Γ hyv
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEi,
       le_trans (le_of_eq (show j + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = j + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEj,
       hΓ⟩ hDvI hDvJ
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts hWp hv k le_rfl _ _ yv hyv
    have hsub₁ : Γ ⊆ finalCtx Γ yv := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yv) := finalCtx_isFormulaSet 8 htbl hΓ hokV
    have ef : mkStep W (funcRow k f) 0 = mkStep walkPieces (funcRow k f) 0 := by rw [hWp, mkStep_certPieces_funcRow]
    obtain ⟨okF, tagF, ctxF, hEk, hEf⟩ := funcConst_ok htbl hW rfl hkf h8 hΓ₁
    rw [← ef] at okF tagF ctxF
    have hΓ₂ := isFormulaSet_ctxAfter 8 htbl okF
    have hD1 : (1 : V) ≤ 2 * (listSum (termLenVec LAct k v) + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    obtain ⟨okS, tagS, ctxS⟩ := cok_eqOfFunc htbl hC hWp hΓ₂ (by simp) (E_fvar hEi) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hEf (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi) (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEj)
      (by simp) (E_fvar hEj)
      (by rw [ctxF]; exact mem_insert_of_mem' (hsub₁ hfI))
      (by rw [ctxF]; exact mem_insert_of_mem' (hsub₁ hfJ))
      (by rw [ctxF]; exact mem_insert_of_mem' hfV)
    refine ⟨listOK_appendV hokV (listOK_cons okF (listOK_single okS)),
      hornOnly_appendV hhV (hornOnly_cons (Or.inl tagF) (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_cons, finalCtx_single, ctxS]
    exact mem_insert_self'

/-- The vector-level identification pass, standalone. -/
theorem passVGraph_eq_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {ν : V} (hν : ν ≠ 2) (n : V) {k v : V} (hk : k ≤ 2)
    (hv : IsSemitermVec LAct k n v) {m : V} (hm : m ≤ k) :
    ∀ i j z E Γ : V, PassVGraph W ν n k v m i j z →
      PassPre (2 * listSum (termLenVec LAct m (takeLast v m)) + 1) n i j E Γ →
      DossV Wd Γ n k v m i → DossV Wd Γ n k v m j →
      PassPost tbl E Γ z (eqFactB (vRef i m) (vRef j m)) :=
  (passVGraph_eq_ok_aux htbl hC hWd hWp hν n hk hv
    (fun a ha ↦ passTGraph_eq_ok htbl hC hWd hWp hν n _ (hv.nth ha)) m hm).2

end termEqOK


/-! ### 4.4 The formula-level SHIFT pass is applicable and certifies `shiftFact &j &i`

`IsSemiformula.pi1_structural_induction` on the SOURCE; at each node the two dossiers'
decomposition lemmas supply the shape facts (`dossF_*`), the children's passes supply the certified
pairs, and the node's `cok_shift*Cert` row fires. The offsets of the pass are computed over
`certPieces`; the dossiers count over `walkPieces` (`descCountF_certPieces`, `outCount_shift`).
-/

section formulaShiftOK

lemma E_fvar_off {i c D E : V} (hc : c + 1 ≤ D) (h : i + D + 1 ≤ E) : termLen LAct (^&(i + c + 1) : V) ≤ E :=
  termLen_fvar_le (le_trans (le_of_eq (show i + c + 1 + 1 = i + (c + 1) + 1 by ring))
    (le_trans (add_le_add (add_le_add (le_refl i) hc) (le_refl (1 : V))) h))

/-- `|p| ≤ |p ⋏ q|`-shaped bounds, as the pass's `PassPre` needs them. -/
lemma two_left_le {a b : V} : 2 * a ≤ 2 * (a + b + 1) :=
  mul_le_mul_of_nonneg_left (le_trans le_self_add le_self_add) zero_le
lemma two_right_le {a b : V} : 2 * b ≤ 2 * (a + b + 1) :=
  mul_le_mul_of_nonneg_left (le_trans le_add_self le_self_add) zero_le
lemma two_succ_le {a : V} : 2 * a + 1 ≤ 2 * (a + 1) := by
  rw [mul_add, mul_one]; exact add_le_add (le_refl (2 * a)) (by norm_num)
lemma two_right_succ_le {a b : V} : 2 * b + 1 ≤ 2 * (a + b + 1) :=
  le_trans (add_le_add (le_refl (2 * b)) (by norm_num : (1 : V) ≤ 2))
    (le_trans (le_of_eq (show 2 * b + 2 = 2 * (b + 1) by ring))
      (mul_le_mul_of_nonneg_left (add_le_add le_add_self (le_refl (1 : V))) zero_le))

set_option maxHeartbeats 4000000 in
/-- **The shift pass of a formula is applicable and certifies `shiftFact &j &i`.** -/
theorem passFGraph_shift_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) :
    ∀ {n r : V}, IsSemiformula LAct n r → ∀ i j y E Γ : V, PassFGraph W 2 n r i j y →
      PassPre (2 * formulaLen LAct r) n i j E Γ → DossF Wd Γ n r i → DossF Wd Γ n (shift LAct r) j →
      PassPost tbl E Γ y (shiftFact (^&j) (^&i)) := by
  have hW : WalkTable tbl := hC.walkTable
  have h21 : (2 : V) ≠ 1 := by norm_num
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i j y E Γ : V, PassFGraph W 2 n r i j y →
      PassPre (2 * formulaLen LAct r) n i j E Γ → DossF Wd Γ n r i → DossF Wd Γ n (shift LAct r) j →
      PassPost tbl E Γ y (shiftFact (^&j) (^&i)))
  · definability
  · -- rel
    intro n k R v hkR hv i j y E Γ hy hP hDi hDj
    rw [formulaLen_rel hkR hv.isUTerm] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.rel_iff.mp hy, fAtomSteps, if_neg h21, show fRow (2 : V) 0 = 108 by norm_num [fRow]]
    have h8 : (8 : V) ≤ E := E_eight hE
    have hD1 : (1 : V) ≤ 2 * (listSum (termLenVec LAct k v) + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hSig : 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * (listSum (termLenVec LAct k v) + 1) := by
      rw [mul_add, mul_one]; exact add_le_add (le_refl _) (by norm_num)
    obtain ⟨hrI, _, huI, hDvI⟩ := dossF_rel htbl hW hWd hkR hv hDi
    rw [shift_rel hkR hv.isUTerm] at hDj
    obtain ⟨hrJ, _, _, hDvJ⟩ := dossF_rel htbl hW hWd hkR hv.termShiftVec hDj
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hV := passVGraph_shift_ok htbl hC hWd hWp n (rel_arity_le_two hkR) hv (le_refl k) (i + 1) (j + 1) _ E Γ
      (passV_graph hv (le_refl k))
    rw [htl] at hV
    obtain ⟨hokV, hhV, hfV⟩ := hV
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEi,
       le_trans (le_of_eq (show j + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = j + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEj,
       hΓ⟩ hDvI hDvJ
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts hWp hv k le_rfl _ _ _ (passV_graph hv (le_refl k))
    have hsub₁ : Γ ⊆ finalCtx Γ (passV W 2 n k v k (i + 1) (j + 1)) := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokV
    have er : mkStep W (relRow R) 0 = mkStep walkPieces (relRow R) 0 := by rw [hWp, mkStep_certPieces_relRow]
    obtain ⟨okR, tagR, ctxR, hEk, hER⟩ := relConst_ok htbl hW rfl hkR h8 hΓ₁
    rw [← er] at okR tagR ctxR
    have hΓ₂ := isFormulaSet_ctxAfter 8 htbl okR
    obtain ⟨okS, tagS, ctxS⟩ := cok_shiftRelCert htbl hC hWp hΓ₂ (by simp) (E_fvar hEi) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi) (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEj)
      (by simp) (E_fvar hEj)
      (by rw [ctxR]; exact mem_insert_self')
      (by rw [ctxR]; exact mem_insert_of_mem' (hsub₁ huI))
      (by rw [ctxR]; exact mem_insert_of_mem' (hsub₁ hrI))
      (by rw [ctxR]; exact mem_insert_of_mem' hfV)
      (by rw [ctxR]; exact mem_insert_of_mem' (hsub₁ hrJ))
    refine ⟨listOK_appendV hokV (listOK_cons okR (listOK_single okS)),
      hornOnly_appendV hhV (hornOnly_cons (Or.inl tagR) (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_cons, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- nrel
    intro n k R v hkR hv i j y E Γ hy hP hDi hDj
    rw [formulaLen_nrel hkR hv.isUTerm] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.nrel_iff.mp hy, fAtomSteps, if_neg h21, show fRow (2 : V) 1 = 109 by norm_num [fRow]]
    have h8 : (8 : V) ≤ E := E_eight hE
    have hD1 : (1 : V) ≤ 2 * (listSum (termLenVec LAct k v) + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hSig : 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * (listSum (termLenVec LAct k v) + 1) := by
      rw [mul_add, mul_one]; exact add_le_add (le_refl _) (by norm_num)
    obtain ⟨hrI, _, huI, hDvI⟩ := dossF_nrel htbl hW hWd hkR hv hDi
    rw [shift_nrel hkR hv.isUTerm] at hDj
    obtain ⟨hrJ, _, _, hDvJ⟩ := dossF_nrel htbl hW hWd hkR hv.termShiftVec hDj
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hV := passVGraph_shift_ok htbl hC hWd hWp n (rel_arity_le_two hkR) hv (le_refl k) (i + 1) (j + 1) _ E Γ
      (passV_graph hv (le_refl k))
    rw [htl] at hV
    obtain ⟨hokV, hhV, hfV⟩ := hV
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEi,
       le_trans (le_of_eq (show j + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = j + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEj,
       hΓ⟩ hDvI hDvJ
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts hWp hv k le_rfl _ _ _ (passV_graph hv (le_refl k))
    have hsub₁ : Γ ⊆ finalCtx Γ (passV W 2 n k v k (i + 1) (j + 1)) := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokV
    have er : mkStep W (relRow R) 0 = mkStep walkPieces (relRow R) 0 := by rw [hWp, mkStep_certPieces_relRow]
    obtain ⟨okR, tagR, ctxR, hEk, hER⟩ := relConst_ok htbl hW rfl hkR h8 hΓ₁
    rw [← er] at okR tagR ctxR
    have hΓ₂ := isFormulaSet_ctxAfter 8 htbl okR
    obtain ⟨okS, tagS, ctxS⟩ := cok_shiftNRelCert htbl hC hWp hΓ₂ (by simp) (E_fvar hEi) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi) (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEj)
      (by simp) (E_fvar hEj)
      (by rw [ctxR]; exact mem_insert_self')
      (by rw [ctxR]; exact mem_insert_of_mem' (hsub₁ huI))
      (by rw [ctxR]; exact mem_insert_of_mem' (hsub₁ hrI))
      (by rw [ctxR]; exact mem_insert_of_mem' hfV)
      (by rw [ctxR]; exact mem_insert_of_mem' (hsub₁ hrJ))
    refine ⟨listOK_appendV hokV (listOK_cons okR (listOK_single okS)),
      hornOnly_appendV hhV (hornOnly_cons (Or.inl tagR) (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_cons, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- verum
    intro n i j y E Γ hy hP hDi hDj
    rw [formulaLen_verum] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.verum_iff.mp hy, fConstSteps, show fRow (2 : V) 2 = 110 by norm_num [fRow]]
    rw [shift_verum] at hDj
    obtain ⟨hvI, _⟩ := dossF_verum htbl hW hWd hDi
    obtain ⟨hvJ, _⟩ := dossF_verum htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_shiftVerumCert htbl hC hWp hΓ (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hvI hvJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · -- falsum
    intro n i j y E Γ hy hP hDi hDj
    rw [formulaLen_falsum] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.falsum_iff.mp hy, fConstSteps, show fRow (2 : V) 3 = 111 by norm_num [fRow]]
    rw [shift_falsum] at hDj
    obtain ⟨hvI, _⟩ := dossF_falsum htbl hW hWd hDi
    obtain ⟨hvJ, _⟩ := dossF_falsum htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_shiftFalsumCert htbl hC hWp hΓ (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hvI hvJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · -- and
    intro n p q hp hq ihp ihq i j y E Γ hy hP hDi hDj
    rw [formulaLen_and hp.isUFormula hq.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yp, yq, _, _, hp', hq', rfl⟩ := PassFGraph.and_iff.mp hy
    have hcq : descCountF W n q = descCountF Wd n q := by rw [hWp, hWd]; exact descCountF_certPieces hq
    have hdq : outCount W 2 n q = descCountF Wd n q := by rw [outCount_shift hq, hcq]
    rw [hcq, hdq] at hp' ⊢
    rw [fBinSteps, show fRow (2 : V) 4 = 112 by norm_num [fRow]]
    have hcq_le : descCountF Wd n q + 1 ≤ 2 * formulaLen LAct q := descCountF_walk_le htbl hW hWd hq
    have hcqD : descCountF Wd n q + 1 ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) := le_trans hcq_le two_right_le
    obtain ⟨handI, _, hDq, hDp⟩ := dossF_and htbl hW hWd hp hq hDi
    rw [shift_and hp.isUFormula hq.isUFormula] at hDj
    obtain ⟨handJ, _, hDq', hDp'⟩ := dossF_and htbl hW hWd hp.shift hq.shift hDj
    rw [descCountF_shift Wd hq] at handJ hDp'
    -- the left child's pass (at `i + cq + 1`)
    obtain ⟨hokP, hhP, hfP⟩ := ihp (i + descCountF Wd n q + 1) (j + descCountF Wd n q + 1) yp E Γ hp'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_left_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          i + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl i) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEi)),
       le_trans (le_of_eq (show j + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          j + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl j) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEj)),
       hΓ⟩ hDp hDp'
    obtain ⟨hndP, hsP⟩ := passFGraph_noDrop_shifts W (Or.inr rfl) hWp hp _ _ yp hp'
    have hsub₁ : Γ ⊆ finalCtx Γ yp := subset_finalCtx_of_shiftsV_zero hndP hsP
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokP
    -- the right child's pass (at `i + 1`)
    obtain ⟨hokQ, hhQ, hfQ⟩ := ihq (i + 1) (j + 1) yq E (finalCtx Γ yp) hq'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_right_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct q + 1 = i + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_right_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct q + 1 = j + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_right_succ_le) (le_refl (1 : V))) hEj),
       hΓ₁⟩ (hDq.mono hsub₁) (hDq'.mono hsub₁)
    obtain ⟨hndQ, hsQ⟩ := passFGraph_noDrop_shifts W (Or.inr rfl) hWp hq _ _ yq hq'
    have hsub₂ : finalCtx Γ yp ⊆ finalCtx (finalCtx Γ yp) yq := subset_finalCtx_of_shiftsV_zero hndQ hsQ
    have hΓ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ hokQ
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    obtain ⟨okS, tagS, ctxS⟩ := cok_shiftAndCert htbl hC hWp hΓ₂ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_off hcqD hEi) (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi)
      (by simp) (E_fvar_off hcqD hEj) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hp hDp))) (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hq hDq)))
      (hsub₂ (hsub₁ handI)) (hsub₂ hfP) hfQ (hsub₂ (hsub₁ handJ))
    refine ⟨listOK_appendV hokP (listOK_appendV hokQ (listOK_single okS)),
      hornOnly_appendV hhP (hornOnly_appendV hhQ (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- or
    intro n p q hp hq ihp ihq i j y E Γ hy hP hDi hDj
    rw [formulaLen_or hp.isUFormula hq.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yp, yq, _, _, hp', hq', rfl⟩ := PassFGraph.or_iff.mp hy
    have hcq : descCountF W n q = descCountF Wd n q := by rw [hWp, hWd]; exact descCountF_certPieces hq
    have hdq : outCount W 2 n q = descCountF Wd n q := by rw [outCount_shift hq, hcq]
    rw [hcq, hdq] at hp' ⊢
    rw [fBinSteps, show fRow (2 : V) 5 = 113 by norm_num [fRow]]
    have hcq_le : descCountF Wd n q + 1 ≤ 2 * formulaLen LAct q := descCountF_walk_le htbl hW hWd hq
    have hcqD : descCountF Wd n q + 1 ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) := le_trans hcq_le two_right_le
    obtain ⟨handI, _, hDq, hDp⟩ := dossF_or htbl hW hWd hp hq hDi
    rw [shift_or hp.isUFormula hq.isUFormula] at hDj
    obtain ⟨handJ, _, hDq', hDp'⟩ := dossF_or htbl hW hWd hp.shift hq.shift hDj
    rw [descCountF_shift Wd hq] at handJ hDp'
    obtain ⟨hokP, hhP, hfP⟩ := ihp (i + descCountF Wd n q + 1) (j + descCountF Wd n q + 1) yp E Γ hp'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_left_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          i + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl i) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEi)),
       le_trans (le_of_eq (show j + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          j + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl j) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEj)),
       hΓ⟩ hDp hDp'
    obtain ⟨hndP, hsP⟩ := passFGraph_noDrop_shifts W (Or.inr rfl) hWp hp _ _ yp hp'
    have hsub₁ : Γ ⊆ finalCtx Γ yp := subset_finalCtx_of_shiftsV_zero hndP hsP
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokP
    obtain ⟨hokQ, hhQ, hfQ⟩ := ihq (i + 1) (j + 1) yq E (finalCtx Γ yp) hq'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_right_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct q + 1 = i + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_right_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct q + 1 = j + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_right_succ_le) (le_refl (1 : V))) hEj),
       hΓ₁⟩ (hDq.mono hsub₁) (hDq'.mono hsub₁)
    obtain ⟨hndQ, hsQ⟩ := passFGraph_noDrop_shifts W (Or.inr rfl) hWp hq _ _ yq hq'
    have hsub₂ : finalCtx Γ yp ⊆ finalCtx (finalCtx Γ yp) yq := subset_finalCtx_of_shiftsV_zero hndQ hsQ
    have hΓ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ hokQ
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    obtain ⟨okS, tagS, ctxS⟩ := cok_shiftOrCert htbl hC hWp hΓ₂ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_off hcqD hEi) (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi)
      (by simp) (E_fvar_off hcqD hEj) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hp hDp))) (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hq hDq)))
      (hsub₂ (hsub₁ handI)) (hsub₂ hfP) hfQ (hsub₂ (hsub₁ handJ))
    refine ⟨listOK_appendV hokP (listOK_appendV hokQ (listOK_single okS)),
      hornOnly_appendV hhP (hornOnly_appendV hhQ (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- all
    intro n p hp ih i j y E Γ hy hP hDi hDj
    rw [formulaLen_all hp.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yb, _, hb, rfl⟩ := PassFGraph.all_iff.mp hy
    rw [fQuantSteps, show fRow (2 : V) 6 = 114 by norm_num [fRow]]
    obtain ⟨hallI, _, hDp⟩ := dossF_all htbl hW hWd hp hDi
    rw [shift_all hp.isUFormula] at hDj
    obtain ⟨hallJ, _, hDp'⟩ := dossF_all htbl hW hWd hp.shift hDj
    obtain ⟨hokB, hhB, hfB⟩ := ih (i + 1) (j + 1) yb E Γ hb
      ⟨le_trans (le_of_eq (show 2 * (n + 1) + 2 * formulaLen LAct p + 8 = 2 * n + 2 * (formulaLen LAct p + 1) + 8 by ring)) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct p + 1 = i + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct p + 1 = j + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_succ_le) (le_refl (1 : V))) hEj),
       hΓ⟩ hDp hDp'
    obtain ⟨hndB, hsB⟩ := passFGraph_noDrop_shifts W (Or.inr rfl) hWp hp _ _ yb hb
    have hsub₁ : Γ ⊆ finalCtx Γ yb := subset_finalCtx_of_shiftsV_zero hndB hsB
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokB
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hpi := dossF_pi htbl hW hWd hp hDp
    rw [cTV_succ] at hpi
    obtain ⟨okS, tagS, ctxS⟩ := cok_shiftAllCert htbl hC hWp hΓ₁ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₁ hpi) (hsub₁ hallI) hfB (hsub₁ hallJ)
    refine ⟨listOK_appendV hokB (listOK_single okS), hornOnly_appendV hhB (hornOnly_single (Or.inl tagS)), ?_⟩
    rw [finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- exs
    intro n p hp ih i j y E Γ hy hP hDi hDj
    rw [formulaLen_exs hp.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yb, _, hb, rfl⟩ := PassFGraph.exs_iff.mp hy
    rw [fQuantSteps, show fRow (2 : V) 7 = 115 by norm_num [fRow]]
    obtain ⟨hallI, _, hDp⟩ := dossF_exs htbl hW hWd hp hDi
    rw [shift_exs hp.isUFormula] at hDj
    obtain ⟨hallJ, _, hDp'⟩ := dossF_exs htbl hW hWd hp.shift hDj
    obtain ⟨hokB, hhB, hfB⟩ := ih (i + 1) (j + 1) yb E Γ hb
      ⟨le_trans (le_of_eq (show 2 * (n + 1) + 2 * formulaLen LAct p + 8 = 2 * n + 2 * (formulaLen LAct p + 1) + 8 by ring)) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct p + 1 = i + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct p + 1 = j + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_succ_le) (le_refl (1 : V))) hEj),
       hΓ⟩ hDp hDp'
    obtain ⟨hndB, hsB⟩ := passFGraph_noDrop_shifts W (Or.inr rfl) hWp hp _ _ yb hb
    have hsub₁ : Γ ⊆ finalCtx Γ yb := subset_finalCtx_of_shiftsV_zero hndB hsB
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokB
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hpi := dossF_pi htbl hW hWd hp hDp
    rw [cTV_succ] at hpi
    obtain ⟨okS, tagS, ctxS⟩ := cok_shiftExsCert htbl hC hWp hΓ₁ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₁ hpi) (hsub₁ hallI) hfB (hsub₁ hallJ)
    refine ⟨listOK_appendV hokB (listOK_single okS), hornOnly_appendV hhB (hornOnly_single (Or.inl tagS)), ?_⟩
    rw [finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'

end formulaShiftOK


/-! ### 4.5 The formula-level NEG pass is applicable and certifies `negFact &j &i`

The same induction as §4.4 with the `neg*Cert` rows; the only structural difference is the atom,
where the image's `nrelFact`/`relFact` names the image's OWN vector: the identification pass
(§4.3, at `ν = 1`) certifies `eqFactB ⟨v⟩ᵢ ⟨v⟩ⱼ`, `eqRefl [&j]` and `congNRel/congRel` move the
image's fact onto the source vector, and only then `negRelCert/negNRelCert` fires.
-/

section formulaNegOK

set_option maxHeartbeats 4000000 in
/-- **The neg pass of a formula is applicable and certifies `negFact &j &i`.** -/
theorem passFGraph_neg_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V}
    (hWd : Wd = walkPieces) (hWp : W = certPieces) :
    ∀ {n r : V}, IsSemiformula LAct n r → ∀ i j y E Γ : V, PassFGraph W 1 n r i j y →
      PassPre (2 * formulaLen LAct r) n i j E Γ → DossF Wd Γ n r i → DossF Wd Γ n (neg LAct r) j →
      PassPost tbl E Γ y (negFact (^&j) (^&i)) := by
  have hW : WalkTable tbl := hC.walkTable
  have h12 : (1 : V) ≠ 2 := by norm_num
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i j y E Γ : V, PassFGraph W 1 n r i j y →
      PassPre (2 * formulaLen LAct r) n i j E Γ → DossF Wd Γ n r i → DossF Wd Γ n (neg LAct r) j →
      PassPost tbl E Γ y (negFact (^&j) (^&i)))
  · definability
  · -- rel: identify the two vectors, move the image's `nrelFact` onto the source vector, then `negRelCert`
    intro n k R v hkR hv i j y E Γ hy hP hDi hDj
    rw [formulaLen_rel hkR hv.isUTerm] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.rel_iff.mp hy, fAtomSteps, if_pos rfl, show congRow (0 : V) = 137 by norm_num [congRow],
      show fRow (1 : V) 0 = 100 by norm_num [fRow]]
    have h8 : (8 : V) ≤ E := E_eight hE
    have hD1 : (1 : V) ≤ 2 * (listSum (termLenVec LAct k v) + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hSig : 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * (listSum (termLenVec LAct k v) + 1) := by
      rw [mul_add, mul_one]; exact add_le_add (le_refl _) (by norm_num)
    obtain ⟨hrI, _, huI, hDvI⟩ := dossF_rel htbl hW hWd hkR hv hDi
    rw [neg_rel hkR hv.isUTerm] at hDj
    obtain ⟨hrJ, _, _, hDvJ⟩ := dossF_nrel htbl hW hWd hkR hv hDj
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hV := passVGraph_eq_ok htbl hC hWd hWp h12 n (rel_arity_le_two hkR) hv (le_refl k) (i + 1) (j + 1) _ E Γ
      (passV_graph hv (le_refl k))
    rw [htl] at hV
    obtain ⟨hokV, hhV, hfV⟩ := hV
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEi,
       le_trans (le_of_eq (show j + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = j + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEj,
       hΓ⟩ hDvI hDvJ
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts (ν := 1) hWp hv k le_rfl (i + 1) (j + 1) _ (passV_graph hv (le_refl k))
    have hsub₁ : Γ ⊆ finalCtx Γ (passV W 1 n k v k (i + 1) (j + 1)) := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokV
    have er : mkStep W (relRow R) 0 = mkStep walkPieces (relRow R) 0 := by rw [hWp, mkStep_certPieces_relRow]
    obtain ⟨okR, tagR, ctxR, hEk, hER⟩ := relConst_ok htbl hW rfl hkR h8 hΓ₁
    rw [← er] at okR tagR ctxR
    have hΓ₂ := isFormulaSet_ctxAfter 8 htbl okR
    obtain ⟨okE, tagE, ctxE⟩ := cok_eqRefl htbl hC hWp hΓ₂ (wx := ^&j) (by simp) (E_fvar hEj)
    have hΓ₃ := isFormulaSet_ctxAfter 8 htbl okE
    obtain ⟨okC, tagC, ctxC⟩ := cok_congNRel htbl hC hWp hΓ₃ (by simp) (E_fvar hEj) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEj) (by simp) (E_fvar hEj)
      (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi)
      (by rw [ctxE]; exact mem_insert_self')
      (by rw [ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' hfV))
      (by rw [ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' (hsub₁ hrJ)))
    have hΓ₄ := isFormulaSet_ctxAfter 8 htbl okC
    obtain ⟨okS, tagS, ctxS⟩ := cok_negRelCert htbl hC hWp hΓ₄ (by simp) (E_fvar hEi) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi) (by simp) (E_fvar hEj)
      (by rw [ctxC, ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' mem_insert_self'))
      (by rw [ctxC, ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (hsub₁ huI))))
      (by rw [ctxC, ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (hsub₁ hrI))))
      (by rw [ctxC]; exact mem_insert_self')
    refine ⟨listOK_appendV hokV (listOK_cons okR (listOK_cons okE (listOK_cons okC (listOK_single okS)))),
      hornOnly_appendV hhV (hornOnly_cons (Or.inl tagR) (hornOnly_cons (Or.inl tagE)
        (hornOnly_cons (Or.inl tagC) (hornOnly_single (Or.inl tagS))))), ?_⟩
    rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- nrel
    intro n k R v hkR hv i j y E Γ hy hP hDi hDj
    rw [formulaLen_nrel hkR hv.isUTerm] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.nrel_iff.mp hy, fAtomSteps, if_pos rfl, show congRow (1 : V) = 136 by norm_num [congRow],
      show fRow (1 : V) 1 = 101 by norm_num [fRow]]
    have h8 : (8 : V) ≤ E := E_eight hE
    have hD1 : (1 : V) ≤ 2 * (listSum (termLenVec LAct k v) + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hSig : 2 * listSum (termLenVec LAct k v) + 1 ≤ 2 * (listSum (termLenVec LAct k v) + 1) := by
      rw [mul_add, mul_one]; exact add_le_add (le_refl _) (by norm_num)
    obtain ⟨hrI, _, huI, hDvI⟩ := dossF_nrel htbl hW hWd hkR hv hDi
    rw [neg_nrel hkR hv.isUTerm] at hDj
    obtain ⟨hrJ, _, _, hDvJ⟩ := dossF_rel htbl hW hWd hkR hv hDj
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hV := passVGraph_eq_ok htbl hC hWd hWp h12 n (rel_arity_le_two hkR) hv (le_refl k) (i + 1) (j + 1) _ E Γ
      (passV_graph hv (le_refl k))
    rw [htl] at hV
    obtain ⟨hokV, hhV, hfV⟩ := hV
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) hSig) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = i + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEi,
       le_trans (le_of_eq (show j + 1 + (2 * listSum (termLenVec LAct k v) + 1) + 1 = j + 2 * (listSum (termLenVec LAct k v) + 1) + 1 by ring)) hEj,
       hΓ⟩ hDvI hDvJ
    obtain ⟨hndV, hsV⟩ := passVGraph_noDrop_shifts (ν := 1) hWp hv k le_rfl (i + 1) (j + 1) _ (passV_graph hv (le_refl k))
    have hsub₁ : Γ ⊆ finalCtx Γ (passV W 1 n k v k (i + 1) (j + 1)) := subset_finalCtx_of_shiftsV_zero hndV hsV
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokV
    have er : mkStep W (relRow R) 0 = mkStep walkPieces (relRow R) 0 := by rw [hWp, mkStep_certPieces_relRow]
    obtain ⟨okR, tagR, ctxR, hEk, hER⟩ := relConst_ok htbl hW rfl hkR h8 hΓ₁
    rw [← er] at okR tagR ctxR
    have hΓ₂ := isFormulaSet_ctxAfter 8 htbl okR
    obtain ⟨okE, tagE, ctxE⟩ := cok_eqRefl htbl hC hWp hΓ₂ (wx := ^&j) (by simp) (E_fvar hEj)
    have hΓ₃ := isFormulaSet_ctxAfter 8 htbl okE
    obtain ⟨okC, tagC, ctxC⟩ := cok_congRel htbl hC hWp hΓ₃ (by simp) (E_fvar hEj) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEj) (by simp) (E_fvar hEj)
      (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi)
      (by rw [ctxE]; exact mem_insert_self')
      (by rw [ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' hfV))
      (by rw [ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' (hsub₁ hrJ)))
    have hΓ₄ := isFormulaSet_ctxAfter 8 htbl okC
    obtain ⟨okS, tagS, ctxS⟩ := cok_negNRelCert htbl hC hWp hΓ₄ (by simp) (E_fvar hEi) (cTV_semiterm_LAct 0 _) hEk
      (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) (E_vRef_succ hD1 hEi) (by simp) (E_fvar hEj)
      (by rw [ctxC, ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' mem_insert_self'))
      (by rw [ctxC, ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (hsub₁ huI))))
      (by rw [ctxC, ctxE, ctxR]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (hsub₁ hrI))))
      (by rw [ctxC]; exact mem_insert_self')
    refine ⟨listOK_appendV hokV (listOK_cons okR (listOK_cons okE (listOK_cons okC (listOK_single okS)))),
      hornOnly_appendV hhV (hornOnly_cons (Or.inl tagR) (hornOnly_cons (Or.inl tagE)
        (hornOnly_cons (Or.inl tagC) (hornOnly_single (Or.inl tagS))))), ?_⟩
    rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- verum
    intro n i j y E Γ hy hP hDi hDj
    rw [formulaLen_verum] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.verum_iff.mp hy, fConstSteps, show fRow (1 : V) 2 = 102 by norm_num [fRow]]
    rw [neg_verum] at hDj
    obtain ⟨hvI, _⟩ := dossF_verum htbl hW hWd hDi
    obtain ⟨hvJ, _⟩ := dossF_falsum htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_negVerumCert htbl hC hWp hΓ (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hvI hvJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · -- falsum
    intro n i j y E Γ hy hP hDi hDj
    rw [formulaLen_falsum] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    rw [PassFGraph.falsum_iff.mp hy, fConstSteps, show fRow (1 : V) 3 = 103 by norm_num [fRow]]
    rw [neg_falsum] at hDj
    obtain ⟨hvI, _⟩ := dossF_falsum htbl hW hWd hDi
    obtain ⟨hvJ, _⟩ := dossF_verum htbl hW hWd hDj
    obtain ⟨hok, htag, hctx⟩ := cok_negFalsumCert htbl hC hWp hΓ (by simp) (E_fvar hEi) (by simp) (E_fvar hEj) hvI hvJ
    refine ⟨listOK_single hok, hornOnly_single (Or.inl htag), ?_⟩
    rw [finalCtx_single, hctx]; exact mem_insert_self'
  · -- and
    intro n p q hp hq ihp ihq i j y E Γ hy hP hDi hDj
    rw [formulaLen_and hp.isUFormula hq.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yp, yq, _, _, hp', hq', rfl⟩ := PassFGraph.and_iff.mp hy
    have hcq : descCountF W n q = descCountF Wd n q := by rw [hWp, hWd]; exact descCountF_certPieces hq
    have hdq : outCount W 1 n q = descCountF Wd n q := by rw [outCount_neg hq, hcq]
    rw [hcq, hdq] at hp' ⊢
    rw [fBinSteps, show fRow (1 : V) 4 = 104 by norm_num [fRow]]
    have hcq_le : descCountF Wd n q + 1 ≤ 2 * formulaLen LAct q := descCountF_walk_le htbl hW hWd hq
    have hcqD : descCountF Wd n q + 1 ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) := le_trans hcq_le two_right_le
    obtain ⟨handI, _, hDq, hDp⟩ := dossF_and htbl hW hWd hp hq hDi
    rw [neg_and hp.isUFormula hq.isUFormula] at hDj
    obtain ⟨handJ, _, hDq', hDp'⟩ := dossF_or htbl hW hWd hp.neg hq.neg hDj
    rw [descCountF_neg Wd hq] at handJ hDp'
    -- the left child's pass (at `i + cq + 1`)
    obtain ⟨hokP, hhP, hfP⟩ := ihp (i + descCountF Wd n q + 1) (j + descCountF Wd n q + 1) yp E Γ hp'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_left_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          i + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl i) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEi)),
       le_trans (le_of_eq (show j + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          j + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl j) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEj)),
       hΓ⟩ hDp hDp'
    obtain ⟨hndP, hsP⟩ := passFGraph_noDrop_shifts W (Or.inl rfl) hWp hp _ _ yp hp'
    have hsub₁ : Γ ⊆ finalCtx Γ yp := subset_finalCtx_of_shiftsV_zero hndP hsP
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokP
    -- the right child's pass (at `i + 1`)
    obtain ⟨hokQ, hhQ, hfQ⟩ := ihq (i + 1) (j + 1) yq E (finalCtx Γ yp) hq'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_right_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct q + 1 = i + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_right_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct q + 1 = j + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_right_succ_le) (le_refl (1 : V))) hEj),
       hΓ₁⟩ (hDq.mono hsub₁) (hDq'.mono hsub₁)
    obtain ⟨hndQ, hsQ⟩ := passFGraph_noDrop_shifts W (Or.inl rfl) hWp hq _ _ yq hq'
    have hsub₂ : finalCtx Γ yp ⊆ finalCtx (finalCtx Γ yp) yq := subset_finalCtx_of_shiftsV_zero hndQ hsQ
    have hΓ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ hokQ
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    obtain ⟨okS, tagS, ctxS⟩ := cok_negAndCert htbl hC hWp hΓ₂ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_off hcqD hEi) (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi)
      (by simp) (E_fvar_off hcqD hEj) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hp hDp))) (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hq hDq)))
      (hsub₂ (hsub₁ handI)) (hsub₂ hfP) hfQ (hsub₂ (hsub₁ handJ))
    refine ⟨listOK_appendV hokP (listOK_appendV hokQ (listOK_single okS)),
      hornOnly_appendV hhP (hornOnly_appendV hhQ (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- or
    intro n p q hp hq ihp ihq i j y E Γ hy hP hDi hDj
    rw [formulaLen_or hp.isUFormula hq.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yp, yq, _, _, hp', hq', rfl⟩ := PassFGraph.or_iff.mp hy
    have hcq : descCountF W n q = descCountF Wd n q := by rw [hWp, hWd]; exact descCountF_certPieces hq
    have hdq : outCount W 1 n q = descCountF Wd n q := by rw [outCount_neg hq, hcq]
    rw [hcq, hdq] at hp' ⊢
    rw [fBinSteps, show fRow (1 : V) 5 = 105 by norm_num [fRow]]
    have hcq_le : descCountF Wd n q + 1 ≤ 2 * formulaLen LAct q := descCountF_walk_le htbl hW hWd hq
    have hcqD : descCountF Wd n q + 1 ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) := le_trans hcq_le two_right_le
    obtain ⟨handI, _, hDq, hDp⟩ := dossF_or htbl hW hWd hp hq hDi
    rw [neg_or hp.isUFormula hq.isUFormula] at hDj
    obtain ⟨handJ, _, hDq', hDp'⟩ := dossF_and htbl hW hWd hp.neg hq.neg hDj
    rw [descCountF_neg Wd hq] at handJ hDp'
    obtain ⟨hokP, hhP, hfP⟩ := ihp (i + descCountF Wd n q + 1) (j + descCountF Wd n q + 1) yp E Γ hp'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_left_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          i + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl i) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEi)),
       le_trans (le_of_eq (show j + descCountF Wd n q + 1 + 2 * formulaLen LAct p + 1 =
          j + (descCountF Wd n q + 1 + 2 * formulaLen LAct p) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) (add_le_add hcq_le (le_refl (2 * formulaLen LAct p)))) (le_refl (1 : V)))
          (le_trans (add_le_add (add_le_add (le_refl j) (le_trans (le_of_eq (show 2 * formulaLen LAct q + 2 * formulaLen LAct p =
              2 * (formulaLen LAct p + formulaLen LAct q) by ring)) (mul_le_mul_of_nonneg_left le_self_add zero_le))) (le_refl (1 : V))) hEj)),
       hΓ⟩ hDp hDp'
    obtain ⟨hndP, hsP⟩ := passFGraph_noDrop_shifts W (Or.inl rfl) hWp hp _ _ yp hp'
    have hsub₁ : Γ ⊆ finalCtx Γ yp := subset_finalCtx_of_shiftsV_zero hndP hsP
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokP
    obtain ⟨hokQ, hhQ, hfQ⟩ := ihq (i + 1) (j + 1) yq E (finalCtx Γ yp) hq'
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) two_right_le) (le_refl (8 : V))) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct q + 1 = i + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_right_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct q + 1 = j + (2 * formulaLen LAct q + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_right_succ_le) (le_refl (1 : V))) hEj),
       hΓ₁⟩ (hDq.mono hsub₁) (hDq'.mono hsub₁)
    obtain ⟨hndQ, hsQ⟩ := passFGraph_noDrop_shifts W (Or.inl rfl) hWp hq _ _ yq hq'
    have hsub₂ : finalCtx Γ yp ⊆ finalCtx (finalCtx Γ yp) yq := subset_finalCtx_of_shiftsV_zero hndQ hsQ
    have hΓ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ hokQ
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    obtain ⟨okS, tagS, ctxS⟩ := cok_negOrCert htbl hC hWp hΓ₂ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_off hcqD hEi) (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi)
      (by simp) (E_fvar_off hcqD hEj) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hp hDp))) (hsub₂ (hsub₁ (dossF_pi htbl hW hWd hq hDq)))
      (hsub₂ (hsub₁ handI)) (hsub₂ hfP) hfQ (hsub₂ (hsub₁ handJ))
    refine ⟨listOK_appendV hokP (listOK_appendV hokQ (listOK_single okS)),
      hornOnly_appendV hhP (hornOnly_appendV hhQ (hornOnly_single (Or.inl tagS))), ?_⟩
    rw [finalCtx_appendV, finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- all
    intro n p hp ih i j y E Γ hy hP hDi hDj
    rw [formulaLen_all hp.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yb, _, hb, rfl⟩ := PassFGraph.all_iff.mp hy
    rw [fQuantSteps, show fRow (1 : V) 6 = 106 by norm_num [fRow]]
    obtain ⟨hallI, _, hDp⟩ := dossF_all htbl hW hWd hp hDi
    rw [neg_all hp.isUFormula] at hDj
    obtain ⟨hallJ, _, hDp'⟩ := dossF_exs htbl hW hWd hp.neg hDj
    obtain ⟨hokB, hhB, hfB⟩ := ih (i + 1) (j + 1) yb E Γ hb
      ⟨le_trans (le_of_eq (show 2 * (n + 1) + 2 * formulaLen LAct p + 8 = 2 * n + 2 * (formulaLen LAct p + 1) + 8 by ring)) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct p + 1 = i + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct p + 1 = j + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_succ_le) (le_refl (1 : V))) hEj),
       hΓ⟩ hDp hDp'
    obtain ⟨hndB, hsB⟩ := passFGraph_noDrop_shifts W (Or.inl rfl) hWp hp _ _ yb hb
    have hsub₁ : Γ ⊆ finalCtx Γ yb := subset_finalCtx_of_shiftsV_zero hndB hsB
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokB
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hpi := dossF_pi htbl hW hWd hp hDp
    rw [cTV_succ] at hpi
    obtain ⟨okS, tagS, ctxS⟩ := cok_negAllCert htbl hC hWp hΓ₁ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₁ hpi) (hsub₁ hallI) hfB (hsub₁ hallJ)
    refine ⟨listOK_appendV hokB (listOK_single okS), hornOnly_appendV hhB (hornOnly_single (Or.inl tagS)), ?_⟩
    rw [finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'
  · -- exs
    intro n p hp ih i j y E Γ hy hP hDi hDj
    rw [formulaLen_exs hp.isUFormula] at hP
    obtain ⟨hE, hEi, hEj, hΓ⟩ := hP
    obtain ⟨yb, _, hb, rfl⟩ := PassFGraph.exs_iff.mp hy
    rw [fQuantSteps, show fRow (1 : V) 7 = 107 by norm_num [fRow]]
    obtain ⟨hallI, _, hDp⟩ := dossF_exs htbl hW hWd hp hDi
    rw [neg_ex hp.isUFormula] at hDj
    obtain ⟨hallJ, _, hDp'⟩ := dossF_all htbl hW hWd hp.neg hDj
    obtain ⟨hokB, hhB, hfB⟩ := ih (i + 1) (j + 1) yb E Γ hb
      ⟨le_trans (le_of_eq (show 2 * (n + 1) + 2 * formulaLen LAct p + 8 = 2 * n + 2 * (formulaLen LAct p + 1) + 8 by ring)) hE,
       le_trans (le_of_eq (show i + 1 + 2 * formulaLen LAct p + 1 = i + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl i) two_succ_le) (le_refl (1 : V))) hEi),
       le_trans (le_of_eq (show j + 1 + 2 * formulaLen LAct p + 1 = j + (2 * formulaLen LAct p + 1) + 1 by ring))
        (le_trans (add_le_add (add_le_add (le_refl j) two_succ_le) (le_refl (1 : V))) hEj),
       hΓ⟩ hDp hDp'
    obtain ⟨hndB, hsB⟩ := passFGraph_noDrop_shifts W (Or.inl rfl) hWp hp _ _ yb hb
    have hsub₁ : Γ ⊆ finalCtx Γ yb := subset_finalCtx_of_shiftsV_zero hndB hsB
    have hΓ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokB
    have hD1 : (1 : V) ≤ 2 * (formulaLen LAct p + 1) :=
      le_trans (by norm_num : (1 : V) ≤ 2 * 1) (mul_le_mul_of_nonneg_left le_add_self zero_le)
    have hpi := dossF_pi htbl hW hWd hp hDp
    rw [cTV_succ] at hpi
    obtain ⟨okS, tagS, ctxS⟩ := cok_negExsCert htbl hC hWp hΓ₁ (cTV_semiterm_LAct 0 _) (E_cT_n hE)
      (by simp) (E_fvar_succ hD1 hEi) (by simp) (E_fvar hEi) (by simp) (E_fvar_succ hD1 hEj) (by simp) (E_fvar hEj)
      (hsub₁ hpi) (hsub₁ hallI) hfB (hsub₁ hallJ)
    refine ⟨listOK_appendV hokB (listOK_single okS), hornOnly_appendV hhB (hornOnly_single (Or.inl tagS)), ?_⟩
    rw [finalCtx_appendV, finalCtx_single, ctxS]
    exact mem_insert_self'

end formulaNegOK

/-! ### 4.6 The named producers: `certShift_ok`, `certNeg_ok`, and their costs (§3.6)

With `r`'s walk dossier at offset `i` and the image's (`shift r` / `neg r`, freshly walked) at
offset `j`, in a formula-set context whose cap `E` bounds the arity part and both offsets, the pass
is applicable at cap `8`, drops nothing, is Horn-only, introduces no eigenvariable, and leaves the
root pair `shiftFact &j &i` / `negFact &j &i` in its final context; its cost is the walk's polynomial
(`costSum_describeF_le`'s shape) at `12|r|` steps.
-/

section certMain

theorem certShift_ok {tbl N Wd W n r i j E Γ : V} (htbl : TableOK tbl N) (hC : CertTable tbl)
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) (hEi : i + 2 * formulaLen LAct r + 1 ≤ E)
    (hEj : j + 2 * formulaLen LAct r + 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hDi : DossF Wd Γ n r i) (hDj : DossF Wd Γ n (shift LAct r) j) :
    ListOK tbl E ((8 : ℕ) : V) Γ (certShift W n r i j) ∧ NoDrop (certShift W n r i j) ∧
    HornOnly (certShift W n r i j) ∧ shiftsV (certShift W n r i j) = 0 ∧
    neg LAct (shiftFact (^&j) (^&i)) ∈ finalCtx Γ (certShift W n r i j) := by
  obtain ⟨hok, hh, hf⟩ := passFGraph_shift_ok htbl hC hWd hWp hr i j _ E Γ (certShift_graph hr) ⟨hE, hEi, hEj, hΓ⟩ hDi hDj
  obtain ⟨hnd, hs⟩ := certShift_noDrop_shifts hWp hr
  exact ⟨hok, hnd, hh, hs, hf⟩

theorem certNeg_ok {tbl N Wd W n r i j E Γ : V} (htbl : TableOK tbl N) (hC : CertTable tbl)
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) (hEi : i + 2 * formulaLen LAct r + 1 ≤ E)
    (hEj : j + 2 * formulaLen LAct r + 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hDi : DossF Wd Γ n r i) (hDj : DossF Wd Γ n (neg LAct r) j) :
    ListOK tbl E ((8 : ℕ) : V) Γ (certNeg W n r i j) ∧ NoDrop (certNeg W n r i j) ∧
    HornOnly (certNeg W n r i j) ∧ shiftsV (certNeg W n r i j) = 0 ∧
    neg LAct (negFact (^&j) (^&i)) ∈ finalCtx Γ (certNeg W n r i j) := by
  obtain ⟨hok, hh, hf⟩ := passFGraph_neg_ok htbl hC hWd hWp hr i j _ E Γ (certNeg_graph hr) ⟨hE, hEi, hEj, hΓ⟩ hDi hDj
  obtain ⟨hnd, hs⟩ := certNeg_noDrop_shifts hWp hr
  exact ⟨hok, hnd, hh, hs, hf⟩

/-- **The cost of the shift pass**: the walk's polynomial at `12|r|` steps. -/
theorem costSum_certShift_le {tbl N E B Wd W n r i j Γ : V} (htbl : TableOK tbl N) (hC : CertTable tbl)
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (hB : ∀ a < len tbl, formulaLen LAct (rowB tbl.[a]) ≤ B)
    (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) (hEi : i + 2 * formulaLen LAct r + 1 ≤ E)
    (hEj : j + 2 * formulaLen LAct r + 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hDi : DossF Wd Γ n r i) (hDj : DossF Wd Γ n (shift LAct r) j) :
    costSum N E Γ (certShift W n r i j) ≤
      12 * formulaLen LAct r * (stepK N E B + 36 * ctxBound E B Γ (12 * formulaLen LAct r)) := by
  have hE1 : 1 ≤ E := le_trans (le_trans (by norm_num) (le_add_self : 8 ≤ 2 * n + 2 * formulaLen LAct r + 8)) hE
  obtain ⟨hok, _, ht, _, _⟩ := certShift_ok htbl hC hWd hWp hr hE hEi hEj hΓ hDi hDj
  have hlen : len (certShift W n r i j) ≤ 12 * formulaLen LAct r := le_trans le_self_add (len_certShift_le hr)
  have hB' : ∀ a < len (certShift W n r i j), formulaLen LAct (rowB tbl.[sRow (certShift W n r i j).[a]]) ≤ B :=
    fun a ha ↦ hB _ (sRow_lt_of_stepOK (hok a ha) (ht a ha))
  refine le_trans (costSum_le_of_hornOnly hE1 htbl hok ht hB') ?_
  unfold ctxBound
  gcongr

/-- **The cost of the neg pass**: the walk's polynomial at `12|r|` steps. -/
theorem costSum_certNeg_le {tbl N E B Wd W n r i j Γ : V} (htbl : TableOK tbl N) (hC : CertTable tbl)
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (hB : ∀ a < len tbl, formulaLen LAct (rowB tbl.[a]) ≤ B)
    (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) (hEi : i + 2 * formulaLen LAct r + 1 ≤ E)
    (hEj : j + 2 * formulaLen LAct r + 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hDi : DossF Wd Γ n r i) (hDj : DossF Wd Γ n (neg LAct r) j) :
    costSum N E Γ (certNeg W n r i j) ≤
      12 * formulaLen LAct r * (stepK N E B + 36 * ctxBound E B Γ (12 * formulaLen LAct r)) := by
  have hE1 : 1 ≤ E := le_trans (le_trans (by norm_num) (le_add_self : 8 ≤ 2 * n + 2 * formulaLen LAct r + 8)) hE
  obtain ⟨hok, _, ht, _, _⟩ := certNeg_ok htbl hC hWd hWp hr hE hEi hEj hΓ hDi hDj
  have hlen : len (certNeg W n r i j) ≤ 12 * formulaLen LAct r := le_trans le_self_add (len_certNeg_le hr)
  have hB' : ∀ a < len (certNeg W n r i j), formulaLen LAct (rowB tbl.[sRow (certNeg W n r i j).[a]]) ≤ B :=
    fun a ha ↦ hB _ (sRow_lt_of_stepOK (hok a ha) (ht a ha))
  refine le_trans (costSum_le_of_hornOnly hE1 htbl hok ht hB') ?_
  unfold ctxBound
  gcongr

end certMain


/-! ### 4.7 Status of the remaining §3.6 producers (2026-09-14, recorded here so the next session starts from facts)

**`certSubst w` / `certFree` — NOT started; three obstacles, in order of size.**
1. The `PassT`/`PassF` template has no slot for the substitution vector, and the image's offsets do
   NOT advance in lock-step with the source's: the image of a leaf `#z` is `w.[z]` walked afresh
   (count `descCountT (w.[z])`, not `1`), so the third family cannot be a `ν` value of the existing
   fixpoints — it is a sibling fixpoint with parameters `(W, wv, wt)` (the vector CODE and the TERM
   naming it), whose image offset increments by `descCountT (termSubst wv t)` per node (the analogue
   of `outCount`). Everything from `blueprint` to the `_ok` proofs (~1500 lines) is new.
2. The bvar leaf: `termSubstBvarCert “e w z t. qqBvarDef t z → nthDef e w z → termSubstGraph e w t”`
   needs `nthFact e &w (cT z)` for the IMAGE's node `e`, but the image walks `w.[z]` afresh at some
   `&j'`, while `nthAdjoinZero/Succ` deliver `nthFact` only for the ORIGINAL entries of `w`
   (`&it` with `adjFact &w &it 𝟎`). No `congNth` row exists. The way out without a new row: apply
   `termSubstBvarCert` at `e := &it` (the original entry), identify `&it` with `&j'` by the
   identification pass (§4.3), and repair the parent vector's `adjFact &u' &j' &u` into
   `adjFact &u' &it &u` with `congAdj` (`Lib/Frag.lean:290`, a LAYOUT row — it is not in
   `certRows`; append it, and `eqSymm`, to `gen_cert.py`'s `TABLE`, index-stable) — every term
   occurs inside a vector, so the parent is always an adjoin.
3. Under a quantifier the vector becomes `qVec w = #0 ∷ termBShiftVec w`, which the rows need as an
   OBJECT (`qVecCert “u sw z w k. utvPi k w → termBShiftVecGraph sw k w → qqBvarDef z 0 →
   adjoinDef u z sw → qVecGraph u w”`): the pass must CONSTRUCT `sw`, `z`, `u` by totality steps
   (`adjoinTotal`, `qqBvarTotal`, `qqFuncTotal` for the shifted entries) — tag-2 steps, so the
   substitution pass is NOT shift-free and its offsets move with `shiftsV` (the `dossF_transport`
   discipline, not the fixed layout of §4.2–4.5). `exsIntro`'s `substs1 t p` needs this whenever `p`
   has inner quantifiers.

**`lenSteps` — NOT started; one missing row.** The bottom-up plan (§3.6 "lengths") is sound:
`formulaLenTotal [&i]` (`cok_formulaLenTotal`, tag 2 — one eigenvariable per node, offsets move),
the `formulaLen*` rows at NUMERAL child witnesses (`lenFact (bnum|p|) &p` from the children) giving
`eqFactB &0 (bnum|p| ^+ bnum|q| ^+ 𝟏)`, then the closed numeral fact, `eqTrans`, `congLenNum`.
The closed fact `bnum|p| ^+ bnum|q| ^+ 𝟏 = bnum (|p| + |q| + 1)` is NOT among `NumSteps`' lemma
facts (`addFact`, `succFact` are, `bin2Fact` is the `≤` version) and cannot be assembled from them
in context: the successor congruence `“y x. x = y → x + 1 = y + 1”` exists NOWHERE in the row
library (checked `Lib/*.lean`, `NumSteps`). Either add that row (`Lib/Frag` + `RowInstB`, then
`gen_cert.py`'s `TABLE`) or add an `addSuccFact a b : eqFact (bnum a ^+ bnum b ^+ 𝟏) (bnum (a + b + 1))`
lemma code to `NumSteps` (a cut of `addFact` and `succFact` through that same congruence — so the
row is needed either way). With the `≤` facts only, `leOfEqLe` yields `&0 ≤ bnum|r|`, an inexact
length no consumer row reads (`congLenNum` needs `=`). State `lenSteps_ok` with `NoDrop'`.
-/

/-! ## Part 5 — `lenSteps`: the exact-length producer (§3.6 "lengths")

Bottom-up over a dossier. The walk leaves NO length fact, so every node first INTRODUCES its length
object (`formulaLenTotal`/`termLenTotal`, tag 2 — one eigenvariable per node, the offsets move with
`shiftsV`), reads the exact equation off the table's `formulaLen*`/`termLen*` row at the children's
NUMERAL lengths, closes the arithmetic by `NumSteps`' `sLemma` facts (`addFact`, `succFact`, `cTEqFact`)
with the new `congSucc` row (cIdx 184) and `eqTrans`, and moves the numeral into the graph position
by `congLenNum`/`congTLenNum`. Atoms go through the vector: the length VECTOR is built by
`adjoinTotal` (walk row 17) + `termLenVecAdj`, the sum by the new intro row `listSumAdjI` (cIdx 185)
at numeral sums, then `formulaLenRelCert`/`termLenFuncCert`. NOT shift-free: `shiftsV + 1 ≤ 2|r|`.
-/

/-! ### 5.0 Preliminaries: numerals are shift-invariant; `NoDrop'` transport of dossiers -/

section lenPrelim

lemma termShiftIterV_bnum (z : V) : ∀ k : V, termShiftIterV (bnum z) k = bnum z := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp [termShiftIterV_zero]
  | succ k ih => rw [termShiftIterV_succ, ih, termShift_bnum]

/-- A dossier survives a cut-admitting list too, moved up by its eigenvariable count. -/
lemma dossF_transport' {W Γ n r i S : V} (hS : NoDrop' S) (h : DossF W Γ n r i) :
    DossF W (finalCtx Γ S) n r (i + shiftsV S) := by
  intro f hf
  rw [shiftIterV_add]
  exact mem_finalCtx_of_mem' hS (h f hf)
lemma dossT_transport' {W Γ n t i S : V} (hS : NoDrop' S) (h : DossT W Γ n t i) :
    DossT W (finalCtx Γ S) n t (i + shiftsV S) := by
  intro f hf
  rw [shiftIterV_add]
  exact mem_finalCtx_of_mem' hS (h f hf)
lemma dossV_transport' {W Γ n k v j i S : V} (hS : NoDrop' S) (h : DossV W Γ n k v j i) :
    DossV W (finalCtx Γ S) n k v j (i + shiftsV S) := by
  intro f hf
  rw [shiftIterV_add]
  exact mem_finalCtx_of_mem' hS (h f hf)

end lenPrelim

/-! ### 5.1 The step-list builders (one per node shape), each a Σ₁ function -/

section lenBuilders

/-- A constant node (`verum` at row `147`, `falsum` at `148`): introduce the length, read `l = 1`, move the
numeral `bnum 1` onto the node. -/
noncomputable def lnConstSteps (W c i : V) : V :=
  ?[mkStep W 155 ?[^&i], mkStep W c ?[^&(i + 1), ^&0], mkStep W 145 ?[^&(i + 1), ^&0, bnum 1]]

noncomputable def lnConstStepsDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y W c i. ∃ fi, !qqFvarDef fi i ∧ ∃ fi', !qqFvarDef fi' (i + 1) ∧ ∃ f0, !qqFvarDef f0 0 ∧ ∃ b1, !bnumGraph b1 1 ∧
    ∃ e₁, !mkVec₁Def e₁ fi ∧ ∃ s₁, !mkStepDef s₁ W 155 e₁ ∧
    ∃ e₂, !mkVec₂Def e₂ fi' f0 ∧ ∃ s₂, !mkStepDef s₂ W c e₂ ∧
    ∃ e₃₀, !mkVec₂Def e₃₀ f0 b1 ∧ ∃ e₃, !adjoinDef e₃ fi' e₃₀ ∧ ∃ s₃, !mkStepDef s₃ W 145 e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ !adjoinDef y s₁ l₂”

instance lnConstSteps_defined : 𝚺₁-Function₃ (lnConstSteps : V → V → V → V) via lnConstStepsDef := .mk
  fun v ↦ by simp [lnConstStepsDef, lnConstSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff]
instance lnConstSteps_definable : 𝚺₁-Function₃ (lnConstSteps : V → V → V → V) := lnConstSteps_defined.to_definable

/-- A binary node (`and` at row `149`, `or` at `150`) after the RIGHT child's list `yq` (offset `i + 1`,
shifts `sq`) and the LEFT child's `yp` (offset `i + cq + 1 + sq`, shifts `sp`), `S = sq + sp`: introduce the
length at `&(i + S)`, read `l = bnum lp + bnum lq + 1`, close by `addFact lp lq`, `congSucc`,
`succFact (lp + lq)` and two `eqTrans`, then `congLenNum`. -/
noncomputable def lnBinSteps (W T c n cq lp lq i sq sp yq yp : V) : V :=
  appendV yq (appendV yp
    ?[mkStep W 155 ?[^&(i + (sq + sp))],
      mkStep W c ?[cTV n, ^&(i + cq + 1 + (sq + sp) + 1), ^&(i + 1 + (sq + sp) + 1), ^&(i + (sq + sp) + 1), bnum lp, bnum lq, ^&0],
      sLemma (addFact lp lq) (addCode T lp lq),
      mkStep W 184 ?[bnum lp ^+ bnum lq, bnum (lp + lq)],
      sLemma (succFact (lp + lq)) (succCode T (lp + lq)),
      mkStep W 123 ?[^&0, bnum lp ^+ bnum lq ^+ (𝟏 : V), bnum (lp + lq) ^+ (𝟏 : V)],
      mkStep W 123 ?[^&0, bnum (lp + lq) ^+ (𝟏 : V), bnum (lp + lq + 1)],
      mkStep W 145 ?[^&(i + (sq + sp) + 1), ^&0, bnum (lp + lq + 1)]])

noncomputable def lnBinStepsDef : 𝚺₁.Semisentence 13 := .mkSigma
  “y W T c n cq lp lq i sq sp yq yp. ∃ S, S = sq + sp ∧
    ∃ fS, !qqFvarDef fS (i + S) ∧ ∃ fp, !qqFvarDef fp (i + cq + 1 + S + 1) ∧ ∃ fq, !qqFvarDef fq (i + 1 + S + 1) ∧
    ∃ fr, !qqFvarDef fr (i + S + 1) ∧ ∃ f0, !qqFvarDef f0 0 ∧ ∃ cn, !cTVGraph cn n ∧
    ∃ bp, !bnumGraph bp lp ∧ ∃ bq, !bnumGraph bq lq ∧ ∃ bs, !bnumGraph bs (lp + lq) ∧ ∃ bs1, !bnumGraph bs1 (lp + lq + 1) ∧
    ∃ pq, !qqAddGraph pq bp bq ∧ ∃ pq1, !qqAddGraph pq1 pq ↑Arithmetic.one ∧ ∃ bs1', !qqAddGraph bs1' bs ↑Arithmetic.one ∧
    ∃ e₁, !mkVec₁Def e₁ fS ∧ ∃ s₁, !mkStepDef s₁ W 155 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ bq f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ bp e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ fr e₂₁ ∧ ∃ e₂₃, !adjoinDef e₂₃ fq e₂₂ ∧
    ∃ e₂₄, !adjoinDef e₂₄ fp e₂₃ ∧ ∃ e₂, !adjoinDef e₂ cn e₂₄ ∧ ∃ s₂, !mkStepDef s₂ W c e₂ ∧
    ∃ A₃, !addFactDef A₃ lp lq ∧ ∃ d₃, !addCodeDef d₃ T lp lq ∧ ∃ q₃, !pairDef q₃ A₃ d₃ ∧ ∃ s₃, !pairDef s₃ 7 q₃ ∧
    ∃ e₄, !mkVec₂Def e₄ pq bs ∧ ∃ s₄, !mkStepDef s₄ W 184 e₄ ∧
    ∃ A₅, !succFactDef A₅ (lp + lq) ∧ ∃ d₅, !succCodeDef d₅ T (lp + lq) ∧ ∃ q₅, !pairDef q₅ A₅ d₅ ∧ ∃ s₅, !pairDef s₅ 7 q₅ ∧
    ∃ e₆₀, !mkVec₂Def e₆₀ pq1 bs1' ∧ ∃ e₆, !adjoinDef e₆ f0 e₆₀ ∧ ∃ s₆, !mkStepDef s₆ W 123 e₆ ∧
    ∃ e₇₀, !mkVec₂Def e₇₀ bs1' bs1 ∧ ∃ e₇, !adjoinDef e₇ f0 e₇₀ ∧ ∃ s₇, !mkStepDef s₇ W 123 e₇ ∧
    ∃ e₈₀, !mkVec₂Def e₈₀ f0 bs1 ∧ ∃ e₈, !adjoinDef e₈ fr e₈₀ ∧ ∃ s₈, !mkStepDef s₈ W 145 e₈ ∧
    ∃ l₈, !mkVec₁Def l₈ s₈ ∧ ∃ l₇, !adjoinDef l₇ s₇ l₈ ∧ ∃ l₆, !adjoinDef l₆ s₆ l₇ ∧ ∃ l₅, !adjoinDef l₅ s₅ l₆ ∧
    ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l, !adjoinDef l s₁ l₂ ∧
    ∃ A, !appendVDef A yp l ∧ !appendVDef y yq A”

instance lnBinSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 12 → V ↦ lnBinSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11))
      lnBinStepsDef := .mk
  fun v ↦ by
    simp [lnBinStepsDef, lnBinSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      qqAdd_defined.iff, addFact_defined.iff, addCode_defined.iff, succFact_defined.iff, succCode_defined.iff,
      appendV_defined.iff, sLemma]
instance lnBinSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 12 → V ↦ lnBinSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) :=
  lnBinSteps_defined.to_definable

/-- A quantifier node (`all` at row `151`, `exs` at `152`) after the body's list `yb` (offset `i + 1`, level
`n + 1`, shifts `sb`): introduce the length at `&(i + sb)`, read `l = bnum lp + 1`, close by
`succFact lp` and `eqTrans`, then `congLenNum`. -/
noncomputable def lnQuantSteps (W T c n lp i sb yb : V) : V :=
  appendV yb
    ?[mkStep W 155 ?[^&(i + sb)],
      mkStep W c ?[cTV n, ^&(i + 1 + sb + 1), ^&(i + sb + 1), bnum lp, ^&0],
      sLemma (succFact lp) (succCode T lp),
      mkStep W 123 ?[^&0, bnum lp ^+ (𝟏 : V), bnum (lp + 1)],
      mkStep W 145 ?[^&(i + sb + 1), ^&0, bnum (lp + 1)]]

noncomputable def lnQuantStepsDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W T c n lp i sb yb.
    ∃ fS, !qqFvarDef fS (i + sb) ∧ ∃ fp, !qqFvarDef fp (i + 1 + sb + 1) ∧ ∃ fr, !qqFvarDef fr (i + sb + 1) ∧
    ∃ f0, !qqFvarDef f0 0 ∧ ∃ cn, !cTVGraph cn n ∧ ∃ bp, !bnumGraph bp lp ∧ ∃ bp1, !bnumGraph bp1 (lp + 1) ∧
    ∃ bp1', !qqAddGraph bp1' bp ↑Arithmetic.one ∧
    ∃ e₁, !mkVec₁Def e₁ fS ∧ ∃ s₁, !mkStepDef s₁ W 155 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ bp f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ fr e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ fp e₂₁ ∧ ∃ e₂, !adjoinDef e₂ cn e₂₂ ∧
    ∃ s₂, !mkStepDef s₂ W c e₂ ∧
    ∃ A₃, !succFactDef A₃ lp ∧ ∃ d₃, !succCodeDef d₃ T lp ∧ ∃ q₃, !pairDef q₃ A₃ d₃ ∧ ∃ s₃, !pairDef s₃ 7 q₃ ∧
    ∃ e₄₀, !mkVec₂Def e₄₀ bp1' bp1 ∧ ∃ e₄, !adjoinDef e₄ f0 e₄₀ ∧ ∃ s₄, !mkStepDef s₄ W 123 e₄ ∧
    ∃ e₅₀, !mkVec₂Def e₅₀ f0 bp1 ∧ ∃ e₅, !adjoinDef e₅ fr e₅₀ ∧ ∃ s₅, !mkStepDef s₅ W 145 e₅ ∧
    ∃ l₅, !mkVec₁Def l₅ s₅ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧
    ∃ l, !adjoinDef l s₁ l₂ ∧ !appendVDef y yb l”

instance lnQuantSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ lnQuantSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) lnQuantStepsDef := .mk
  fun v ↦ by
    simp [lnQuantStepsDef, lnQuantSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      qqAdd_defined.iff, succFact_defined.iff, succCode_defined.iff, appendV_defined.iff, sLemma]
instance lnQuantSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 8 → V ↦ lnQuantSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  lnQuantSteps_defined.to_definable

/-- An atom (`rel` at row `142`, `nrel` at `143`) after the vector's list `yv` (offset `i + 1`, shifts `sv`,
leaving the length vector at `&0` (`vRef 0 k`) and `listSumFact (bnum σ) ⟨M⟩`): the closed symbol row, the
length at `&(i + sv)`, `formulaLenRelCert` at `[cT k, cT R, ⟨v⟩, &p, ⟨M⟩, bnum σ, &0]` reading
`l = bnum σ + 1`, `succFact σ`, `eqTrans`, `congLenNum`. -/
noncomputable def lnAtomSteps (W T c k R σ i sv yv : V) : V :=
  appendV yv
    ?[mkStep W (relRow R) 0,
      mkStep W 155 ?[^&(i + sv)],
      mkStep W c ?[cTV k, cTV R, vRef (i + 1 + sv + 1) k, ^&(i + sv + 1), vRef 1 k, bnum σ, ^&0],
      sLemma (succFact σ) (succCode T σ),
      mkStep W 123 ?[^&0, bnum σ ^+ (𝟏 : V), bnum (σ + 1)],
      mkStep W 145 ?[^&(i + sv + 1), ^&0, bnum (σ + 1)]]

noncomputable def lnAtomStepsDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y W T c k R σ i sv yv. ∃ ρ, !relRowDef ρ R ∧ ∃ s₀, !mkStepDef s₀ W ρ 0 ∧
    ∃ fS, !qqFvarDef fS (i + sv) ∧ ∃ fr, !qqFvarDef fr (i + sv + 1) ∧ ∃ f0, !qqFvarDef f0 0 ∧
    ∃ ck, !cTVGraph ck k ∧ ∃ cR, !cTVGraph cR R ∧ ∃ rv, !vRefDef rv (i + 1 + sv + 1) k ∧ ∃ rM, !vRefDef rM 1 k ∧
    ∃ bσ, !bnumGraph bσ σ ∧ ∃ bσ1, !bnumGraph bσ1 (σ + 1) ∧ ∃ bσ1', !qqAddGraph bσ1' bσ ↑Arithmetic.one ∧
    ∃ e₁, !mkVec₁Def e₁ fS ∧ ∃ s₁, !mkStepDef s₁ W 155 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ bσ f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ rM e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ fr e₂₁ ∧ ∃ e₂₃, !adjoinDef e₂₃ rv e₂₂ ∧
    ∃ e₂₄, !adjoinDef e₂₄ cR e₂₃ ∧ ∃ e₂, !adjoinDef e₂ ck e₂₄ ∧ ∃ s₂, !mkStepDef s₂ W c e₂ ∧
    ∃ A₃, !succFactDef A₃ σ ∧ ∃ d₃, !succCodeDef d₃ T σ ∧ ∃ q₃, !pairDef q₃ A₃ d₃ ∧ ∃ s₃, !pairDef s₃ 7 q₃ ∧
    ∃ e₄₀, !mkVec₂Def e₄₀ bσ1' bσ1 ∧ ∃ e₄, !adjoinDef e₄ f0 e₄₀ ∧ ∃ s₄, !mkStepDef s₄ W 123 e₄ ∧
    ∃ e₅₀, !mkVec₂Def e₅₀ f0 bσ1 ∧ ∃ e₅, !adjoinDef e₅ fr e₅₀ ∧ ∃ s₅, !mkStepDef s₅ W 145 e₅ ∧
    ∃ l₅, !mkVec₁Def l₅ s₅ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧
    ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ ∃ l, !adjoinDef l s₀ l₁ ∧ !appendVDef y yv l”

instance lnAtomSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → V ↦ lnAtomSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) lnAtomStepsDef := .mk
  fun v ↦ by
    simp [lnAtomStepsDef, lnAtomSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      vRef_defined.iff, relRow_defined.iff, qqAdd_defined.iff, succFact_defined.iff, succCode_defined.iff,
      appendV_defined.iff, sLemma]
instance lnAtomSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 9 → V ↦ lnAtomSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  lnAtomSteps_defined.to_definable

/-- A term leaf (`bvar` at row `153`, `fvar` at `154`, index `z`): `termLenTotal`, the row reading
`l = cT z + 1`, the closed `cTEqFact (z + 1)` (`cT (z + 1) = bnum (z + 1)`, and `cT (z + 1) = cT z + 1`
syntactically), `eqTrans`, `congTLenNum`. -/
noncomputable def lnLeafSteps (W T c z i : V) : V :=
  ?[mkStep W 156 ?[^&i],
    mkStep W c ?[cTV z, ^&(i + 1), ^&0],
    sLemma (cTEqFact (z + 1)) (cTEqCode T (z + 1)),
    mkStep W 123 ?[^&0, cTV (z + 1), bnum (z + 1)],
    mkStep W 146 ?[^&(i + 1), ^&0, bnum (z + 1)]]

noncomputable def lnLeafStepsDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W T c z i. ∃ fi, !qqFvarDef fi i ∧ ∃ fi', !qqFvarDef fi' (i + 1) ∧ ∃ f0, !qqFvarDef f0 0 ∧
    ∃ cz, !cTVGraph cz z ∧ ∃ cz1, !cTVGraph cz1 (z + 1) ∧ ∃ bz1, !bnumGraph bz1 (z + 1) ∧
    ∃ e₁, !mkVec₁Def e₁ fi ∧ ∃ s₁, !mkStepDef s₁ W 156 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ fi' f0 ∧ ∃ e₂, !adjoinDef e₂ cz e₂₀ ∧ ∃ s₂, !mkStepDef s₂ W c e₂ ∧
    ∃ A₃, !cTEqFactDef A₃ (z + 1) ∧ ∃ d₃, !cTEqCodeDef d₃ T (z + 1) ∧ ∃ q₃, !pairDef q₃ A₃ d₃ ∧ ∃ s₃, !pairDef s₃ 7 q₃ ∧
    ∃ e₄₀, !mkVec₂Def e₄₀ cz1 bz1 ∧ ∃ e₄, !adjoinDef e₄ f0 e₄₀ ∧ ∃ s₄, !mkStepDef s₄ W 123 e₄ ∧
    ∃ e₅₀, !mkVec₂Def e₅₀ f0 bz1 ∧ ∃ e₅, !adjoinDef e₅ fi' e₅₀ ∧ ∃ s₅, !mkStepDef s₅ W 146 e₅ ∧
    ∃ l₅, !mkVec₁Def l₅ s₅ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧
    !adjoinDef y s₁ l₂”

instance lnLeafSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ lnLeafSteps (v 0) (v 1) (v 2) (v 3) (v 4)) lnLeafStepsDef := .mk
  fun v ↦ by
    simp [lnLeafStepsDef, lnLeafSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      cTEqFact_defined.iff, cTEqCode_defined.iff, sLemma]
instance lnLeafSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 5 → V ↦ lnLeafSteps (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  lnLeafSteps_defined.to_definable

/-- A function node after the vector's list `yv` (as `lnAtomSteps`, with `termLenFuncCert` (row `144`) and
`congTLenNum` (`146`)). -/
noncomputable def lnFuncSteps (W T k f σ i sv yv : V) : V :=
  appendV yv
    ?[mkStep W (funcRow k f) 0,
      mkStep W 156 ?[^&(i + sv)],
      mkStep W 144 ?[cTV k, cTV f, vRef (i + 1 + sv + 1) k, ^&(i + sv + 1), vRef 1 k, bnum σ, ^&0],
      sLemma (succFact σ) (succCode T σ),
      mkStep W 123 ?[^&0, bnum σ ^+ (𝟏 : V), bnum (σ + 1)],
      mkStep W 146 ?[^&(i + sv + 1), ^&0, bnum (σ + 1)]]

noncomputable def lnFuncStepsDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W T k f σ i sv yv. ∃ ρ, !funcRowDef ρ k f ∧ ∃ s₀, !mkStepDef s₀ W ρ 0 ∧
    ∃ fS, !qqFvarDef fS (i + sv) ∧ ∃ fr, !qqFvarDef fr (i + sv + 1) ∧ ∃ f0, !qqFvarDef f0 0 ∧
    ∃ ck, !cTVGraph ck k ∧ ∃ cf, !cTVGraph cf f ∧ ∃ rv, !vRefDef rv (i + 1 + sv + 1) k ∧ ∃ rM, !vRefDef rM 1 k ∧
    ∃ bσ, !bnumGraph bσ σ ∧ ∃ bσ1, !bnumGraph bσ1 (σ + 1) ∧ ∃ bσ1', !qqAddGraph bσ1' bσ ↑Arithmetic.one ∧
    ∃ e₁, !mkVec₁Def e₁ fS ∧ ∃ s₁, !mkStepDef s₁ W 156 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ bσ f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ rM e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ fr e₂₁ ∧ ∃ e₂₃, !adjoinDef e₂₃ rv e₂₂ ∧
    ∃ e₂₄, !adjoinDef e₂₄ cf e₂₃ ∧ ∃ e₂, !adjoinDef e₂ ck e₂₄ ∧ ∃ s₂, !mkStepDef s₂ W 144 e₂ ∧
    ∃ A₃, !succFactDef A₃ σ ∧ ∃ d₃, !succCodeDef d₃ T σ ∧ ∃ q₃, !pairDef q₃ A₃ d₃ ∧ ∃ s₃, !pairDef s₃ 7 q₃ ∧
    ∃ e₄₀, !mkVec₂Def e₄₀ bσ1' bσ1 ∧ ∃ e₄, !adjoinDef e₄ f0 e₄₀ ∧ ∃ s₄, !mkStepDef s₄ W 123 e₄ ∧
    ∃ e₅₀, !mkVec₂Def e₅₀ f0 bσ1 ∧ ∃ e₅, !adjoinDef e₅ fr e₅₀ ∧ ∃ s₅, !mkStepDef s₅ W 146 e₅ ∧
    ∃ l₅, !mkVec₁Def l₅ s₅ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧
    ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ ∃ l, !adjoinDef l s₀ l₁ ∧ !appendVDef y yv l”

instance lnFuncSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ lnFuncSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) lnFuncStepsDef := .mk
  fun v ↦ by
    simp [lnFuncStepsDef, lnFuncSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      vRef_defined.iff, funcRow_defined.iff, qqAdd_defined.iff, succFact_defined.iff, succCode_defined.iff,
      appendV_defined.iff, sLemma]
instance lnFuncSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 8 → V ↦ lnFuncSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  lnFuncSteps_defined.to_definable

/-- The empty vector: `termLenVecNil` (row `138`) and `listSumNil` (`140`), their dummy witness `cT 0`. -/
noncomputable def lnNilSteps (W : V) : V := ?[mkStep W 138 ?[cTV 0], mkStep W 140 ?[cTV 0]]

noncomputable def lnNilStepsDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y W. ∃ c0, !cTVGraph c0 0 ∧ ∃ e, !mkVec₁Def e c0 ∧ ∃ s₁, !mkStepDef s₁ W 138 e ∧ ∃ s₂, !mkStepDef s₂ W 140 e ∧
    ∃ l₂, !mkVec₁Def l₂ s₂ ∧ !adjoinDef y s₁ l₂”

instance lnNilSteps_defined : 𝚺₁-Function₁ (lnNilSteps : V → V) via lnNilStepsDef := .mk
  fun v ↦ by simp [lnNilStepsDef, lnNilSteps, numeral_eq_natCast, mkStep_defined.iff, cTV.defined.iff]
instance lnNilSteps_definable : 𝚺₁-Function₁ (lnNilSteps : V → V) := lnNilSteps_defined.to_definable

/-- A vector node with `m` tail entries: the entry's list `yt` (offset `i + 1`, shifts `st`), the tail's `yv`
(offset `i + 1 + ct + st`, shifts `sv`; its length vector at `&0` = `vRef 0 m`, sum `bnum σ'`), `S = st + sv + 1`:
`adjoinTotal [bnum lt, ⟨M⟩]` (the new length vector `&0`), the tail's `utvPi` bridge (rows 38/39),
`termLenVecAdj [cT n, cT m, ⟨tail⟩, &v', &t, bnum lt, ⟨M⟩, &0]`, `addFact lt σ'`, and
`listSumAdjI [&0, ⟨M⟩, bnum lt, bnum σ', bnum (lt + σ')]`. -/
noncomputable def lnAdjSteps (W T n m ct lt σ' i st sv yt yv : V) : V :=
  appendV yt (appendV yv
    ?[mkStep W 17 ?[bnum lt, vRef 0 m],
      mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + ct + (st + sv + 1)) m],
      mkStep W 39 ?[cTV m, vRef (i + 1 + ct + (st + sv + 1)) m],
      mkStep W 139 ?[cTV n, cTV m, vRef (i + 1 + ct + (st + sv + 1)) m, ^&(i + (st + sv + 1)), ^&(i + 1 + (st + sv + 1)),
        bnum lt, vRef 1 m, ^&0],
      sLemma (addFact lt σ') (addCode T lt σ'),
      mkStep W 185 ?[^&0, vRef 1 m, bnum lt, bnum σ', bnum (lt + σ')]])

noncomputable def lnAdjStepsDef : 𝚺₁.Semisentence 13 := .mkSigma
  “y W T n m ct lt σ' i st sv yt yv. ∃ S, S = st + sv + 1 ∧
    ∃ bt, !bnumGraph bt lt ∧ ∃ bσ, !bnumGraph bσ σ' ∧ ∃ bs, !bnumGraph bs (lt + σ') ∧
    ∃ r0, !vRefDef r0 0 m ∧ ∃ r1, !vRefDef r1 1 m ∧ ∃ rt, !vRefDef rt (i + 1 + ct + S) m ∧
    ∃ cn, !cTVGraph cn n ∧ ∃ cm, !cTVGraph cm m ∧ ∃ fv, !qqFvarDef fv (i + S) ∧ ∃ ft, !qqFvarDef ft (i + 1 + S) ∧
    ∃ f0, !qqFvarDef f0 0 ∧
    ∃ e₁, !mkVec₂Def e₁ bt r0 ∧ ∃ s₁, !mkStepDef s₁ W 17 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ cn rt ∧ ∃ e₂, !adjoinDef e₂ cm e₂₀ ∧ ∃ s₂, !mkStepDef s₂ W 38 e₂ ∧
    ∃ e₃, !mkVec₂Def e₃ cm rt ∧ ∃ s₃, !mkStepDef s₃ W 39 e₃ ∧
    ∃ e₄₀, !mkVec₂Def e₄₀ r1 f0 ∧ ∃ e₄₁, !adjoinDef e₄₁ bt e₄₀ ∧ ∃ e₄₂, !adjoinDef e₄₂ ft e₄₁ ∧ ∃ e₄₃, !adjoinDef e₄₃ fv e₄₂ ∧
    ∃ e₄₄, !adjoinDef e₄₄ rt e₄₃ ∧ ∃ e₄₅, !adjoinDef e₄₅ cm e₄₄ ∧ ∃ e₄, !adjoinDef e₄ cn e₄₅ ∧ ∃ s₄, !mkStepDef s₄ W 139 e₄ ∧
    ∃ A₅, !addFactDef A₅ lt σ' ∧ ∃ d₅, !addCodeDef d₅ T lt σ' ∧ ∃ q₅, !pairDef q₅ A₅ d₅ ∧ ∃ s₅, !pairDef s₅ 7 q₅ ∧
    ∃ e₆₀, !mkVec₂Def e₆₀ bσ bs ∧ ∃ e₆₁, !adjoinDef e₆₁ bt e₆₀ ∧ ∃ e₆₂, !adjoinDef e₆₂ r1 e₆₁ ∧ ∃ e₆, !adjoinDef e₆ f0 e₆₂ ∧
    ∃ s₆, !mkStepDef s₆ W 185 e₆ ∧
    ∃ l₆, !mkVec₁Def l₆ s₆ ∧ ∃ l₅, !adjoinDef l₅ s₅ l₆ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧
    ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l, !adjoinDef l s₁ l₂ ∧ ∃ A, !appendVDef A yv l ∧ !appendVDef y yt A”

instance lnAdjSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 12 → V ↦ lnAdjSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11))
      lnAdjStepsDef := .mk
  fun v ↦ by
    simp [lnAdjStepsDef, lnAdjSteps, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      vRef_defined.iff, addFact_defined.iff, addCode_defined.iff, appendV_defined.iff, sLemma]
instance lnAdjSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 12 → V ↦ lnAdjSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) :=
  lnAdjSteps_defined.to_definable

end lenBuilders

/-! ### 5.2 The term/vector fixpoint `LenT` on `⟪tg, n, x, i, y⟫` (`tg = 0`: term `x`; `tg = 1`: `x = ⟪k, v, m⟫`),
parameters `W` (the pieces) and `T` (the `NumSteps` table of the `sLemma` codes) -/

namespace LenT

/-- The cases of the length operator on the unpacked tuple. -/
def Cases (W T : V) (C : Set V) (tg n x i y : V) : Prop :=
  (tg = 0 ∧ ∃ z < x, x = ^#z ∧ y = lnLeafSteps W T 153 z i) ∨
  (tg = 0 ∧ ∃ a < x, x = ^&a ∧ y = lnLeafSteps W T 154 a i) ∨
  (tg = 0 ∧ ∃ k < x, ∃ f < x, ∃ w < x, x = ^func k f w ∧ ∃ yv ≤ y,
    ⟪1, n, ⟪k, w, k⟫, i + 1, yv⟫ ∈ C ∧ y = lnFuncSteps W T k f (listSum (termLenVec LAct k w)) i (shiftsV yv) yv) ∨
  (tg = 1 ∧ ∃ k ≤ x, ∃ q ≤ x, x = ⟪k, q⟫ ∧ ∃ v ≤ q, ∃ m ≤ q, q = ⟪v, m⟫ ∧ m = 0 ∧ y = lnNilSteps W) ∨
  (tg = 1 ∧ ∃ k ≤ x, ∃ q ≤ x, x = ⟪k, q⟫ ∧ ∃ v ≤ q, ∃ m ≤ q, q = ⟪v, m⟫ ∧ ∃ m' < m, m = m' + 1 ∧
    ∃ yt ≤ y, ∃ yv ≤ y, ⟪0, n, nthFromEnd v m', i + 1, yt⟫ ∈ C ∧
    ⟪1, n, ⟪k, v, m'⟫, i + 1 + descCountT W n (nthFromEnd v m') + shiftsV yt, yv⟫ ∈ C ∧
    y = lnAdjSteps W T n m' (descCountT W n (nthFromEnd v m')) (termLen LAct (nthFromEnd v m'))
      (listSum (termLenVec LAct m' (takeLast v m'))) i (shiftsV yt) (shiftsV yv) yt yv)

/-- The operator on the packed tuples. -/
def Phi (W T : V) (C : Set V) (pr : V) : Prop :=
  ∃ tg ≤ pr, ∃ q₁ ≤ pr, pr = ⟪tg, q₁⟫ ∧ ∃ n ≤ q₁, ∃ q₂ ≤ q₁, q₁ = ⟪n, q₂⟫ ∧
  ∃ x ≤ q₂, ∃ q₃ ≤ q₂, q₂ = ⟪x, q₃⟫ ∧ ∃ i ≤ q₃, ∃ y ≤ q₃, q₃ = ⟪i, y⟫ ∧ Cases W T C tg n x i y

lemma phi_unpack (W T : V) (C : Set V) (pr : V) :
    Phi W T C pr ↔ ∃ tg n x i y, pr = ⟪tg, n, x, i, y⟫ ∧ Cases W T C tg n x i y := by
  constructor
  · rintro ⟨tg, _, q₁, _, rfl, n, _, q₂, _, rfl, x, _, q₃, _, rfl, i, _, y, _, rfl, h⟩
    exact ⟨tg, n, x, i, y, rfl, h⟩
  · rintro ⟨tg, n, x, i, y, rfl, h⟩
    exact ⟨tg, le_pair_left _ _, _, le_pair_right _ _, rfl, n, le_pair_left _ _, _, le_pair_right _ _, rfl,
      x, le_pair_left _ _, _, le_pair_right _ _, rfl, i, le_pair_left _ _, y, le_pair_right _ _, rfl, h⟩

lemma phi_of_cases {W T : V} {C : Set V} {tg n x i y : V} (h : Cases W T C tg n x i y) :
    Phi W T C ⟪tg, n, x, i, y⟫ := (phi_unpack W T C _).mpr ⟨tg, n, x, i, y, rfl, h⟩

lemma cases_of_phi {W T : V} {C : Set V} {tg n x i y : V} (h : Phi W T C ⟪tg, n, x, i, y⟫) :
    Cases W T C tg n x i y := by
  obtain ⟨tg', n', x', i', y', e, h⟩ := (phi_unpack W T C _).mp h
  rw [pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff] at e
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
  exact h

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C W T.
    ∃ tg <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr tg q₁ ∧ ∃ n <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ n q₂ ∧
    ∃ x <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ x q₃ ∧ ∃ i <⁺ q₃, ∃ y <⁺ q₃, !pairDef q₃ i y ∧
    ( (tg = 0 ∧ ∃ z < x, !qqBvarDef x z ∧ ∃ s, !lnLeafStepsDef s W T 153 z i ∧ y = s) ∨
      (tg = 0 ∧ ∃ a < x, !qqFvarDef x a ∧ ∃ s, !lnLeafStepsDef s W T 154 a i ∧ y = s) ∨
      (tg = 0 ∧ ∃ k < x, ∃ f < x, ∃ w < x, !qqFuncDef x k f w ∧ ∃ yv <⁺ y, ∃ x₁, !pairDef x₁ w k ∧ ∃ x₂, !pairDef x₂ k x₁ ∧
        ∃ r₄, !pairDef r₄ (i + 1) yv ∧ ∃ r₃, !pairDef r₃ x₂ r₄ ∧ ∃ r₂, !pairDef r₂ n r₃ ∧ :⟪1, r₂⟫:∈ C ∧
        ∃ M, !(termLenVecGraph LAct) M k w ∧ ∃ σ, !listSumDef σ M ∧ ∃ sv, !shiftsVDef sv yv ∧
        ∃ s, !lnFuncStepsDef s W T k f σ i sv yv ∧ y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ m = 0 ∧ ∃ s, !lnNilStepsDef s W ∧ y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ ∃ m' < m, m = m' + 1 ∧
        ∃ yt <⁺ y, ∃ yv <⁺ y, ∃ t, !nthFromEndDef t v m' ∧ ∃ ct, !descCountTDef ct W n t ∧ ∃ st, !shiftsVDef st yt ∧
        ∃ p₄, !pairDef p₄ (i + 1) yt ∧ ∃ p₃, !pairDef p₃ t p₄ ∧ ∃ p₂, !pairDef p₂ n p₃ ∧ :⟪0, p₂⟫:∈ C ∧
        ∃ x₁, !pairDef x₁ v m' ∧ ∃ x₂, !pairDef x₂ k x₁ ∧
        ∃ r₄, !pairDef r₄ (i + 1 + ct + st) yv ∧ ∃ r₃, !pairDef r₃ x₂ r₄ ∧ ∃ r₂, !pairDef r₂ n r₃ ∧ :⟪1, r₂⟫:∈ C ∧
        ∃ lt, !(termLenGraph LAct) lt t ∧ ∃ u, !takeLastDef u v m' ∧ ∃ M, !(termLenVecGraph LAct) M m' u ∧
        ∃ σ, !listSumDef σ M ∧ ∃ sv, !shiftsVDef sv yv ∧
        ∃ s, !lnAdjStepsDef s W T n m' ct lt σ i st sv yt yv ∧ y = s) )”)
  (.mkPi “pr C W T.
    ∃ tg <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr tg q₁ ∧ ∃ n <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ n q₂ ∧
    ∃ x <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ x q₃ ∧ ∃ i <⁺ q₃, ∃ y <⁺ q₃, !pairDef q₃ i y ∧
    ( (tg = 0 ∧ ∃ z < x, !qqBvarDef x z ∧ ∀ s, !lnLeafStepsDef s W T 153 z i → y = s) ∨
      (tg = 0 ∧ ∃ a < x, !qqFvarDef x a ∧ ∀ s, !lnLeafStepsDef s W T 154 a i → y = s) ∨
      (tg = 0 ∧ ∃ k < x, ∃ f < x, ∃ w < x, !qqFuncDef x k f w ∧ ∃ yv <⁺ y, ∀ x₁, !pairDef x₁ w k → ∀ x₂, !pairDef x₂ k x₁ →
        ∀ r₄, !pairDef r₄ (i + 1) yv → ∀ r₃, !pairDef r₃ x₂ r₄ → ∀ r₂, !pairDef r₂ n r₃ → :⟪1, r₂⟫:∈ C ∧
        ∀ M, !(termLenVecGraph LAct) M k w → ∀ σ, !listSumDef σ M → ∀ sv, !shiftsVDef sv yv →
        ∀ s, !lnFuncStepsDef s W T k f σ i sv yv → y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ m = 0 ∧ ∀ s, !lnNilStepsDef s W → y = s) ∨
      (tg = 1 ∧ ∃ k <⁺ x, ∃ q <⁺ x, !pairDef x k q ∧ ∃ v <⁺ q, ∃ m <⁺ q, !pairDef q v m ∧ ∃ m' < m, m = m' + 1 ∧
        ∃ yt <⁺ y, ∃ yv <⁺ y, ∀ t, !nthFromEndDef t v m' → ∀ ct, !descCountTDef ct W n t → ∀ st, !shiftsVDef st yt →
        ∀ p₄, !pairDef p₄ (i + 1) yt → ∀ p₃, !pairDef p₃ t p₄ → ∀ p₂, !pairDef p₂ n p₃ → :⟪0, p₂⟫:∈ C ∧
        ∀ x₁, !pairDef x₁ v m' → ∀ x₂, !pairDef x₂ k x₁ →
        ∀ r₄, !pairDef r₄ (i + 1 + ct + st) yv → ∀ r₃, !pairDef r₃ x₂ r₄ → ∀ r₂, !pairDef r₂ n r₃ → :⟪1, r₂⟫:∈ C ∧
        ∀ lt, !(termLenGraph LAct) lt t → ∀ u, !takeLastDef u v m' → ∀ M, !(termLenVecGraph LAct) M m' u →
        ∀ σ, !listSumDef σ M → ∀ sv, !shiftsVDef sv yv →
        ∀ s, !lnAdjStepsDef s W T n m' ct lt σ i st sv yt yv → y = s) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, lnLeafSteps_defined.iff, lnFuncSteps_defined.iff, lnNilSteps_defined.iff, lnAdjSteps_defined.iff,
        nthFromEnd_defined.iff, descCountT_defined.iff, shiftsV_defined.iff, listSum_defined.iff, takeLast_defined.iff,
        (termLenVec.defined (L := LAct)).iff, (termLen.defined (L := LAct)).iff, numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, Cases, lnLeafSteps_defined.iff, lnFuncSteps_defined.iff, lnNilSteps_defined.iff, lnAdjSteps_defined.iff,
        nthFromEnd_defined.iff, descCountT_defined.iff, shiftsV_defined.iff, listSum_defined.iff, takeLast_defined.iff,
        (termLenVec.defined (L := LAct)).iff, (termLen.defined (L := LAct)).iff, numeral_eq_natCast]
  monotone := by
    intro C C' hC w pr h
    change Phi (w 0) (w 1) C pr at h
    rw [phi_unpack] at h ⊢
    obtain ⟨tg, n, x, i, y, rfl, h⟩ := h
    refine ⟨tg, n, x, i, y, rfl, ?_⟩
    rcases h with h | h | ⟨htg, k, hk, f, hf, w', hw, rfl, yv, hyv, h₁, rfl⟩ | h |
      ⟨htg, k, hk, q, hq, rfl, v, hv, m, hm, rfl, m', hm', rfl, yt, hyt, yv, hyv, h₁, h₂, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨htg, k, hk, f, hf, w', hw, rfl, yv, hyv, hC h₁, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨htg, k, hk, _, hq, rfl, v, hv, _, hm, rfl, m', hm', rfl, yt, hyt, yv, hyv, hC h₁, hC h₂, rfl⟩)))

instance : construction.Finite V where
  finite := by
    intro C w pr h
    change Phi (w 0) (w 1) C pr at h
    change ∃ m, Phi (w 0) (w 1) {y ∈ C | y < m} pr
    rw [phi_unpack] at h
    simp only [phi_unpack]
    obtain ⟨tg, n, x, i, y, rfl, h⟩ := h
    rcases h with h | h | ⟨htg, k, hk, f, hf, w', hw, hx, yv, hyv, h₁, hy⟩ | h |
      ⟨htg, k, hk, q, hq, hx, v, hv, m, hm, hq', m', hm', hmm, yt, hyt, yv, hyv, h₁, h₂, hy⟩
    · exact ⟨0, tg, n, x, i, y, rfl, Or.inl h⟩
    · exact ⟨0, tg, n, x, i, y, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨⟪1, n, ⟪k, w', k⟫, i + 1, yv⟫ + 1, tg, n, x, i, y, rfl,
        Or.inr (Or.inr (Or.inl ⟨htg, k, hk, f, hf, w', hw, hx, yv, hyv, ⟨h₁, lt_add_one _⟩, hy⟩))⟩
    · exact ⟨0, tg, n, x, i, y, rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · refine ⟨⟪0, n, nthFromEnd v m', i + 1, yt⟫ + ⟪1, n, ⟪k, v, m'⟫, i + 1 + descCountT (w 0) n (nthFromEnd v m') + shiftsV yt, yv⟫ + 1,
        tg, n, x, i, y, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨htg, k, hk, q, hq, hx, v, hv, m, hm, hq', m', hm', hmm, yt, hyt, yv, hyv,
          ⟨h₁, lt_of_le_of_lt le_self_add (lt_add_one _)⟩, ⟨h₂, lt_of_le_of_lt le_add_self (lt_add_one _)⟩, hy⟩)))⟩

/-- `Phi` at a term tuple. -/
lemma phi_term_iff (W T : V) (C : Set V) (n t i y : V) :
    Phi W T C ⟪0, n, t, i, y⟫ ↔
    ( (∃ z, t = ^#z ∧ y = lnLeafSteps W T 153 z i) ∨
      (∃ a, t = ^&a ∧ y = lnLeafSteps W T 154 a i) ∨
      (∃ k f w yv, t = ^func k f w ∧ yv ≤ y ∧ ⟪1, n, ⟪k, w, k⟫, i + 1, yv⟫ ∈ C ∧
        y = lnFuncSteps W T k f (listSum (termLenVec LAct k w)) i (shiftsV yv) yv) ) := by
  rw [show Phi W T C ⟪0, n, t, i, y⟫ ↔ Cases W T C 0 n t i y from ⟨cases_of_phi, phi_of_cases⟩]
  unfold Cases
  constructor
  · rintro (⟨_, z, _, rfl, rfl⟩ | ⟨_, a, _, rfl, rfl⟩ | ⟨_, k, _, f, _, w, _, rfl, yv, hyv, h₁, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl ⟨z, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨a, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨k, f, w, yv, rfl, hyv, h₁, rfl⟩)
    · exact absurd h zero_ne_one
    · exact absurd h zero_ne_one
  · rintro (⟨z, rfl, rfl⟩ | ⟨a, rfl, rfl⟩ | ⟨k, f, w, yv, rfl, hyv, h₁, rfl⟩)
    · exact Or.inl ⟨rfl, z, by simp, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, a, by simp, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, k, by simp, f, by simp, w, by simp, rfl, yv, hyv, h₁, rfl⟩))

/-- `Phi` at a vector tuple. -/
lemma phi_vec_iff (W T : V) (C : Set V) (n k v m i y : V) :
    Phi W T C ⟪1, n, ⟪k, v, m⟫, i, y⟫ ↔
    ( (m = 0 ∧ y = lnNilSteps W) ∨
      (∃ m' yt yv, m = m' + 1 ∧ yt ≤ y ∧ yv ≤ y ∧ ⟪0, n, nthFromEnd v m', i + 1, yt⟫ ∈ C ∧
        ⟪1, n, ⟪k, v, m'⟫, i + 1 + descCountT W n (nthFromEnd v m') + shiftsV yt, yv⟫ ∈ C ∧
        y = lnAdjSteps W T n m' (descCountT W n (nthFromEnd v m')) (termLen LAct (nthFromEnd v m'))
          (listSum (termLenVec LAct m' (takeLast v m'))) i (shiftsV yt) (shiftsV yv) yt yv) ) := by
  rw [show Phi W T C ⟪1, n, ⟪k, v, m⟫, i, y⟫ ↔ Cases W T C 1 n ⟪k, v, m⟫ i y from ⟨cases_of_phi, phi_of_cases⟩]
  unfold Cases
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, k', _, q, _, e, v', _, m'', _, e', hm, rfl⟩ |
      ⟨_, k', _, q, _, e, v', _, m'', _, e', m', hm', hmm, yt, hyt, yv, hyv, h₁, h₂, rfl⟩)
    · exact absurd h _root_.one_ne_zero
    · exact absurd h _root_.one_ne_zero
    · exact absurd h _root_.one_ne_zero
    · rw [pair_ext_iff] at e; obtain ⟨rfl, rfl⟩ := e
      rw [pair_ext_iff] at e'; obtain ⟨rfl, rfl⟩ := e'
      exact Or.inl ⟨hm, rfl⟩
    · rw [pair_ext_iff] at e; obtain ⟨rfl, rfl⟩ := e
      rw [pair_ext_iff] at e'; obtain ⟨rfl, rfl⟩ := e'
      exact Or.inr ⟨m', yt, yv, hmm, hyt, hyv, h₁, h₂, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨m', yt, yv, rfl, hyt, hyv, h₁, h₂, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k, le_pair_left _ _, _, le_pair_right _ _, rfl, v, le_pair_left _ _, 0,
        le_pair_right _ _, rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k, le_pair_left _ _, _, le_pair_right _ _, rfl, v, le_pair_left _ _, m' + 1,
        le_pair_right _ _, rfl, m', lt_add_one _, rfl, yt, hyt, yv, hyv, h₁, h₂, rfl⟩)))

end LenT

/-- The fixpoint on the PACKED tuples (kept separate so that instance search never unfolds it). -/
def LenTPacked (W T pr : V) : Prop := LenT.construction.Fixpoint ![W, T] pr
/-- `LenTGraph W T n t i y`: the length steps of the term `t` (at `&i`) are the list `y`. -/
def LenTGraph (W T n t i y : V) : Prop := LenTPacked W T ⟪0, n, t, i, y⟫
/-- `LenVGraph W T n k v m i y`: the length steps of the last `m` entries of the vector `v` (of length `k`, at `&i`). -/
def LenVGraph (W T n k v m i y : V) : Prop := LenTPacked W T ⟪1, n, ⟪k, v, m⟫, i, y⟫

noncomputable def lenTPackedDef : 𝚺₁.Semisentence 3 := .mkSigma “W T pr. !LenT.blueprint.fixpointDef pr W T”

-- The house pattern (`Cert.lean:1679`): never let `simp` unfold the blueprint here.
instance lenTPacked_defined : 𝚺₁-Relation₃ (LenTPacked : V → V → V → Prop) via lenTPackedDef := .mk
  fun v ↦ by
    simp only [lenTPackedDef, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.constant_eq_singleton]
    rw [LenT.construction.eval_fixpointDef]
    rfl
instance lenTPacked_definable : 𝚺₁-Relation₃ (LenTPacked : V → V → V → Prop) := lenTPacked_defined.to_definable

noncomputable def lenTGraphDef : 𝚺₁.Semisentence 6 := .mkSigma
  “W T n t i y. ∃ q₃, !pairDef q₃ i y ∧ ∃ q₂, !pairDef q₂ t q₃ ∧ ∃ q₁, !pairDef q₁ n q₂ ∧ ∃ pr, !pairDef pr 0 q₁ ∧
    !lenTPackedDef W T pr”
instance lenTGraph_defined :
    𝚺₁.Defined (fun v : Fin 6 → V ↦ LenTGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) lenTGraphDef := .mk
  fun v ↦ by simp [lenTGraphDef, lenTPacked_defined.iff, LenTGraph]
instance lenTGraph_definable :
    𝚺₁.Definable (fun v : Fin 6 → V ↦ LenTGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := lenTGraph_defined.to_definable

noncomputable def lenVGraphDef : 𝚺₁.Semisentence 8 := .mkSigma
  “W T n k v m i y. ∃ q₃, !pairDef q₃ i y ∧ ∃ x₁, !pairDef x₁ v m ∧ ∃ x, !pairDef x k x₁ ∧ ∃ q₂, !pairDef q₂ x q₃ ∧
    ∃ q₁, !pairDef q₁ n q₂ ∧ ∃ pr, !pairDef pr 1 q₁ ∧ !lenTPackedDef W T pr”
instance lenVGraph_defined :
    𝚺₁.Defined (fun v : Fin 8 → V ↦ LenVGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) lenVGraphDef := .mk
  fun v ↦ by simp [lenVGraphDef, lenTPacked_defined.iff, LenVGraph]
instance lenVGraph_definable :
    𝚺₁.Definable (fun v : Fin 8 → V ↦ LenVGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) := lenVGraph_defined.to_definable

/-! #### Case analysis and inversion -/

lemma LenTGraph.case_iff {W T n t i y : V} :
    LenTGraph W T n t i y ↔
    ( (∃ z, t = ^#z ∧ y = lnLeafSteps W T 153 z i) ∨
      (∃ a, t = ^&a ∧ y = lnLeafSteps W T 154 a i) ∨
      (∃ k f w yv, t = ^func k f w ∧ yv ≤ y ∧ LenVGraph W T n k w k (i + 1) yv ∧
        y = lnFuncSteps W T k f (listSum (termLenVec LAct k w)) i (shiftsV yv) yv) ) := by
  unfold LenTGraph LenVGraph LenTPacked
  rw [LenT.construction.case]
  exact LenT.phi_term_iff W T _ n t i y

lemma LenVGraph.case_iff {W T n k v m i y : V} :
    LenVGraph W T n k v m i y ↔
    ( (m = 0 ∧ y = lnNilSteps W) ∨
      (∃ m' yt yv, m = m' + 1 ∧ yt ≤ y ∧ yv ≤ y ∧ LenTGraph W T n (nthFromEnd v m') (i + 1) yt ∧
        LenVGraph W T n k v m' (i + 1 + descCountT W n (nthFromEnd v m') + shiftsV yt) yv ∧
        y = lnAdjSteps W T n m' (descCountT W n (nthFromEnd v m')) (termLen LAct (nthFromEnd v m'))
          (listSum (termLenVec LAct m' (takeLast v m'))) i (shiftsV yt) (shiftsV yv) yt yv) ) := by
  unfold LenTGraph LenVGraph LenTPacked
  rw [LenT.construction.case]
  exact LenT.phi_vec_iff W T _ n k v m i y

section lenInversion

attribute [local simp] qqBvar qqFvar qqFunc

lemma LenTGraph.bvar_iff {W T n z i y : V} : LenTGraph W T n (^#z) i y ↔ y = lnLeafSteps W T 153 z i := by
  rw [LenTGraph.case_iff]; simp
lemma LenTGraph.fvar_iff {W T n a i y : V} : LenTGraph W T n (^&a) i y ↔ y = lnLeafSteps W T 154 a i := by
  rw [LenTGraph.case_iff]; simp
lemma LenTGraph.func_iff {W T n k f w i y : V} :
    LenTGraph W T n (^func k f w) i y ↔
    ∃ yv, yv ≤ y ∧ LenVGraph W T n k w k (i + 1) yv ∧ y = lnFuncSteps W T k f (listSum (termLenVec LAct k w)) i (shiftsV yv) yv := by
  rw [LenTGraph.case_iff]; simp
lemma LenVGraph.zero_iff {W T n k v i y : V} : LenVGraph W T n k v 0 i y ↔ y = lnNilSteps W := by
  rw [LenVGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨m', _, _, h, _⟩)
    · rfl
    · exact absurd h.symm (succ_ne_zero' m')
  · intro h; exact Or.inl ⟨rfl, h⟩
lemma LenVGraph.succ_iff {W T n k v m i y : V} :
    LenVGraph W T n k v (m + 1) i y ↔
    ∃ yt yv, yt ≤ y ∧ yv ≤ y ∧ LenTGraph W T n (nthFromEnd v m) (i + 1) yt ∧
      LenVGraph W T n k v m (i + 1 + descCountT W n (nthFromEnd v m) + shiftsV yt) yv ∧
      y = lnAdjSteps W T n m (descCountT W n (nthFromEnd v m)) (termLen LAct (nthFromEnd v m))
        (listSum (termLenVec LAct m (takeLast v m))) i (shiftsV yt) (shiftsV yv) yt yv := by
  rw [LenVGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨m', yt, yv, h, hyt, hyv, h₁, h₂, rfl⟩)
    · exact absurd h (succ_ne_zero' m)
    · obtain rfl : m = m' := add_right_cancel h
      exact ⟨yt, yv, hyt, hyv, h₁, h₂, rfl⟩
  · rintro ⟨yt, yv, hyt, hyv, h₁, h₂, rfl⟩
    exact Or.inr ⟨m, yt, yv, rfl, hyt, hyv, h₁, h₂, rfl⟩

end lenInversion

lemma le_lnFuncSteps (W T k f σ i sv yv : V) : yv ≤ lnFuncSteps W T k f σ i sv yv := le_appendV_left _ _
lemma le_lnAdjSteps_left (W T n m ct lt σ' i st sv yt yv : V) : yt ≤ lnAdjSteps W T n m ct lt σ' i st sv yt yv :=
  le_appendV_left _ _
lemma le_lnAdjSteps_right (W T n m ct lt σ' i st sv yt yv : V) : yv ≤ lnAdjSteps W T n m ct lt σ' i st sv yt yv :=
  le_trans (le_appendV_left _ _) (le_appendV_right _ _)

/-! ### 5.3 Structure of the term/vector lists: tags, `NoDrop'`, shifts, lengths -/

section lenTStruct

lemma noDrop'_tag0 {s : V} (h : sTag s = 0) :
    sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7 := Or.inl h
lemma noDrop'_tag2 {s : V} (h : sTag s = 2) :
    sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7 := Or.inr (Or.inr (Or.inl h))
lemma noDrop'_tag7 {s : V} (h : sTag s = 7) :
    sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

lemma shiftsV_cons_tag0 {s : V} (h : sTag s = 0) (S : V) : shiftsV (s ∷ S) = shiftsV S := by
  rw [shiftsV_cons, if_neg (by rw [h]; simp), zero_add]
lemma shiftsV_cons_tag2 {s : V} (h : sTag s = 2) (S : V) : shiftsV (s ∷ S) = 1 + shiftsV S := by
  rw [shiftsV_cons, if_pos (Or.inl h)]
lemma shiftsV_cons_sLemma (A d S : V) : shiftsV (sLemma A d ∷ S) = shiftsV S := by
  rw [shiftsV_cons, if_neg (by rw [sTag_sLemma]; norm_num), zero_add]
lemma shiftsV_single_tag0 {s : V} (h : sTag s = 0) : shiftsV (?[s] : V) = 0 := by
  rw [shiftsV_single, if_neg (by rw [h]; simp)]

/-- Every step shifts at most once. -/
lemma shiftsAux_le (S : V) : ∀ j, shiftsAux S j ≤ j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ j ih =>
    rw [shiftsAux_succ]
    split_ifs
    · exact add_le_add ih (le_refl (1 : V))
    · exact le_trans ih le_self_add
lemma shiftsV_le_len (S : V) : shiftsV S ≤ len S := shiftsAux_le S (len S)

/-- The walk's `adjoinTotal` (row 17) read from the certification pieces: an intro step. -/
lemma ctag_cert17 {W : V} (hWp : W = certPieces) (ev : V) : sTag (mkStep W (17 : V) ev) = 2 := by
  subst hWp
  rw [show (17 : V) = ((17 : ℕ) : V) by simp, mkStep_certPieces_lt 17 (by decide)]
  exact tag_adjoinTotal rfl ev
lemma ctag_lnLeafRow {W : V} (hWp : W = certPieces) {c : V} (hc : c = 153 ∨ c = 154) (ev : V) :
    sTag (mkStep W c ev) = 0 := by
  rcases hc with rfl | rfl
  · exact ctag_termLenBvar hWp ev
  · exact ctag_termLenFvar hWp ev

lemma lnLeafSteps_struct {W : V} (hWp : W = certPieces) {c : V} (hc : c = 153 ∨ c = 154) (T z i : V) :
    NoDrop' (lnLeafSteps W T c z i) ∧ shiftsV (lnLeafSteps W T c z i) = 1 := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_cons (noDrop'_tag2 (ctag_termLenTotal hWp _)) (noDrop'_cons (noDrop'_tag0 (ctag_lnLeafRow hWp hc _))
      (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _)) (noDrop'_cons (noDrop'_tag0 (ctag_eqTrans hWp _))
      (noDrop'_single (noDrop'_tag0 (ctag_congTLenNum hWp _))))))
  · rw [lnLeafSteps, shiftsV_cons_tag2 (ctag_termLenTotal hWp _), shiftsV_cons_tag0 (ctag_lnLeafRow hWp hc _),
      shiftsV_cons_sLemma, shiftsV_cons_tag0 (ctag_eqTrans hWp _), shiftsV_single_tag0 (ctag_congTLenNum hWp _), add_zero]
lemma len_lnLeafSteps (W T c z i : V) : len (lnLeafSteps W T c z i) = 5 := by
  rw [lnLeafSteps, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_nil]; norm_num

lemma lnFuncSteps_struct {W : V} (hWp : W = certPieces) (T k f σ i sv yv : V) (hv : NoDrop' yv) :
    NoDrop' (lnFuncSteps W T k f σ i sv yv) ∧ shiftsV (lnFuncSteps W T k f σ i sv yv) = shiftsV yv + 1 := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_appendV hv (noDrop'_cons (noDrop'_tag0 (ctag_certFuncRow hWp _ _ _))
      (noDrop'_cons (noDrop'_tag2 (ctag_termLenTotal hWp _)) (noDrop'_cons (noDrop'_tag0 (ctag_termLenFuncCert hWp _))
      (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _)) (noDrop'_cons (noDrop'_tag0 (ctag_eqTrans hWp _))
      (noDrop'_single (noDrop'_tag0 (ctag_congTLenNum hWp _))))))))
  · rw [lnFuncSteps, shiftsV_appendV, shiftsV_cons_tag0 (ctag_certFuncRow hWp _ _ _), shiftsV_cons_tag2 (ctag_termLenTotal hWp _),
      shiftsV_cons_tag0 (ctag_termLenFuncCert hWp _), shiftsV_cons_sLemma, shiftsV_cons_tag0 (ctag_eqTrans hWp _),
      shiftsV_single_tag0 (ctag_congTLenNum hWp _), add_zero]
lemma len_lnFuncSteps (W T k f σ i sv yv : V) : len (lnFuncSteps W T k f σ i sv yv) = len yv + 6 := by
  rw [lnFuncSteps, len_appendV, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_nil]; ring

lemma lnNilSteps_struct {W : V} (hWp : W = certPieces) : NoDrop' (lnNilSteps W) ∧ shiftsV (lnNilSteps W) = 0 := by
  refine ⟨noDrop'_cons (noDrop'_tag0 (ctag_termLenVecNil hWp _)) (noDrop'_single (noDrop'_tag0 (ctag_listSumNil hWp _))), ?_⟩
  rw [lnNilSteps, shiftsV_cons_tag0 (ctag_termLenVecNil hWp _), shiftsV_single_tag0 (ctag_listSumNil hWp _)]
lemma len_lnNilSteps (W : V) : len (lnNilSteps W) = 2 := by
  rw [lnNilSteps, len_adjoin, len_adjoin, len_nil]; norm_num

lemma lnAdjSteps_struct {W : V} (hWp : W = certPieces) (T n m ct lt σ' i st sv yt yv : V) (ht : NoDrop' yt) (hv : NoDrop' yv) :
    NoDrop' (lnAdjSteps W T n m ct lt σ' i st sv yt yv) ∧
    shiftsV (lnAdjSteps W T n m ct lt σ' i st sv yt yv) = shiftsV yt + (shiftsV yv + 1) := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_appendV ht (noDrop'_appendV hv (noDrop'_cons (noDrop'_tag2 (ctag_cert17 hWp _))
      (noDrop'_cons (noDrop'_tag0 (ctag_cert38 hWp _)) (noDrop'_cons (noDrop'_tag0 (ctag_cert39 hWp _))
      (noDrop'_cons (noDrop'_tag0 (ctag_termLenVecAdj hWp _)) (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _))
      (noDrop'_single (noDrop'_tag0 (ctag_listSumAdjI hWp _)))))))))
  · rw [lnAdjSteps, shiftsV_appendV, shiftsV_appendV, shiftsV_cons_tag2 (ctag_cert17 hWp _), shiftsV_cons_tag0 (ctag_cert38 hWp _),
      shiftsV_cons_tag0 (ctag_cert39 hWp _), shiftsV_cons_tag0 (ctag_termLenVecAdj hWp _), shiftsV_cons_sLemma,
      shiftsV_single_tag0 (ctag_listSumAdjI hWp _), add_zero]
lemma len_lnAdjSteps (W T n m ct lt σ' i st sv yt yv : V) :
    len (lnAdjSteps W T n m ct lt σ' i st sv yt yv) = len yt + (len yv + 6) := by
  rw [lnAdjSteps, len_appendV, len_appendV, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_nil]; ring

set_option maxHeartbeats 2000000 in
/-- **Length bound, `W`-free** (the existence proof needs it for every `W`): `len y + 6 ≤ 14|t|`; at the vector
level `len z ≤ 14·Σ + 2` over the last `m` entries. -/
lemma lenTGraph_len (W T n : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i y : V, LenTGraph W T n t i y → len y + 6 ≤ 14 * termLen LAct t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · simp only [LenTGraph, LenVGraph]; definability
  · intro z _ i y hy
    rw [LenTGraph.bvar_iff.mp hy, len_lnLeafSteps, termLen_bvar]
    calc (5 : V) + 6 = 11 := by norm_num
      _ ≤ 14 * 1 := by norm_num
      _ ≤ 14 * (z + 1) := mul_le_mul_of_nonneg_left le_add_self zero_le
  · intro a i y hy
    rw [LenTGraph.fvar_iff.mp hy, len_lnLeafSteps, termLen_fvar]
    calc (5 : V) + 6 = 11 := by norm_num
      _ ≤ 14 * 1 := by norm_num
      _ ≤ 14 * (a + 1) := mul_le_mul_of_nonneg_left le_add_self zero_le
  · intro k f v hkf hv ih i y hy
    have key : ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i z : V, LenVGraph W T n k v m i z →
        len z ≤ 14 * listSum (termLenVec LAct m (takeLast v m)) + 2 := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => simp only [LenTGraph, LenVGraph]; definability
      | zero =>
        intro _
        refine ⟨by simp, ?_⟩
        intro i z hz
        rw [LenVGraph.zero_iff.mp hz, len_lnNilSteps]
        exact le_add_self
      | succ m ihm =>
        intro hm
        have hvlen : len v = k := hv.lh
        have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
        obtain ⟨hU, hrest⟩ := ihm (le_trans le_self_add hm)
        have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
          rw [takeLast_succ_of_lt hjk, hvlen]
        refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
        intro i z hz
        obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        rw [hnth'] at hyt
        have hlT := ih _ hlt (i + 1) yt hyt
        have hlV := hrest _ yv hyv
        rw [len_lnAdjSteps, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
        calc len yt + (len yv + 6) = (len yt + 6) + len yv := by ring
          _ ≤ 14 * termLen LAct v.[k - (m + 1)] + (14 * listSum (termLenVec LAct m (takeLast v m)) + 2) := add_le_add hlT hlV
          _ = 14 * termLen LAct v.[k - (m + 1)] + 14 * listSum (termLenVec LAct m (takeLast v m)) + 2 := by ring
    obtain ⟨yv, _, hyv, rfl⟩ := LenTGraph.func_iff.mp hy
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hlV := (key k le_rfl).2 (i + 1) yv hyv
    rw [htl] at hlV
    rw [len_lnFuncSteps, termLen_func hkf hv.isUTerm]
    calc len yv + 6 + 6 = len yv + 12 := by ring
      _ ≤ (14 * listSum (termLenVec LAct k v) + 2) + 12 := add_le_add hlV (le_refl (12 : V))
      _ = 14 * (listSum (termLenVec LAct k v) + 1) := by ring

set_option maxHeartbeats 2000000 in
lemma lenVGraph_len (W T n : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i z : V, LenVGraph W T n k v m i z →
      len z ≤ 14 * listSum (termLenVec LAct m (takeLast v m)) + 2 := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => simp only [LenTGraph, LenVGraph]; definability
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i z hz
    rw [LenVGraph.zero_iff.mp hz, len_lnNilSteps]
    exact le_add_self
  | succ m ihm =>
    intro hm
    have hvlen : len v = k := hv.lh
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    obtain ⟨hU, hrest⟩ := ihm (le_trans le_self_add hm)
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    intro i z hz
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    rw [hnth'] at hyt
    have hlT := lenTGraph_len W T n _ ht (i + 1) yt hyt
    have hlV := hrest _ yv hyv
    rw [len_lnAdjSteps, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
    calc len yt + (len yv + 6) = (len yt + 6) + len yv := by ring
      _ ≤ 14 * termLen LAct v.[k - (m + 1)] + (14 * listSum (termLenVec LAct m (takeLast v m)) + 2) := add_le_add hlT hlV
      _ = 14 * termLen LAct v.[k - (m + 1)] + 14 * listSum (termLenVec LAct m (takeLast v m)) + 2 := by ring

set_option maxHeartbeats 2000000 in
/-- **`NoDrop'` and the shift count** (over the certification pieces): `shiftsV y + 1 ≤ 2|t|`; at the vector
level `shiftsV z ≤ 2·Σ`. -/
lemma lenTGraph_noDrop_shifts {W : V} (hWp : W = certPieces) (T n : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i y : V, LenTGraph W T n t i y → NoDrop' y ∧ shiftsV y + 1 ≤ 2 * termLen LAct t := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · simp only [LenTGraph, LenVGraph]; definability
  · intro z _ i y hy
    rw [LenTGraph.bvar_iff.mp hy, termLen_bvar]
    obtain ⟨h1, h2⟩ := lnLeafSteps_struct hWp (Or.inl rfl) T z i
    refine ⟨h1, ?_⟩
    rw [h2]
    calc (1 : V) + 1 = 2 * 1 := by norm_num
      _ ≤ 2 * (z + 1) := mul_le_mul_of_nonneg_left le_add_self zero_le
  · intro a i y hy
    rw [LenTGraph.fvar_iff.mp hy, termLen_fvar]
    obtain ⟨h1, h2⟩ := lnLeafSteps_struct hWp (Or.inr rfl) T a i
    refine ⟨h1, ?_⟩
    rw [h2]
    calc (1 : V) + 1 = 2 * 1 := by norm_num
      _ ≤ 2 * (a + 1) := mul_le_mul_of_nonneg_left le_add_self zero_le
  · intro k f v hkf hv ih i y hy
    have key : ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i z : V, LenVGraph W T n k v m i z →
        NoDrop' z ∧ shiftsV z ≤ 2 * listSum (termLenVec LAct m (takeLast v m)) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => simp only [LenTGraph, LenVGraph]; definability
      | zero =>
        intro _
        refine ⟨by simp, ?_⟩
        intro i z hz
        rw [LenVGraph.zero_iff.mp hz]
        obtain ⟨h1, h2⟩ := lnNilSteps_struct hWp
        exact ⟨h1, by rw [h2]; exact zero_le⟩
      | succ m ihm =>
        intro hm
        have hvlen : len v = k := hv.lh
        have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
        obtain ⟨hU, hrest⟩ := ihm (le_trans le_self_add hm)
        have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
          rw [takeLast_succ_of_lt hjk, hvlen]
        refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
        intro i z hz
        obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        rw [hnth'] at hyt
        obtain ⟨hnT, hsT⟩ := ih _ hlt (i + 1) yt hyt
        obtain ⟨hnV, hsV⟩ := hrest _ yv hyv
        obtain ⟨h1, h2⟩ := lnAdjSteps_struct hWp T n m _ _ _ i _ _ yt yv hnT hnV
        refine ⟨h1, ?_⟩
        rw [h2, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
        calc shiftsV yt + (shiftsV yv + 1) = (shiftsV yt + 1) + shiftsV yv := by ring
          _ ≤ 2 * termLen LAct v.[k - (m + 1)] + 2 * listSum (termLenVec LAct m (takeLast v m)) := add_le_add hsT hsV
    obtain ⟨yv, _, hyv, rfl⟩ := LenTGraph.func_iff.mp hy
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨hnV, hsV⟩ := (key k le_rfl).2 (i + 1) yv hyv
    rw [htl] at hsV
    obtain ⟨h1, h2⟩ := lnFuncSteps_struct hWp T k f _ i _ yv hnV
    refine ⟨h1, ?_⟩
    rw [h2, termLen_func hkf hv.isUTerm]
    calc shiftsV yv + 1 + 1 = shiftsV yv + 2 := by ring
      _ ≤ 2 * listSum (termLenVec LAct k v) + 2 := add_le_add hsV (le_refl (2 : V))
      _ = 2 * (listSum (termLenVec LAct k v) + 1) := by ring

set_option maxHeartbeats 2000000 in
lemma lenVGraph_noDrop_shifts {W : V} (hWp : W = certPieces) (T n : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, ∀ i z : V, LenVGraph W T n k v m i z →
      NoDrop' z ∧ shiftsV z ≤ 2 * listSum (termLenVec LAct m (takeLast v m)) := by
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => simp only [LenTGraph, LenVGraph]; definability
  | zero =>
    intro _ i z hz
    rw [LenVGraph.zero_iff.mp hz]
    obtain ⟨h1, h2⟩ := lnNilSteps_struct hWp
    exact ⟨h1, by rw [h2]; exact zero_le⟩
  | succ m ihm =>
    intro hm i z hz
    have hvlen : len v = k := hv.lh
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    have hU : IsUTermVec LAct m (takeLast v m) := (lenVGraph_len W T n hv m (le_trans le_self_add hm)).1
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    rw [hnth'] at hyt
    obtain ⟨hnT, hsT⟩ := lenTGraph_noDrop_shifts hWp T n _ ht (i + 1) yt hyt
    obtain ⟨hnV, hsV⟩ := ihm (le_trans le_self_add hm) _ yv hyv
    obtain ⟨h1, h2⟩ := lnAdjSteps_struct hWp T n m _ _ _ i _ _ yt yv hnT hnV
    refine ⟨h1, ?_⟩
    rw [h2, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
    calc shiftsV yt + (shiftsV yv + 1) = (shiftsV yt + 1) + shiftsV yv := by ring
      _ ≤ 2 * termLen LAct v.[k - (m + 1)] + 2 * listSum (termLenVec LAct m (takeLast v m)) := add_le_add hsT hsV

end lenTStruct

/-! ### 5.4 Existence, uniqueness, and the functions `lenT`/`lenV` -/

section lenTFun

set_option maxHeartbeats 1000000 in
/-- **Existence**, offsets bounded by `B` (the motive must be Σ₁); `W`-free — the sub-call offsets involve
`shiftsV`, bounded through `shiftsV_le_len` and `lenTGraph_len`. -/
lemma lenTGraph_exists_bounded (W T n B : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i ≤ B, i + descCountT W n t + 16 * termLen LAct t ≤ B → ∃ y, LenTGraph W T n t i y := by
  refine IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_
  · simp only [LenTGraph, LenVGraph]; definability
  · intro z _ i _ _; exact ⟨_, LenTGraph.bvar_iff.mpr rfl⟩
  · intro a i _ _; exact ⟨_, LenTGraph.fvar_iff.mpr rfl⟩
  · intro k f v hkf hv ih i hi hiB
    rw [descCountT_func W n hkf hv.isUTerm, termLen_func hkf hv.isUTerm] at hiB
    have key : ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i ≤ B,
        i + π₁ (descVecAux W n (descTVec W n k v) m) + 16 * listSum (termLenVec LAct m (takeLast v m)) + 1 ≤ B →
        ∃ yv, LenVGraph W T n k v m i yv := by
      intro m
      induction m using ISigma1.sigma1_succ_induction with
      | hP => simp only [LenTGraph, LenVGraph]; definability
      | zero => intro _; exact ⟨by simp, fun i _ _ ↦ ⟨_, LenVGraph.zero_iff.mpr rfl⟩⟩
      | succ m ihm =>
        intro hm
        have hvlen : len v = k := hv.lh
        have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
        obtain ⟨hU, ihm'⟩ := ihm (le_trans le_self_add hm)
        have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
          rw [takeLast_succ_of_lt hjk, hvlen]
        refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
        intro i hi hiB
        have hnth : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
          rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
            nth_descTVec W n hv.isUTerm hlt]
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        have hC : π₁ (descVecAux W n (descTVec W n k v) (m + 1)) =
            π₁ (descVecAux W n (descTVec W n k v) m) + descCountT W n v.[k - (m + 1)] + 1 := by
          rw [descVecAux_succ, hnth, adjNode, pi₁_pair]; rfl
        rw [hC, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hiB
        set ct := descCountT W n v.[k - (m + 1)] with hct
        set cv := π₁ (descVecAux W n (descTVec W n k v) m) with hcv
        set lt := termLen LAct v.[k - (m + 1)] with hlt'
        set σ' := listSum (termLenVec LAct m (takeLast v m)) with hσ'
        -- hiB : i + (cv + ct + 1) + 16 * (lt + σ') + 1 ≤ B
        have hiT : i + 1 + ct + 16 * lt ≤ B :=
          le_trans (le_of_eq (show i + 1 + ct + 16 * lt = i + (0 + ct + 1) + 16 * (lt + 0) + 0 by ring))
            (le_trans (add_le_add (add_le_add (add_le_add (le_refl i) (add_le_add (add_le_add zero_le (le_refl ct)) (le_refl 1)))
              (mul_le_mul_of_nonneg_left (add_le_add (le_refl lt) zero_le) zero_le)) zero_le) hiB)
        obtain ⟨yt, hyt⟩ := ih _ hlt (i + 1) (le_trans (le_trans le_self_add le_self_add) hiT) hiT
        have hst : shiftsV yt ≤ 14 * lt := by
          have h1 := shiftsV_le_len yt
          have h2 := lenTGraph_len W T n _ ht (i + 1) yt hyt
          exact le_trans h1 (le_trans le_self_add h2)
        have hiV : i + 1 + ct + shiftsV yt + cv + 16 * σ' + 1 ≤ B := by
          calc i + 1 + ct + shiftsV yt + cv + 16 * σ' + 1 ≤ i + 1 + ct + 14 * lt + cv + 16 * σ' + 1 := by
                gcongr
            _ ≤ i + 1 + ct + 16 * lt + cv + 16 * σ' + 1 := by gcongr; norm_num
            _ = i + (cv + ct + 1) + 16 * (lt + σ') + 1 := by ring
            _ ≤ B := hiB
        obtain ⟨yv, hyv⟩ := ihm' (i + 1 + ct + shiftsV yt) (le_trans (le_trans le_self_add le_self_add) (le_trans le_self_add hiV)) hiV
        refine ⟨_, LenVGraph.succ_iff.mpr ⟨yt, yv, le_lnAdjSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
          le_lnAdjSteps_right _ _ _ _ _ _ _ _ _ _ _ _, ?_, ?_, rfl⟩⟩
        · rw [hnth']; exact hyt
        · rw [hnth']; exact hyv
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hiV : i + 1 + π₁ (descVecAux W n (descTVec W n k v) k) + 16 * listSum (termLenVec LAct k (takeLast v k)) + 1 ≤ B := by
      rw [htl]
      calc i + 1 + π₁ (descVecAux W n (descTVec W n k v) k) + 16 * listSum (termLenVec LAct k v) + 1
          = i + (π₁ (descVecAux W n (descTVec W n k v) k) + 1) + 16 * listSum (termLenVec LAct k v) + 1 := by ring
        _ ≤ i + (π₁ (descVecAux W n (descTVec W n k v) k) + 1) + 16 * listSum (termLenVec LAct k v) + 16 := by gcongr; norm_num
        _ = i + (π₁ (descVecAux W n (descTVec W n k v) k) + 1) + 16 * (listSum (termLenVec LAct k v) + 1) := by ring
        _ ≤ B := hiB
    obtain ⟨yv, hyv⟩ := (key k le_rfl).2 (i + 1) (le_trans (le_trans le_self_add le_self_add) (le_trans le_self_add hiV)) hiV
    exact ⟨_, LenTGraph.func_iff.mpr ⟨yv, le_lnFuncSteps _ _ _ _ _ _ _ _, hyv, rfl⟩⟩

lemma lenTGraph_exists (W T n : V) {t : V} (ht : IsSemiterm LAct n t) (i : V) : ∃ y, LenTGraph W T n t i y :=
  lenTGraph_exists_bounded W T n (i + descCountT W n t + 16 * termLen LAct t) t ht i
    (le_trans le_self_add le_self_add) le_rfl

set_option maxHeartbeats 2000000 in
lemma lenVGraph_exists_bounded (W T n B : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i ≤ B,
      i + π₁ (descVecAux W n (descTVec W n k v) m) + 16 * listSum (termLenVec LAct m (takeLast v m)) + 1 ≤ B →
      ∃ y, LenVGraph W T n k v m i y := by
  have hvlen : len v = k := hv.lh
  intro m
  induction m using ISigma1.sigma1_succ_induction with
  | hP => simp only [LenTGraph, LenVGraph]; definability
  | zero => intro _; exact ⟨by simp, fun i _ _ ↦ ⟨_, LenVGraph.zero_iff.mpr rfl⟩⟩
  | succ m ihm =>
    intro hm
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    obtain ⟨hU, ihm'⟩ := ihm (le_trans le_self_add hm)
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    intro i hi hiB
    have hnth : nthFromEnd (descTVec W n k v) m = descT W n v.[k - (m + 1)] := by
      rw [nthFromEnd_eq (a := k - (m + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hm]),
        nth_descTVec W n hv.isUTerm hlt]
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    have hC : π₁ (descVecAux W n (descTVec W n k v) (m + 1)) =
        π₁ (descVecAux W n (descTVec W n k v) m) + descCountT W n v.[k - (m + 1)] + 1 := by
      rw [descVecAux_succ, hnth, adjNode, pi₁_pair]; rfl
    rw [hC, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hiB
    set ct := descCountT W n v.[k - (m + 1)] with hct
    set cv := π₁ (descVecAux W n (descTVec W n k v) m) with hcv
    set lt := termLen LAct v.[k - (m + 1)] with hlt'
    set σ' := listSum (termLenVec LAct m (takeLast v m)) with hσ'
    obtain ⟨yt, hyt⟩ := lenTGraph_exists W T n ht (i + 1)
    have hst : shiftsV yt ≤ 14 * lt := by
      have h1 := shiftsV_le_len yt
      have h2 := lenTGraph_len W T n _ ht (i + 1) yt hyt
      exact le_trans h1 (le_trans le_self_add h2)
    have hiV : i + 1 + ct + shiftsV yt + cv + 16 * σ' + 1 ≤ B := by
      calc i + 1 + ct + shiftsV yt + cv + 16 * σ' + 1 ≤ i + 1 + ct + 14 * lt + cv + 16 * σ' + 1 := by
            gcongr
        _ ≤ i + 1 + ct + 16 * lt + cv + 16 * σ' + 1 := by gcongr; norm_num
        _ = i + (cv + ct + 1) + 16 * (lt + σ') + 1 := by ring
        _ ≤ B := hiB
    obtain ⟨yv, hyv⟩ := ihm' (i + 1 + ct + shiftsV yt) (le_trans (le_trans le_self_add le_self_add) (le_trans le_self_add hiV)) hiV
    refine ⟨_, LenVGraph.succ_iff.mpr ⟨yt, yv, le_lnAdjSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
      le_lnAdjSteps_right _ _ _ _ _ _ _ _ _ _ _ _, ?_, ?_, rfl⟩⟩
    · rw [hnth']; exact hyt
    · rw [hnth']; exact hyv

lemma lenVGraph_exists (W T n : V) {k v : V} (hv : IsSemitermVec LAct k n v) {m : V} (hm : m ≤ k) (i : V) :
    ∃ y, LenVGraph W T n k v m i y :=
  (lenVGraph_exists_bounded W T n
    (i + π₁ (descVecAux W n (descTVec W n k v) m) + 16 * listSum (termLenVec LAct m (takeLast v m)) + 1) hv m hm).2 i
    (le_trans (le_trans le_self_add le_self_add) le_self_add) le_rfl

set_option maxHeartbeats 2000000 in
/-- **Uniqueness** (Π₁ motive). -/
lemma lenTGraph_unique (W T n : V) : ∀ t, IsSemiterm LAct n t →
    ∀ i y₁ y₂, LenTGraph W T n t i y₁ → LenTGraph W T n t i y₂ → y₁ = y₂ := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · simp only [LenTGraph, LenVGraph]; definability
  · intro z _ i y₁ y₂ h₁ h₂; rw [LenTGraph.bvar_iff] at h₁ h₂; rw [h₁, h₂]
  · intro a i y₁ y₂ h₁ h₂; rw [LenTGraph.fvar_iff] at h₁ h₂; rw [h₁, h₂]
  · intro k f v hkf hv ih i y₁ y₂ h₁ h₂
    have hvlen : len v = k := hv.lh
    have key : ∀ m ≤ k, ∀ i z₁ z₂, LenVGraph W T n k v m i z₁ → LenVGraph W T n k v m i z₂ → z₁ = z₂ := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => simp only [LenTGraph, LenVGraph]; definability
      | zero => intro _ i z₁ z₂ h₁ h₂; rw [LenVGraph.zero_iff] at h₁ h₂; rw [h₁, h₂]
      | succ m ihm =>
        intro hm i z₁ z₂ h₁ h₂
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp h₁
        obtain ⟨yt', yv', _, _, hyt', hyv', rfl⟩ := LenVGraph.succ_iff.mp h₂
        rw [hnth'] at hyt hyt'
        obtain rfl := ih _ hlt (i + 1) yt yt' hyt hyt'
        obtain rfl := ihm (le_trans le_self_add hm) _ yv yv' hyv hyv'
        rfl
    obtain ⟨yv, _, hyv, rfl⟩ := LenTGraph.func_iff.mp h₁
    obtain ⟨yv', _, hyv', rfl⟩ := LenTGraph.func_iff.mp h₂
    rw [key k le_rfl (i + 1) yv yv' hyv hyv']

set_option maxHeartbeats 2000000 in
lemma lenVGraph_unique (W T n : V) {k v : V} (hv : IsSemitermVec LAct k n v) :
    ∀ m ≤ k, ∀ i z₁ z₂, LenVGraph W T n k v m i z₁ → LenVGraph W T n k v m i z₂ → z₁ = z₂ := by
  have hvlen : len v = k := hv.lh
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => simp only [LenTGraph, LenVGraph]; definability
  | zero => intro _ i z₁ z₂ h₁ h₂; rw [LenVGraph.zero_iff] at h₁ h₂; rw [h₁, h₂]
  | succ m ihm =>
    intro hm i z₁ z₂ h₁ h₂
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp h₁
    obtain ⟨yt', yv', _, _, hyt', hyv', rfl⟩ := LenVGraph.succ_iff.mp h₂
    rw [hnth'] at hyt hyt'
    obtain rfl := lenTGraph_unique W T n _ ht (i + 1) yt yt' hyt hyt'
    obtain rfl := ihm (le_trans le_self_add hm) _ yv yv' hyv hyv'
    rfl

lemma lenTGraph_existsUnique_total (W T n t i : V) :
    ∃! y, (IsSemiterm LAct n t → LenTGraph W T n t i y) ∧ (¬IsSemiterm LAct n t → y = 0) := by
  by_cases h : IsSemiterm LAct n t
  · obtain ⟨y, hy⟩ := lenTGraph_exists W T n h i
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ lenTGraph_unique W T n t h i y' y hy' hy)
  · simp [h]

/-- **The term-level length producer as a function** (`0` off semiterms). -/
noncomputable def lenT (W T n t i : V) : V := Classical.choose! (lenTGraph_existsUnique_total W T n t i)

theorem lenT_graph {W T n t i : V} (h : IsSemiterm LAct n t) : LenTGraph W T n t i (lenT W T n t i) :=
  (Classical.choose!_spec (lenTGraph_existsUnique_total W T n t i)).1 h
theorem lenT_of_not {W T n t i : V} (h : ¬IsSemiterm LAct n t) : lenT W T n t i = 0 :=
  (Classical.choose!_spec (lenTGraph_existsUnique_total W T n t i)).2 h
lemma lenT_eq_of_graph {W T n t i y : V} (h : IsSemiterm LAct n t) (hy : LenTGraph W T n t i y) : lenT W T n t i = y :=
  lenTGraph_unique W T n t h i _ _ (lenT_graph h) hy

noncomputable def lenTDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W T n t i. (!(isSemiterm LAct).pi n t → !lenTGraphDef W T n t i y) ∧ (¬!(isSemiterm LAct).sigma n t → y = 0)”

instance lenT_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ lenT (v 0) (v 1) (v 2) (v 3) (v 4)) lenTDef := .mk
  fun v ↦ by
    simp [lenTDef, HierarchySymbol.Semiformula.val_sigma, lenTGraph_defined.iff,
      (IsSemiterm.defined (L := LAct)).proper.iff', (IsSemiterm.defined (L := LAct)).df, lenT,
      Classical.choose!_eq_iff_right]
instance lenT_definable :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ lenT (v 0) (v 1) (v 2) (v 3) (v 4)) lenTDef := lenT_defined

lemma lenVGraph_existsUnique_total (W T n k v m i : V) :
    ∃! y, ((IsSemitermVec LAct k n v ∧ m ≤ k) → LenVGraph W T n k v m i y) ∧
      (¬(IsSemitermVec LAct k n v ∧ m ≤ k) → y = 0) := by
  by_cases h : IsSemitermVec LAct k n v ∧ m ≤ k
  · obtain ⟨y, hy⟩ := lenVGraph_exists W T n h.1 h.2 i
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ lenVGraph_unique W T n h.1 m h.2 i y' y hy' hy)
  · simp [h]

/-- **The vector-level length producer as a function** (`0` off semiterm vectors / oversized `m`). -/
noncomputable def lenV (W T n k v m i : V) : V := Classical.choose! (lenVGraph_existsUnique_total W T n k v m i)

theorem lenV_graph {W T n k v m i : V} (hv : IsSemitermVec LAct k n v) (hm : m ≤ k) :
    LenVGraph W T n k v m i (lenV W T n k v m i) :=
  (Classical.choose!_spec (lenVGraph_existsUnique_total W T n k v m i)).1 ⟨hv, hm⟩
lemma lenV_eq_of_graph {W T n k v m i y : V} (hv : IsSemitermVec LAct k n v) (hm : m ≤ k)
    (hy : LenVGraph W T n k v m i y) : lenV W T n k v m i = y :=
  lenVGraph_unique W T n hv m hm i _ _ (lenV_graph hv hm) hy

noncomputable def lenVDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W T n k v m i. ((!(isSemitermVec LAct).pi k n v ∧ m ≤ k) → !lenVGraphDef W T n k v m i y) ∧
    ((!(isSemitermVec LAct).sigma k n v → k < m) → y = 0)”

instance lenV_defined :
    𝚺₁.DefinedFunction (fun w : Fin 7 → V ↦ lenV (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) lenVDef := .mk
  fun w ↦ by
    simp [lenVDef, HierarchySymbol.Semiformula.val_sigma, lenVGraph_defined.iff,
      (IsSemitermVec.defined (L := LAct)).proper.iff', (IsSemitermVec.defined (L := LAct)).df, lenV,
      Classical.choose!_eq_iff_right]
instance lenV_definable :
    𝚺₁.DefinedFunction (fun w : Fin 7 → V ↦ lenV (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) lenVDef := lenV_defined

/-! #### The equations -/

lemma lenT_bvar (W T n z i : V) (hz : IsSemiterm LAct n (^#z)) : lenT W T n (^#z) i = lnLeafSteps W T 153 z i :=
  lenT_eq_of_graph hz (LenTGraph.bvar_iff.mpr rfl)
lemma lenT_fvar (W T n a i : V) : lenT W T n (^&a) i = lnLeafSteps W T 154 a i :=
  lenT_eq_of_graph (by simp) (LenTGraph.fvar_iff.mpr rfl)
lemma lenT_func (W T n : V) {k f v : V} (hkf : LAct.IsFunc k f) (hv : IsSemitermVec LAct k n v) (i : V) :
    lenT W T n (^func k f v) i =
      lnFuncSteps W T k f (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1)) :=
  lenT_eq_of_graph (by simp [hkf, hv]) (LenTGraph.func_iff.mpr ⟨_, le_lnFuncSteps _ _ _ _ _ _ _ _, lenV_graph hv le_rfl, rfl⟩)
lemma lenV_zero (W T n k v i : V) (hv : IsSemitermVec LAct k n v) : lenV W T n k v 0 i = lnNilSteps W :=
  lenV_eq_of_graph hv zero_le (LenVGraph.zero_iff.mpr rfl)
lemma lenV_succ (W T n : V) {k v m : V} (hv : IsSemitermVec LAct k n v) (hm : m + 1 ≤ k) (i : V) :
    lenV W T n k v (m + 1) i =
      lnAdjSteps W T n m (descCountT W n (nthFromEnd v m)) (termLen LAct (nthFromEnd v m))
        (listSum (termLenVec LAct m (takeLast v m))) i
        (shiftsV (lenT W T n (nthFromEnd v m) (i + 1)))
        (shiftsV (lenV W T n k v m (i + 1 + descCountT W n (nthFromEnd v m) + shiftsV (lenT W T n (nthFromEnd v m) (i + 1)))))
        (lenT W T n (nthFromEnd v m) (i + 1))
        (lenV W T n k v m (i + 1 + descCountT W n (nthFromEnd v m) + shiftsV (lenT W T n (nthFromEnd v m) (i + 1)))) := by
  have hvlen : len v = k := hv.lh
  have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
  have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
    nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
  have ht : IsSemiterm LAct n (nthFromEnd v m) := by rw [hnth']; exact hv.nth hlt
  exact lenV_eq_of_graph hv hm (LenVGraph.succ_iff.mpr ⟨_, _, le_lnAdjSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
    le_lnAdjSteps_right _ _ _ _ _ _ _ _ _ _ _ _, lenT_graph ht, lenV_graph hv (le_trans le_self_add hm), rfl⟩)

end lenTFun

/-! ### 5.5 The formula fixpoint `LenF` on `⟪n, r, i, y⟫` (parameters `W`, `T`; atoms call `lenV`) -/

namespace LenF

def Cases (W T : V) (C : Set V) (n r i y : V) : Prop :=
  (∃ k < r, ∃ R < r, ∃ v < r, r = ^rel k R v ∧
    y = lnAtomSteps W T 142 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1))) ∨
  (∃ k < r, ∃ R < r, ∃ v < r, r = ^nrel k R v ∧
    y = lnAtomSteps W T 143 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1))) ∨
  (r = ^⊤ ∧ y = lnConstSteps W 147 i) ∨
  (r = ^⊥ ∧ y = lnConstSteps W 148 i) ∨
  (∃ p < r, ∃ q < r, r = p ^⋏ q ∧ ∃ yq ≤ y, ∃ yp ≤ y,
    ⟪n, q, i + 1, yq⟫ ∈ C ∧ ⟪n, p, i + descCountF W n q + 1 + shiftsV yq, yp⟫ ∈ C ∧
    y = lnBinSteps W T 149 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp) ∨
  (∃ p < r, ∃ q < r, r = p ^⋎ q ∧ ∃ yq ≤ y, ∃ yp ≤ y,
    ⟪n, q, i + 1, yq⟫ ∈ C ∧ ⟪n, p, i + descCountF W n q + 1 + shiftsV yq, yp⟫ ∈ C ∧
    y = lnBinSteps W T 150 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp) ∨
  (∃ p < r, r = ^∀ p ∧ ∃ yb ≤ y, ⟪n + 1, p, i + 1, yb⟫ ∈ C ∧ y = lnQuantSteps W T 151 n (formulaLen LAct p) i (shiftsV yb) yb) ∨
  (∃ p < r, r = ^∃ p ∧ ∃ yb ≤ y, ⟪n + 1, p, i + 1, yb⟫ ∈ C ∧ y = lnQuantSteps W T 152 n (formulaLen LAct p) i (shiftsV yb) yb)

def Phi (W T : V) (C : Set V) (pr : V) : Prop :=
  ∃ n ≤ pr, ∃ q₁ ≤ pr, pr = ⟪n, q₁⟫ ∧ ∃ r ≤ q₁, ∃ q₂ ≤ q₁, q₁ = ⟪r, q₂⟫ ∧
  ∃ i ≤ q₂, ∃ y ≤ q₂, q₂ = ⟪i, y⟫ ∧ Cases W T C n r i y

lemma phi_unpack (W T : V) (C : Set V) (pr : V) :
    Phi W T C pr ↔ ∃ n r i y, pr = ⟪n, r, i, y⟫ ∧ Cases W T C n r i y := by
  constructor
  · rintro ⟨n, _, q₁, _, rfl, r, _, q₂, _, rfl, i, _, y, _, rfl, h⟩
    exact ⟨n, r, i, y, rfl, h⟩
  · rintro ⟨n, r, i, y, rfl, h⟩
    exact ⟨n, le_pair_left _ _, _, le_pair_right _ _, rfl, r, le_pair_left _ _, _, le_pair_right _ _, rfl,
      i, le_pair_left _ _, y, le_pair_right _ _, rfl, h⟩

lemma phi_of_cases {W T : V} {C : Set V} {n r i y : V} (h : Cases W T C n r i y) :
    Phi W T C ⟪n, r, i, y⟫ := (phi_unpack W T C _).mpr ⟨n, r, i, y, rfl, h⟩

lemma cases_of_phi {W T : V} {C : Set V} {n r i y : V} (h : Phi W T C ⟪n, r, i, y⟫) :
    Cases W T C n r i y := by
  obtain ⟨n', r', i', y', e, h⟩ := (phi_unpack W T C _).mp h
  rw [pair_ext_iff, pair_ext_iff, pair_ext_iff] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact h

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C W T.
    ∃ n <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr n q₁ ∧ ∃ r <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ r q₂ ∧
    ∃ i <⁺ q₂, ∃ y <⁺ q₂, !pairDef q₂ i y ∧
    ( (∃ k < r, ∃ R < r, ∃ v < r, !qqRelDef r k R v ∧ ∃ yv, !lenVDef yv W T n k v k (i + 1) ∧
        ∃ M, !(termLenVecGraph LAct) M k v ∧ ∃ σ, !listSumDef σ M ∧ ∃ sv, !shiftsVDef sv yv ∧
        ∃ s, !lnAtomStepsDef s W T 142 k R σ i sv yv ∧ y = s) ∨
      (∃ k < r, ∃ R < r, ∃ v < r, !qqNRelDef r k R v ∧ ∃ yv, !lenVDef yv W T n k v k (i + 1) ∧
        ∃ M, !(termLenVecGraph LAct) M k v ∧ ∃ σ, !listSumDef σ M ∧ ∃ sv, !shiftsVDef sv yv ∧
        ∃ s, !lnAtomStepsDef s W T 143 k R σ i sv yv ∧ y = s) ∨
      (!qqVerumDef r ∧ ∃ s, !lnConstStepsDef s W 147 i ∧ y = s) ∨
      (!qqFalsumDef r ∧ ∃ s, !lnConstStepsDef s W 148 i ∧ y = s) ∨
      (∃ p < r, ∃ q < r, !qqAndDef r p q ∧ ∃ yq <⁺ y, ∃ yp <⁺ y, ∃ cq, !descCountFDef cq W n q ∧
        ∃ sq, !shiftsVDef sq yq ∧ ∃ sp, !shiftsVDef sp yp ∧ ∃ lp, !(formulaLenGraph LAct) lp p ∧ ∃ lq, !(formulaLenGraph LAct) lq q ∧
        ∃ b₃, !pairDef b₃ (i + 1) yq ∧ ∃ b₂, !pairDef b₂ q b₃ ∧ :⟪n, b₂⟫:∈ C ∧
        ∃ a₃, !pairDef a₃ (i + cq + 1 + sq) yp ∧ ∃ a₂, !pairDef a₂ p a₃ ∧ :⟪n, a₂⟫:∈ C ∧
        ∃ s, !lnBinStepsDef s W T 149 n cq lp lq i sq sp yq yp ∧ y = s) ∨
      (∃ p < r, ∃ q < r, !qqOrDef r p q ∧ ∃ yq <⁺ y, ∃ yp <⁺ y, ∃ cq, !descCountFDef cq W n q ∧
        ∃ sq, !shiftsVDef sq yq ∧ ∃ sp, !shiftsVDef sp yp ∧ ∃ lp, !(formulaLenGraph LAct) lp p ∧ ∃ lq, !(formulaLenGraph LAct) lq q ∧
        ∃ b₃, !pairDef b₃ (i + 1) yq ∧ ∃ b₂, !pairDef b₂ q b₃ ∧ :⟪n, b₂⟫:∈ C ∧
        ∃ a₃, !pairDef a₃ (i + cq + 1 + sq) yp ∧ ∃ a₂, !pairDef a₂ p a₃ ∧ :⟪n, a₂⟫:∈ C ∧
        ∃ s, !lnBinStepsDef s W T 150 n cq lp lq i sq sp yq yp ∧ y = s) ∨
      (∃ p < r, !qqAllDef r p ∧ ∃ yb <⁺ y, ∃ sb, !shiftsVDef sb yb ∧ ∃ lp, !(formulaLenGraph LAct) lp p ∧
        ∃ a₃, !pairDef a₃ (i + 1) yb ∧ ∃ a₂, !pairDef a₂ p a₃ ∧ :⟪n + 1, a₂⟫:∈ C ∧
        ∃ s, !lnQuantStepsDef s W T 151 n lp i sb yb ∧ y = s) ∨
      (∃ p < r, !qqExsDef r p ∧ ∃ yb <⁺ y, ∃ sb, !shiftsVDef sb yb ∧ ∃ lp, !(formulaLenGraph LAct) lp p ∧
        ∃ a₃, !pairDef a₃ (i + 1) yb ∧ ∃ a₂, !pairDef a₂ p a₃ ∧ :⟪n + 1, a₂⟫:∈ C ∧
        ∃ s, !lnQuantStepsDef s W T 152 n lp i sb yb ∧ y = s) )”)
  (.mkPi “pr C W T.
    ∃ n <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr n q₁ ∧ ∃ r <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ r q₂ ∧
    ∃ i <⁺ q₂, ∃ y <⁺ q₂, !pairDef q₂ i y ∧
    ( (∃ k < r, ∃ R < r, ∃ v < r, !qqRelDef r k R v ∧ ∀ yv, !lenVDef yv W T n k v k (i + 1) →
        ∀ M, !(termLenVecGraph LAct) M k v → ∀ σ, !listSumDef σ M → ∀ sv, !shiftsVDef sv yv →
        ∀ s, !lnAtomStepsDef s W T 142 k R σ i sv yv → y = s) ∨
      (∃ k < r, ∃ R < r, ∃ v < r, !qqNRelDef r k R v ∧ ∀ yv, !lenVDef yv W T n k v k (i + 1) →
        ∀ M, !(termLenVecGraph LAct) M k v → ∀ σ, !listSumDef σ M → ∀ sv, !shiftsVDef sv yv →
        ∀ s, !lnAtomStepsDef s W T 143 k R σ i sv yv → y = s) ∨
      (!qqVerumDef r ∧ ∀ s, !lnConstStepsDef s W 147 i → y = s) ∨
      (!qqFalsumDef r ∧ ∀ s, !lnConstStepsDef s W 148 i → y = s) ∨
      (∃ p < r, ∃ q < r, !qqAndDef r p q ∧ ∃ yq <⁺ y, ∃ yp <⁺ y, ∀ cq, !descCountFDef cq W n q →
        ∀ sq, !shiftsVDef sq yq → ∀ sp, !shiftsVDef sp yp → ∀ lp, !(formulaLenGraph LAct) lp p → ∀ lq, !(formulaLenGraph LAct) lq q →
        ∀ b₃, !pairDef b₃ (i + 1) yq → ∀ b₂, !pairDef b₂ q b₃ → :⟪n, b₂⟫:∈ C ∧
        ∀ a₃, !pairDef a₃ (i + cq + 1 + sq) yp → ∀ a₂, !pairDef a₂ p a₃ → :⟪n, a₂⟫:∈ C ∧
        ∀ s, !lnBinStepsDef s W T 149 n cq lp lq i sq sp yq yp → y = s) ∨
      (∃ p < r, ∃ q < r, !qqOrDef r p q ∧ ∃ yq <⁺ y, ∃ yp <⁺ y, ∀ cq, !descCountFDef cq W n q →
        ∀ sq, !shiftsVDef sq yq → ∀ sp, !shiftsVDef sp yp → ∀ lp, !(formulaLenGraph LAct) lp p → ∀ lq, !(formulaLenGraph LAct) lq q →
        ∀ b₃, !pairDef b₃ (i + 1) yq → ∀ b₂, !pairDef b₂ q b₃ → :⟪n, b₂⟫:∈ C ∧
        ∀ a₃, !pairDef a₃ (i + cq + 1 + sq) yp → ∀ a₂, !pairDef a₂ p a₃ → :⟪n, a₂⟫:∈ C ∧
        ∀ s, !lnBinStepsDef s W T 150 n cq lp lq i sq sp yq yp → y = s) ∨
      (∃ p < r, !qqAllDef r p ∧ ∃ yb <⁺ y, ∀ sb, !shiftsVDef sb yb → ∀ lp, !(formulaLenGraph LAct) lp p →
        ∀ a₃, !pairDef a₃ (i + 1) yb → ∀ a₂, !pairDef a₂ p a₃ → :⟪n + 1, a₂⟫:∈ C ∧
        ∀ s, !lnQuantStepsDef s W T 151 n lp i sb yb → y = s) ∨
      (∃ p < r, !qqExsDef r p ∧ ∃ yb <⁺ y, ∀ sb, !shiftsVDef sb yb → ∀ lp, !(formulaLenGraph LAct) lp p →
        ∀ a₃, !pairDef a₃ (i + 1) yb → ∀ a₂, !pairDef a₂ p a₃ → :⟪n + 1, a₂⟫:∈ C ∧
        ∀ s, !lnQuantStepsDef s W T 152 n lp i sb yb → y = s) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, lenV_defined.iff, lnAtomSteps_defined.iff, lnConstSteps_defined.iff, lnBinSteps_defined.iff,
        lnQuantSteps_defined.iff, descCountF_defined.iff, shiftsV_defined.iff, listSum_defined.iff,
        (termLenVec.defined (L := LAct)).iff, (formulaLen.defined (L := LAct)).iff, numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, Cases, lenV_defined.iff, lnAtomSteps_defined.iff, lnConstSteps_defined.iff, lnBinSteps_defined.iff,
        lnQuantSteps_defined.iff, descCountF_defined.iff, shiftsV_defined.iff, listSum_defined.iff,
        (termLenVec.defined (L := LAct)).iff, (formulaLen.defined (L := LAct)).iff, numeral_eq_natCast]
  monotone := by
    intro C C' hC w pr h
    change Phi (w 0) (w 1) C pr at h
    rw [phi_unpack] at h ⊢
    obtain ⟨n, r, i, y, rfl, h⟩ := h
    refine ⟨n, r, i, y, rfl, ?_⟩
    rcases h with h | h | h | h |
      ⟨p, hp, q, hq, rfl, yq, hyq, yp, hyp, h₁, h₂, rfl⟩ | ⟨p, hp, q, hq, rfl, yq, hyq, yp, hyp, h₁, h₂, rfl⟩ |
      ⟨p, hp, rfl, yb, hyb, h₁, rfl⟩ | ⟨p, hp, rfl, yb, hyb, h₁, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, rfl, yq, hyq, yp, hyp, hC h₁, hC h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, rfl, yq, hyq, yp, hyp, hC h₁, hC h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl, yb, hyb, hC h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, rfl, yb, hyb, hC h₁, rfl⟩))))))

instance : construction.Finite V where
  finite := by
    intro C w pr h
    change Phi (w 0) (w 1) C pr at h
    change ∃ m, Phi (w 0) (w 1) {y ∈ C | y < m} pr
    rw [phi_unpack] at h
    simp only [phi_unpack]
    obtain ⟨n, r, i, y, rfl, h⟩ := h
    rcases h with h | h | h | h |
      ⟨p, hp, q, hq, hr, yq, hyq, yp, hyp, h₁, h₂, hy⟩ | ⟨p, hp, q, hq, hr, yq, hyq, yp, hyp, h₁, h₂, hy⟩ |
      ⟨p, hp, hr, yb, hyb, h₁, hy⟩ | ⟨p, hp, hr, yb, hyb, h₁, hy⟩
    · exact ⟨0, n, r, i, y, rfl, Or.inl h⟩
    · exact ⟨0, n, r, i, y, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨0, n, r, i, y, rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨0, n, r, i, y, rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · refine ⟨⟪n, q, i + 1, yq⟫ + ⟪n, p, i + descCountF (w 0) n q + 1 + shiftsV yq, yp⟫ + 1, n, r, i, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, hr, yq, hyq, yp, hyp,
          ⟨h₁, lt_of_le_of_lt le_self_add (lt_add_one _)⟩, ⟨h₂, lt_of_le_of_lt le_add_self (lt_add_one _)⟩, hy⟩))))⟩
    · refine ⟨⟪n, q, i + 1, yq⟫ + ⟪n, p, i + descCountF (w 0) n q + 1 + shiftsV yq, yp⟫ + 1, n, r, i, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, q, hq, hr, yq, hyq, yp, hyp,
          ⟨h₁, lt_of_le_of_lt le_self_add (lt_add_one _)⟩, ⟨h₂, lt_of_le_of_lt le_add_self (lt_add_one _)⟩, hy⟩)))))⟩
    · exact ⟨⟪n + 1, p, i + 1, yb⟫ + 1, n, r, i, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hr, yb, hyb, ⟨h₁, lt_add_one _⟩, hy⟩))))))⟩
    · exact ⟨⟪n + 1, p, i + 1, yb⟫ + 1, n, r, i, y, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hr, yb, hyb, ⟨h₁, lt_add_one _⟩, hy⟩))))))⟩

lemma phi_iff (W T : V) (C : Set V) (n r i y : V) :
    Phi W T C ⟪n, r, i, y⟫ ↔
    ( (∃ k R v, r = ^rel k R v ∧
        y = lnAtomSteps W T 142 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1))) ∨
      (∃ k R v, r = ^nrel k R v ∧
        y = lnAtomSteps W T 143 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1))) ∨
      (r = ^⊤ ∧ y = lnConstSteps W 147 i) ∨
      (r = ^⊥ ∧ y = lnConstSteps W 148 i) ∨
      (∃ p q yq yp, r = p ^⋏ q ∧ yq ≤ y ∧ yp ≤ y ∧
        ⟪n, q, i + 1, yq⟫ ∈ C ∧ ⟪n, p, i + descCountF W n q + 1 + shiftsV yq, yp⟫ ∈ C ∧
        y = lnBinSteps W T 149 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp) ∨
      (∃ p q yq yp, r = p ^⋎ q ∧ yq ≤ y ∧ yp ≤ y ∧
        ⟪n, q, i + 1, yq⟫ ∈ C ∧ ⟪n, p, i + descCountF W n q + 1 + shiftsV yq, yp⟫ ∈ C ∧
        y = lnBinSteps W T 150 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp) ∨
      (∃ p yb, r = ^∀ p ∧ yb ≤ y ∧ ⟪n + 1, p, i + 1, yb⟫ ∈ C ∧ y = lnQuantSteps W T 151 n (formulaLen LAct p) i (shiftsV yb) yb) ∨
      (∃ p yb, r = ^∃ p ∧ yb ≤ y ∧ ⟪n + 1, p, i + 1, yb⟫ ∈ C ∧ y = lnQuantSteps W T 152 n (formulaLen LAct p) i (shiftsV yb) yb) ) := by
  rw [show Phi W T C ⟪n, r, i, y⟫ ↔ Cases W T C n r i y from ⟨cases_of_phi, phi_of_cases⟩]
  unfold Cases
  constructor
  · rintro (⟨k, _, R, _, v, _, rfl, rfl⟩ | ⟨k, _, R, _, v, _, rfl, rfl⟩ | h | h |
      ⟨p, _, q, _, rfl, yq, hyq, yp, hyp, h₁, h₂, rfl⟩ | ⟨p, _, q, _, rfl, yq, hyq, yp, hyp, h₁, h₂, rfl⟩ |
      ⟨p, _, rfl, yb, hyb, h₁, rfl⟩ | ⟨p, _, rfl, yb, hyb, h₁, rfl⟩)
    · exact Or.inl ⟨k, R, v, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k, R, v, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, yq, yp, rfl, hyq, hyp, h₁, h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, yq, yp, rfl, hyq, hyp, h₁, h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, yb, rfl, hyb, h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, yb, rfl, hyb, h₁, rfl⟩))))))
  · rintro (⟨k, R, v, rfl, rfl⟩ | ⟨k, R, v, rfl, rfl⟩ | h | h |
      ⟨p, q, yq, yp, rfl, hyq, hyp, h₁, h₂, rfl⟩ | ⟨p, q, yq, yp, rfl, hyq, hyp, h₁, h₂, rfl⟩ |
      ⟨p, yb, rfl, hyb, h₁, rfl⟩ | ⟨p, yb, rfl, hyb, h₁, rfl⟩)
    · exact Or.inl ⟨k, by simp, R, by simp, v, by simp, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k, by simp, R, by simp, v, by simp, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl, yq, hyq, yp, hyp, h₁, h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl, yq, hyq, yp, hyp, h₁, h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, yb, hyb, h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, by simp, rfl, yb, hyb, h₁, rfl⟩))))))

end LenF

def LenFPacked (W T pr : V) : Prop := LenF.construction.Fixpoint ![W, T] pr
/-- `LenFGraph W T n r i y`: the length steps of the formula `r` (dossier at `&i`) are the list `y`. -/
def LenFGraph (W T n r i y : V) : Prop := LenFPacked W T ⟪n, r, i, y⟫

noncomputable def lenFPackedDef : 𝚺₁.Semisentence 3 := .mkSigma “W T pr. !LenF.blueprint.fixpointDef pr W T”

instance lenFPacked_defined : 𝚺₁-Relation₃ (LenFPacked : V → V → V → Prop) via lenFPackedDef := .mk
  fun v ↦ by
    simp only [lenFPackedDef, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.constant_eq_singleton]
    rw [LenF.construction.eval_fixpointDef]
    rfl
instance lenFPacked_definable : 𝚺₁-Relation₃ (LenFPacked : V → V → V → Prop) := lenFPacked_defined.to_definable

noncomputable def lenFGraphDef : 𝚺₁.Semisentence 6 := .mkSigma
  “W T n r i y. ∃ q₂, !pairDef q₂ i y ∧ ∃ q₁, !pairDef q₁ r q₂ ∧ ∃ pr, !pairDef pr n q₁ ∧ !lenFPackedDef W T pr”
instance lenFGraph_defined :
    𝚺₁.Defined (fun v : Fin 6 → V ↦ LenFGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) lenFGraphDef := .mk
  fun v ↦ by simp [lenFGraphDef, lenFPacked_defined.iff, LenFGraph]
instance lenFGraph_definable :
    𝚺₁.Definable (fun v : Fin 6 → V ↦ LenFGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := lenFGraph_defined.to_definable

lemma LenFGraph.case_iff {W T n r i y : V} :
    LenFGraph W T n r i y ↔
    ( (∃ k R v, r = ^rel k R v ∧
        y = lnAtomSteps W T 142 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1))) ∨
      (∃ k R v, r = ^nrel k R v ∧
        y = lnAtomSteps W T 143 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1))) ∨
      (r = ^⊤ ∧ y = lnConstSteps W 147 i) ∨
      (r = ^⊥ ∧ y = lnConstSteps W 148 i) ∨
      (∃ p q yq yp, r = p ^⋏ q ∧ yq ≤ y ∧ yp ≤ y ∧
        LenFGraph W T n q (i + 1) yq ∧ LenFGraph W T n p (i + descCountF W n q + 1 + shiftsV yq) yp ∧
        y = lnBinSteps W T 149 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp) ∨
      (∃ p q yq yp, r = p ^⋎ q ∧ yq ≤ y ∧ yp ≤ y ∧
        LenFGraph W T n q (i + 1) yq ∧ LenFGraph W T n p (i + descCountF W n q + 1 + shiftsV yq) yp ∧
        y = lnBinSteps W T 150 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp) ∨
      (∃ p yb, r = ^∀ p ∧ yb ≤ y ∧ LenFGraph W T (n + 1) p (i + 1) yb ∧ y = lnQuantSteps W T 151 n (formulaLen LAct p) i (shiftsV yb) yb) ∨
      (∃ p yb, r = ^∃ p ∧ yb ≤ y ∧ LenFGraph W T (n + 1) p (i + 1) yb ∧ y = lnQuantSteps W T 152 n (formulaLen LAct p) i (shiftsV yb) yb) ) := by
  unfold LenFGraph LenFPacked
  rw [LenF.construction.case]
  exact LenF.phi_iff W T _ n r i y

section lenFInversion

attribute [local simp] qqRel qqNRel qqVerum qqFalsum qqAnd qqOr qqAll qqExs

lemma LenFGraph.rel_iff {W T n k R v i y : V} :
    LenFGraph W T n (^rel k R v) i y ↔
    y = lnAtomSteps W T 142 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1)) := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.nrel_iff {W T n k R v i y : V} :
    LenFGraph W T n (^nrel k R v) i y ↔
    y = lnAtomSteps W T 143 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1)) := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.verum_iff {W T n i y : V} : LenFGraph W T n ^⊤ i y ↔ y = lnConstSteps W 147 i := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.falsum_iff {W T n i y : V} : LenFGraph W T n ^⊥ i y ↔ y = lnConstSteps W 148 i := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.and_iff {W T n p q i y : V} :
    LenFGraph W T n (p ^⋏ q) i y ↔
    ∃ yq yp, yq ≤ y ∧ yp ≤ y ∧ LenFGraph W T n q (i + 1) yq ∧ LenFGraph W T n p (i + descCountF W n q + 1 + shiftsV yq) yp ∧
      y = lnBinSteps W T 149 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.or_iff {W T n p q i y : V} :
    LenFGraph W T n (p ^⋎ q) i y ↔
    ∃ yq yp, yq ≤ y ∧ yp ≤ y ∧ LenFGraph W T n q (i + 1) yq ∧ LenFGraph W T n p (i + descCountF W n q + 1 + shiftsV yq) yp ∧
      y = lnBinSteps W T 150 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i (shiftsV yq) (shiftsV yp) yq yp := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.all_iff {W T n p i y : V} :
    LenFGraph W T n (^∀ p) i y ↔
    ∃ yb, yb ≤ y ∧ LenFGraph W T (n + 1) p (i + 1) yb ∧ y = lnQuantSteps W T 151 n (formulaLen LAct p) i (shiftsV yb) yb := by
  rw [LenFGraph.case_iff]; simp
lemma LenFGraph.exs_iff {W T n p i y : V} :
    LenFGraph W T n (^∃ p) i y ↔
    ∃ yb, yb ≤ y ∧ LenFGraph W T (n + 1) p (i + 1) yb ∧ y = lnQuantSteps W T 152 n (formulaLen LAct p) i (shiftsV yb) yb := by
  rw [LenFGraph.case_iff]; simp

end lenFInversion

lemma le_lnBinSteps_left (W T c n cq lp lq i sq sp yq yp : V) : yq ≤ lnBinSteps W T c n cq lp lq i sq sp yq yp :=
  le_appendV_left _ _
lemma le_lnBinSteps_right (W T c n cq lp lq i sq sp yq yp : V) : yp ≤ lnBinSteps W T c n cq lp lq i sq sp yq yp :=
  le_trans (le_appendV_left _ _) (le_appendV_right _ _)
lemma le_lnQuantSteps (W T c n lp i sb yb : V) : yb ≤ lnQuantSteps W T c n lp i sb yb := le_appendV_left _ _

/-! ### 5.6 Structure of the formula lists; existence, uniqueness, and the producer `lenSteps` -/

section lenFStruct

lemma ctag_lnConstRow {W : V} (hWp : W = certPieces) {c : V} (hc : c = 147 ∨ c = 148) (ev : V) : sTag (mkStep W c ev) = 0 := by
  rcases hc with rfl | rfl
  · exact ctag_formulaLenVerum hWp ev
  · exact ctag_formulaLenFalsum hWp ev
lemma ctag_lnBinRow {W : V} (hWp : W = certPieces) {c : V} (hc : c = 149 ∨ c = 150) (ev : V) : sTag (mkStep W c ev) = 0 := by
  rcases hc with rfl | rfl
  · exact ctag_formulaLenAnd hWp ev
  · exact ctag_formulaLenOr hWp ev
lemma ctag_lnQuantRow {W : V} (hWp : W = certPieces) {c : V} (hc : c = 151 ∨ c = 152) (ev : V) : sTag (mkStep W c ev) = 0 := by
  rcases hc with rfl | rfl
  · exact ctag_formulaLenAll hWp ev
  · exact ctag_formulaLenExs hWp ev
lemma ctag_lnAtomRow {W : V} (hWp : W = certPieces) {c : V} (hc : c = 142 ∨ c = 143) (ev : V) : sTag (mkStep W c ev) = 0 := by
  rcases hc with rfl | rfl
  · exact ctag_formulaLenRelCert hWp ev
  · exact ctag_formulaLenNRelCert hWp ev

lemma lnConstSteps_struct {W : V} (hWp : W = certPieces) {c : V} (hc : c = 147 ∨ c = 148) (i : V) :
    NoDrop' (lnConstSteps W c i) ∧ shiftsV (lnConstSteps W c i) = 1 := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_cons (noDrop'_tag2 (ctag_formulaLenTotal hWp _)) (noDrop'_cons (noDrop'_tag0 (ctag_lnConstRow hWp hc _))
      (noDrop'_single (noDrop'_tag0 (ctag_congLenNum hWp _))))
  · rw [lnConstSteps, shiftsV_cons_tag2 (ctag_formulaLenTotal hWp _), shiftsV_cons_tag0 (ctag_lnConstRow hWp hc _),
      shiftsV_single_tag0 (ctag_congLenNum hWp _), add_zero]
lemma len_lnConstSteps (W c i : V) : len (lnConstSteps W c i) = 3 := by
  rw [lnConstSteps, len_adjoin, len_adjoin, len_adjoin, len_nil]; norm_num

lemma lnBinSteps_struct {W : V} (hWp : W = certPieces) {c : V} (hc : c = 149 ∨ c = 150) (T n cq lp lq i sq sp yq yp : V)
    (hq : NoDrop' yq) (hp : NoDrop' yp) :
    NoDrop' (lnBinSteps W T c n cq lp lq i sq sp yq yp) ∧
    shiftsV (lnBinSteps W T c n cq lp lq i sq sp yq yp) = shiftsV yq + (shiftsV yp + 1) := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_appendV hq (noDrop'_appendV hp (noDrop'_cons (noDrop'_tag2 (ctag_formulaLenTotal hWp _))
      (noDrop'_cons (noDrop'_tag0 (ctag_lnBinRow hWp hc _)) (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _))
      (noDrop'_cons (noDrop'_tag0 (ctag_congSucc hWp _)) (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _))
      (noDrop'_cons (noDrop'_tag0 (ctag_eqTrans hWp _)) (noDrop'_cons (noDrop'_tag0 (ctag_eqTrans hWp _))
      (noDrop'_single (noDrop'_tag0 (ctag_congLenNum hWp _)))))))))))
  · rw [lnBinSteps, shiftsV_appendV, shiftsV_appendV, shiftsV_cons_tag2 (ctag_formulaLenTotal hWp _),
      shiftsV_cons_tag0 (ctag_lnBinRow hWp hc _), shiftsV_cons_sLemma, shiftsV_cons_tag0 (ctag_congSucc hWp _),
      shiftsV_cons_sLemma, shiftsV_cons_tag0 (ctag_eqTrans hWp _), shiftsV_cons_tag0 (ctag_eqTrans hWp _),
      shiftsV_single_tag0 (ctag_congLenNum hWp _), add_zero]
lemma len_lnBinSteps (W T c n cq lp lq i sq sp yq yp : V) :
    len (lnBinSteps W T c n cq lp lq i sq sp yq yp) = len yq + (len yp + 8) := by
  rw [lnBinSteps, len_appendV, len_appendV, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin,
    len_adjoin, len_nil]; ring

lemma lnQuantSteps_struct {W : V} (hWp : W = certPieces) {c : V} (hc : c = 151 ∨ c = 152) (T n lp i sb yb : V)
    (hb : NoDrop' yb) :
    NoDrop' (lnQuantSteps W T c n lp i sb yb) ∧ shiftsV (lnQuantSteps W T c n lp i sb yb) = shiftsV yb + 1 := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_appendV hb (noDrop'_cons (noDrop'_tag2 (ctag_formulaLenTotal hWp _))
      (noDrop'_cons (noDrop'_tag0 (ctag_lnQuantRow hWp hc _)) (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _))
      (noDrop'_cons (noDrop'_tag0 (ctag_eqTrans hWp _)) (noDrop'_single (noDrop'_tag0 (ctag_congLenNum hWp _)))))))
  · rw [lnQuantSteps, shiftsV_appendV, shiftsV_cons_tag2 (ctag_formulaLenTotal hWp _), shiftsV_cons_tag0 (ctag_lnQuantRow hWp hc _),
      shiftsV_cons_sLemma, shiftsV_cons_tag0 (ctag_eqTrans hWp _), shiftsV_single_tag0 (ctag_congLenNum hWp _), add_zero]
lemma len_lnQuantSteps (W T c n lp i sb yb : V) : len (lnQuantSteps W T c n lp i sb yb) = len yb + 5 := by
  rw [lnQuantSteps, len_appendV, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_nil]; ring

lemma lnAtomSteps_struct {W : V} (hWp : W = certPieces) {c : V} (hc : c = 142 ∨ c = 143) (T k R σ i sv yv : V)
    (hv : NoDrop' yv) :
    NoDrop' (lnAtomSteps W T c k R σ i sv yv) ∧ shiftsV (lnAtomSteps W T c k R σ i sv yv) = shiftsV yv + 1 := by
  refine ⟨?_, ?_⟩
  · exact noDrop'_appendV hv (noDrop'_cons (noDrop'_tag0 (ctag_certRelRow hWp _ _))
      (noDrop'_cons (noDrop'_tag2 (ctag_formulaLenTotal hWp _)) (noDrop'_cons (noDrop'_tag0 (ctag_lnAtomRow hWp hc _))
      (noDrop'_cons (noDrop'_tag7 (sTag_sLemma _ _)) (noDrop'_cons (noDrop'_tag0 (ctag_eqTrans hWp _))
      (noDrop'_single (noDrop'_tag0 (ctag_congLenNum hWp _))))))))
  · rw [lnAtomSteps, shiftsV_appendV, shiftsV_cons_tag0 (ctag_certRelRow hWp _ _), shiftsV_cons_tag2 (ctag_formulaLenTotal hWp _),
      shiftsV_cons_tag0 (ctag_lnAtomRow hWp hc _), shiftsV_cons_sLemma, shiftsV_cons_tag0 (ctag_eqTrans hWp _),
      shiftsV_single_tag0 (ctag_congLenNum hWp _), add_zero]
lemma len_lnAtomSteps (W T c k R σ i sv yv : V) : len (lnAtomSteps W T c k R σ i sv yv) = len yv + 6 := by
  rw [lnAtomSteps, len_appendV, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_adjoin, len_nil]; ring

set_option maxHeartbeats 2000000 in
/-- **Length bound, `W`-free**: `len y ≤ 14|r|`. -/
lemma lenFGraph_len (W T : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i y : V, LenFGraph W T n r i y → len y ≤ 14 * formulaLen LAct r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i y : V, LenFGraph W T n r i y → len y ≤ 14 * formulaLen LAct r)
  · simp only [LenFGraph]; definability
  · intro n k R v hkR hv i y hy
    rw [LenFGraph.rel_iff.mp hy, len_lnAtomSteps, formulaLen_rel hkR hv.isUTerm]
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hl := (lenVGraph_len W T n hv k le_rfl).2 (i + 1) _ (lenV_graph hv le_rfl)
    rw [htl] at hl
    calc len (lenV W T n k v k (i + 1)) + 6 ≤ (14 * listSum (termLenVec LAct k v) + 2) + 6 := add_le_add hl (le_refl (6 : V))
      _ = 14 * listSum (termLenVec LAct k v) + 8 := by ring
      _ ≤ 14 * listSum (termLenVec LAct k v) + 14 := add_le_add (le_refl _) (by norm_num)
      _ = 14 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n k R v hkR hv i y hy
    rw [LenFGraph.nrel_iff.mp hy, len_lnAtomSteps, formulaLen_nrel hkR hv.isUTerm]
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hl := (lenVGraph_len W T n hv k le_rfl).2 (i + 1) _ (lenV_graph hv le_rfl)
    rw [htl] at hl
    calc len (lenV W T n k v k (i + 1)) + 6 ≤ (14 * listSum (termLenVec LAct k v) + 2) + 6 := add_le_add hl (le_refl (6 : V))
      _ = 14 * listSum (termLenVec LAct k v) + 8 := by ring
      _ ≤ 14 * listSum (termLenVec LAct k v) + 14 := add_le_add (le_refl _) (by norm_num)
      _ = 14 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n i y hy
    rw [LenFGraph.verum_iff.mp hy, len_lnConstSteps, formulaLen_verum]; norm_num
  · intro n i y hy
    rw [LenFGraph.falsum_iff.mp hy, len_lnConstSteps, formulaLen_falsum]; norm_num
  · intro n p q hp hq ihp ihq i y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.and_iff.mp hy
    rw [len_lnBinSteps, formulaLen_and hp.isUFormula hq.isUFormula]
    calc len yq + (len yp + 8) ≤ 14 * formulaLen LAct q + (14 * formulaLen LAct p + 8) :=
          add_le_add (ihq _ _ hyq) (add_le_add (ihp _ _ hyp) (le_refl (8 : V)))
      _ ≤ 14 * formulaLen LAct q + (14 * formulaLen LAct p + 14) := by gcongr; norm_num
      _ = 14 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
  · intro n p q hp hq ihp ihq i y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.or_iff.mp hy
    rw [len_lnBinSteps, formulaLen_or hp.isUFormula hq.isUFormula]
    calc len yq + (len yp + 8) ≤ 14 * formulaLen LAct q + (14 * formulaLen LAct p + 8) :=
          add_le_add (ihq _ _ hyq) (add_le_add (ihp _ _ hyp) (le_refl (8 : V)))
      _ ≤ 14 * formulaLen LAct q + (14 * formulaLen LAct p + 14) := by gcongr; norm_num
      _ = 14 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
  · intro n p hp ih i y hy
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.all_iff.mp hy
    rw [len_lnQuantSteps, formulaLen_all hp.isUFormula]
    calc len yb + 5 ≤ 14 * formulaLen LAct p + 5 := add_le_add (ih _ _ hyb) (le_refl (5 : V))
      _ ≤ 14 * formulaLen LAct p + 14 := by gcongr; norm_num
      _ = 14 * (formulaLen LAct p + 1) := by ring
  · intro n p hp ih i y hy
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.exs_iff.mp hy
    rw [len_lnQuantSteps, formulaLen_exs hp.isUFormula]
    calc len yb + 5 ≤ 14 * formulaLen LAct p + 5 := add_le_add (ih _ _ hyb) (le_refl (5 : V))
      _ ≤ 14 * formulaLen LAct p + 14 := by gcongr; norm_num
      _ = 14 * (formulaLen LAct p + 1) := by ring

set_option maxHeartbeats 2000000 in
/-- **`NoDrop'` and the shift count**: `shiftsV y + 1 ≤ 2|r|`. -/
lemma lenFGraph_noDrop_shifts {W : V} (hWp : W = certPieces) (T : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i y : V, LenFGraph W T n r i y → NoDrop' y ∧ shiftsV y + 1 ≤ 2 * formulaLen LAct r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i y : V, LenFGraph W T n r i y → NoDrop' y ∧ shiftsV y + 1 ≤ 2 * formulaLen LAct r)
  · simp only [LenFGraph]; definability
  · intro n k R v hkR hv i y hy
    rw [LenFGraph.rel_iff.mp hy, formulaLen_rel hkR hv.isUTerm]
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨hnV, hsV⟩ := lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) _ (lenV_graph hv le_rfl)
    rw [htl] at hsV
    obtain ⟨h1, h2⟩ := lnAtomSteps_struct hWp (Or.inl rfl) T k R _ i _ _ hnV
    refine ⟨h1, ?_⟩
    rw [h2]
    calc shiftsV (lenV W T n k v k (i + 1)) + 1 + 1 = shiftsV (lenV W T n k v k (i + 1)) + 2 := by ring
      _ ≤ 2 * listSum (termLenVec LAct k v) + 2 := add_le_add hsV (le_refl (2 : V))
      _ = 2 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n k R v hkR hv i y hy
    rw [LenFGraph.nrel_iff.mp hy, formulaLen_nrel hkR hv.isUTerm]
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨hnV, hsV⟩ := lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) _ (lenV_graph hv le_rfl)
    rw [htl] at hsV
    obtain ⟨h1, h2⟩ := lnAtomSteps_struct hWp (Or.inr rfl) T k R _ i _ _ hnV
    refine ⟨h1, ?_⟩
    rw [h2]
    calc shiftsV (lenV W T n k v k (i + 1)) + 1 + 1 = shiftsV (lenV W T n k v k (i + 1)) + 2 := by ring
      _ ≤ 2 * listSum (termLenVec LAct k v) + 2 := add_le_add hsV (le_refl (2 : V))
      _ = 2 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n i y hy
    rw [LenFGraph.verum_iff.mp hy, formulaLen_verum]
    obtain ⟨h1, h2⟩ := lnConstSteps_struct hWp (Or.inl rfl) i
    exact ⟨h1, by rw [h2]; norm_num⟩
  · intro n i y hy
    rw [LenFGraph.falsum_iff.mp hy, formulaLen_falsum]
    obtain ⟨h1, h2⟩ := lnConstSteps_struct hWp (Or.inr rfl) i
    exact ⟨h1, by rw [h2]; norm_num⟩
  · intro n p q hp hq ihp ihq i y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.and_iff.mp hy
    obtain ⟨hnq, hsq⟩ := ihq _ _ hyq
    obtain ⟨hnp, hsp⟩ := ihp _ _ hyp
    obtain ⟨h1, h2⟩ := lnBinSteps_struct hWp (Or.inl rfl) T n _ _ _ i _ _ yq yp hnq hnp
    refine ⟨h1, ?_⟩
    rw [h2, formulaLen_and hp.isUFormula hq.isUFormula]
    calc shiftsV yq + (shiftsV yp + 1) + 1 = (shiftsV yq + 1) + (shiftsV yp + 1) := by ring
      _ ≤ 2 * formulaLen LAct q + 2 * formulaLen LAct p := add_le_add hsq hsp
      _ ≤ 2 * formulaLen LAct q + 2 * formulaLen LAct p + 2 := le_self_add
      _ = 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
  · intro n p q hp hq ihp ihq i y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.or_iff.mp hy
    obtain ⟨hnq, hsq⟩ := ihq _ _ hyq
    obtain ⟨hnp, hsp⟩ := ihp _ _ hyp
    obtain ⟨h1, h2⟩ := lnBinSteps_struct hWp (Or.inr rfl) T n _ _ _ i _ _ yq yp hnq hnp
    refine ⟨h1, ?_⟩
    rw [h2, formulaLen_or hp.isUFormula hq.isUFormula]
    calc shiftsV yq + (shiftsV yp + 1) + 1 = (shiftsV yq + 1) + (shiftsV yp + 1) := by ring
      _ ≤ 2 * formulaLen LAct q + 2 * formulaLen LAct p := add_le_add hsq hsp
      _ ≤ 2 * formulaLen LAct q + 2 * formulaLen LAct p + 2 := le_self_add
      _ = 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
  · intro n p hp ih i y hy
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.all_iff.mp hy
    obtain ⟨hnb, hsb⟩ := ih _ _ hyb
    obtain ⟨h1, h2⟩ := lnQuantSteps_struct hWp (Or.inl rfl) T n _ i _ yb hnb
    refine ⟨h1, ?_⟩
    rw [h2, formulaLen_all hp.isUFormula]
    calc shiftsV yb + 1 + 1 ≤ 2 * formulaLen LAct p + 1 := add_le_add hsb (le_refl (1 : V))
      _ ≤ 2 * formulaLen LAct p + 2 := by gcongr; norm_num
      _ = 2 * (formulaLen LAct p + 1) := by ring
  · intro n p hp ih i y hy
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.exs_iff.mp hy
    obtain ⟨hnb, hsb⟩ := ih _ _ hyb
    obtain ⟨h1, h2⟩ := lnQuantSteps_struct hWp (Or.inr rfl) T n _ i _ yb hnb
    refine ⟨h1, ?_⟩
    rw [h2, formulaLen_exs hp.isUFormula]
    calc shiftsV yb + 1 + 1 ≤ 2 * formulaLen LAct p + 1 := add_le_add hsb (le_refl (1 : V))
      _ ≤ 2 * formulaLen LAct p + 2 := by gcongr; norm_num
      _ = 2 * (formulaLen LAct p + 1) := by ring

end lenFStruct

section lenFFun

set_option maxHeartbeats 2000000 in
/-- **Existence**, offsets bounded by `B` (Σ₁ motive; `W`-free through `shiftsV_le_len` + `lenFGraph_len`). -/
lemma lenFGraph_exists_bounded (W T B : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i ≤ B, i + descCountF W n r + 16 * formulaLen LAct r ≤ B → ∃ y, LenFGraph W T n r i y := by
  intro n r
  apply IsSemiformula.sigma1_structural_induction
    (P := fun n r ↦ ∀ i ≤ B, i + descCountF W n r + 16 * formulaLen LAct r ≤ B → ∃ y, LenFGraph W T n r i y)
  · simp only [LenFGraph]; definability
  · intro n k R v _ _ i _ _; exact ⟨_, LenFGraph.rel_iff.mpr rfl⟩
  · intro n k R v _ _ i _ _; exact ⟨_, LenFGraph.nrel_iff.mpr rfl⟩
  · intro n i _ _; exact ⟨_, LenFGraph.verum_iff.mpr rfl⟩
  · intro n i _ _; exact ⟨_, LenFGraph.falsum_iff.mpr rfl⟩
  · intro n p q hp hq ihp ihq i hi hiB
    rw [descCountF_and W n hp hq, formulaLen_and hp.isUFormula hq.isUFormula] at hiB
    set cp := descCountF W n p with hcp
    set cq := descCountF W n q with hcq
    set lp := formulaLen LAct p with hlp
    set lq := formulaLen LAct q with hlq
    have hiq : i + 1 + cq + 16 * lq ≤ B := by
      calc i + 1 + cq + 16 * lq ≤ i + (cp + cq + 1) + 16 * (lp + lq + 1) := by
            rw [show i + (cp + cq + 1) + 16 * (lp + lq + 1) = (i + 1 + cq + 16 * lq) + (cp + 16 * lp + 16) by ring]
            exact le_self_add
        _ ≤ B := hiB
    obtain ⟨yq, hyq⟩ := ihq (i + 1) (le_trans (le_trans le_self_add le_self_add) hiq) hiq
    have hsq : shiftsV yq ≤ 14 * lq := le_trans (shiftsV_le_len yq) (lenFGraph_len W T hq (i + 1) yq hyq)
    have hip : i + cq + 1 + shiftsV yq + cp + 16 * lp ≤ B := by
      calc i + cq + 1 + shiftsV yq + cp + 16 * lp ≤ i + cq + 1 + 14 * lq + cp + 16 * lp := by gcongr
        _ ≤ i + (cp + cq + 1) + 16 * (lp + lq + 1) := by
            rw [show i + (cp + cq + 1) + 16 * (lp + lq + 1) = (i + cq + 1 + 14 * lq + cp + 16 * lp) + (2 * lq + 16) by ring]
            exact le_self_add
        _ ≤ B := hiB
    obtain ⟨yp, hyp⟩ := ihp (i + cq + 1 + shiftsV yq) (le_trans (le_trans le_self_add le_self_add) hip) hip
    exact ⟨_, LenFGraph.and_iff.mpr ⟨yq, yp, le_lnBinSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
      le_lnBinSteps_right _ _ _ _ _ _ _ _ _ _ _ _, hyq, hyp, rfl⟩⟩
  · intro n p q hp hq ihp ihq i hi hiB
    rw [descCountF_or W n hp hq, formulaLen_or hp.isUFormula hq.isUFormula] at hiB
    set cp := descCountF W n p with hcp
    set cq := descCountF W n q with hcq
    set lp := formulaLen LAct p with hlp
    set lq := formulaLen LAct q with hlq
    have hiq : i + 1 + cq + 16 * lq ≤ B := by
      calc i + 1 + cq + 16 * lq ≤ i + (cp + cq + 1) + 16 * (lp + lq + 1) := by
            rw [show i + (cp + cq + 1) + 16 * (lp + lq + 1) = (i + 1 + cq + 16 * lq) + (cp + 16 * lp + 16) by ring]
            exact le_self_add
        _ ≤ B := hiB
    obtain ⟨yq, hyq⟩ := ihq (i + 1) (le_trans (le_trans le_self_add le_self_add) hiq) hiq
    have hsq : shiftsV yq ≤ 14 * lq := le_trans (shiftsV_le_len yq) (lenFGraph_len W T hq (i + 1) yq hyq)
    have hip : i + cq + 1 + shiftsV yq + cp + 16 * lp ≤ B := by
      calc i + cq + 1 + shiftsV yq + cp + 16 * lp ≤ i + cq + 1 + 14 * lq + cp + 16 * lp := by gcongr
        _ ≤ i + (cp + cq + 1) + 16 * (lp + lq + 1) := by
            rw [show i + (cp + cq + 1) + 16 * (lp + lq + 1) = (i + cq + 1 + 14 * lq + cp + 16 * lp) + (2 * lq + 16) by ring]
            exact le_self_add
        _ ≤ B := hiB
    obtain ⟨yp, hyp⟩ := ihp (i + cq + 1 + shiftsV yq) (le_trans (le_trans le_self_add le_self_add) hip) hip
    exact ⟨_, LenFGraph.or_iff.mpr ⟨yq, yp, le_lnBinSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
      le_lnBinSteps_right _ _ _ _ _ _ _ _ _ _ _ _, hyq, hyp, rfl⟩⟩
  · intro n p hp ih i hi hiB
    rw [descCountF_all W n hp, formulaLen_all hp.isUFormula] at hiB
    have hib : i + 1 + descCountF W (n + 1) p + 16 * formulaLen LAct p ≤ B := by
      calc i + 1 + descCountF W (n + 1) p + 16 * formulaLen LAct p ≤ i + (descCountF W (n + 1) p + 1) + 16 * (formulaLen LAct p + 1) := by
            rw [show i + (descCountF W (n + 1) p + 1) + 16 * (formulaLen LAct p + 1) =
              (i + 1 + descCountF W (n + 1) p + 16 * formulaLen LAct p) + 16 by ring]
            exact le_self_add
        _ ≤ B := hiB
    obtain ⟨yb, hyb⟩ := ih (i + 1) (le_trans (le_trans le_self_add le_self_add) hib) hib
    exact ⟨_, LenFGraph.all_iff.mpr ⟨yb, le_lnQuantSteps _ _ _ _ _ _ _ _, hyb, rfl⟩⟩
  · intro n p hp ih i hi hiB
    rw [descCountF_exs W n hp, formulaLen_exs hp.isUFormula] at hiB
    have hib : i + 1 + descCountF W (n + 1) p + 16 * formulaLen LAct p ≤ B := by
      calc i + 1 + descCountF W (n + 1) p + 16 * formulaLen LAct p ≤ i + (descCountF W (n + 1) p + 1) + 16 * (formulaLen LAct p + 1) := by
            rw [show i + (descCountF W (n + 1) p + 1) + 16 * (formulaLen LAct p + 1) =
              (i + 1 + descCountF W (n + 1) p + 16 * formulaLen LAct p) + 16 by ring]
            exact le_self_add
        _ ≤ B := hiB
    obtain ⟨yb, hyb⟩ := ih (i + 1) (le_trans (le_trans le_self_add le_self_add) hib) hib
    exact ⟨_, LenFGraph.exs_iff.mpr ⟨yb, le_lnQuantSteps _ _ _ _ _ _ _ _, hyb, rfl⟩⟩

lemma lenFGraph_exists (W T : V) {n r : V} (hr : IsSemiformula LAct n r) (i : V) : ∃ y, LenFGraph W T n r i y :=
  lenFGraph_exists_bounded W T (i + descCountF W n r + 16 * formulaLen LAct r) hr i (le_trans le_self_add le_self_add) le_rfl

set_option maxHeartbeats 2000000 in
/-- **Uniqueness** (Π₁ motive). -/
lemma lenFGraph_unique (W T : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ i y₁ y₂, LenFGraph W T n r i y₁ → LenFGraph W T n r i y₂ → y₁ = y₂ := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ i y₁ y₂, LenFGraph W T n r i y₁ → LenFGraph W T n r i y₂ → y₁ = y₂)
  · simp only [LenFGraph]; definability
  · intro n k R v _ _ i y₁ y₂ h₁ h₂; rw [LenFGraph.rel_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n k R v _ _ i y₁ y₂ h₁ h₂; rw [LenFGraph.nrel_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n i y₁ y₂ h₁ h₂; rw [LenFGraph.verum_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n i y₁ y₂ h₁ h₂; rw [LenFGraph.falsum_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n p q _ _ ihp ihq i y₁ y₂ h₁ h₂
    obtain ⟨yq, yp, _, _, hq₁, hp₁, rfl⟩ := LenFGraph.and_iff.mp h₁
    obtain ⟨yq', yp', _, _, hq₂, hp₂, rfl⟩ := LenFGraph.and_iff.mp h₂
    obtain rfl := ihq _ yq yq' hq₁ hq₂
    obtain rfl := ihp _ yp yp' hp₁ hp₂
    rfl
  · intro n p q _ _ ihp ihq i y₁ y₂ h₁ h₂
    obtain ⟨yq, yp, _, _, hq₁, hp₁, rfl⟩ := LenFGraph.or_iff.mp h₁
    obtain ⟨yq', yp', _, _, hq₂, hp₂, rfl⟩ := LenFGraph.or_iff.mp h₂
    obtain rfl := ihq _ yq yq' hq₁ hq₂
    obtain rfl := ihp _ yp yp' hp₁ hp₂
    rfl
  · intro n p _ ih i y₁ y₂ h₁ h₂
    obtain ⟨yb, _, hb₁, rfl⟩ := LenFGraph.all_iff.mp h₁
    obtain ⟨yb', _, hb₂, rfl⟩ := LenFGraph.all_iff.mp h₂
    rw [ih _ yb yb' hb₁ hb₂]
  · intro n p _ ih i y₁ y₂ h₁ h₂
    obtain ⟨yb, _, hb₁, rfl⟩ := LenFGraph.exs_iff.mp h₁
    obtain ⟨yb', _, hb₂, rfl⟩ := LenFGraph.exs_iff.mp h₂
    rw [ih _ yb yb' hb₁ hb₂]

lemma lenFGraph_existsUnique_total (W T n r i : V) :
    ∃! y, (IsSemiformula LAct n r → LenFGraph W T n r i y) ∧ (¬IsSemiformula LAct n r → y = 0) := by
  by_cases h : IsSemiformula LAct n r
  · obtain ⟨y, hy⟩ := lenFGraph_exists W T h i
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ lenFGraph_unique W T h i y' y hy' hy)
  · simp [h]

/-- **The exact-length producer `lenSteps W T n r i`** (§3.6 "lengths"): the step list which, from the walk
dossier of `r` at offset `i`, derives `lenFact (bnum |r|) (^&(i + shiftsV (lenSteps …)))` — the numeral length
in the graph position; `W` the certification pieces, `T` the `NumSteps` table; `0` off semiformulas. -/
noncomputable def lenSteps (W T n r i : V) : V := Classical.choose! (lenFGraph_existsUnique_total W T n r i)

theorem lenSteps_graph {W T n r i : V} (hr : IsSemiformula LAct n r) : LenFGraph W T n r i (lenSteps W T n r i) :=
  (Classical.choose!_spec (lenFGraph_existsUnique_total W T n r i)).1 hr
theorem lenSteps_of_not {W T n r i : V} (h : ¬IsSemiformula LAct n r) : lenSteps W T n r i = 0 :=
  (Classical.choose!_spec (lenFGraph_existsUnique_total W T n r i)).2 h
lemma lenSteps_eq_of_graph {W T n r i y : V} (hr : IsSemiformula LAct n r) (hy : LenFGraph W T n r i y) :
    lenSteps W T n r i = y :=
  lenFGraph_unique W T hr i _ _ (lenSteps_graph hr) hy

noncomputable def lenStepsDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W T n r i. (!(isSemiformula LAct).pi n r → !lenFGraphDef W T n r i y) ∧ (¬!(isSemiformula LAct).sigma n r → y = 0)”

instance lenSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ lenSteps (v 0) (v 1) (v 2) (v 3) (v 4)) lenStepsDef := .mk
  fun v ↦ by
    simp [lenStepsDef, HierarchySymbol.Semiformula.val_sigma, lenFGraph_defined.iff,
      (IsSemiformula.defined (L := LAct)).proper.iff', (IsSemiformula.defined (L := LAct)).df, lenSteps,
      Classical.choose!_eq_iff_right]
instance lenSteps_definable :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ lenSteps (v 0) (v 1) (v 2) (v 3) (v 4)) lenStepsDef := lenSteps_defined

/-! #### The equations of `lenSteps` -/

variable {W T n : V}

lemma lenSteps_rel {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) (i : V) :
    lenSteps W T n (^rel k R v) i =
      lnAtomSteps W T 142 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1)) :=
  lenSteps_eq_of_graph (by simp [hR, hv]) (LenFGraph.rel_iff.mpr rfl)
lemma lenSteps_nrel {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) (i : V) :
    lenSteps W T n (^nrel k R v) i =
      lnAtomSteps W T 143 k R (listSum (termLenVec LAct k v)) i (shiftsV (lenV W T n k v k (i + 1))) (lenV W T n k v k (i + 1)) :=
  lenSteps_eq_of_graph (by simp [hR, hv]) (LenFGraph.nrel_iff.mpr rfl)
lemma lenSteps_verum (i : V) : lenSteps W T n ^⊤ i = lnConstSteps W 147 i :=
  lenSteps_eq_of_graph (by simp) (LenFGraph.verum_iff.mpr rfl)
lemma lenSteps_falsum (i : V) : lenSteps W T n ^⊥ i = lnConstSteps W 148 i :=
  lenSteps_eq_of_graph (by simp) (LenFGraph.falsum_iff.mpr rfl)
lemma lenSteps_and {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) (i : V) :
    lenSteps W T n (p ^⋏ q) i =
      lnBinSteps W T 149 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i
        (shiftsV (lenSteps W T n q (i + 1))) (shiftsV (lenSteps W T n p (i + descCountF W n q + 1 + shiftsV (lenSteps W T n q (i + 1)))))
        (lenSteps W T n q (i + 1)) (lenSteps W T n p (i + descCountF W n q + 1 + shiftsV (lenSteps W T n q (i + 1)))) :=
  lenSteps_eq_of_graph (by simp [hp, hq]) (LenFGraph.and_iff.mpr ⟨_, _, le_lnBinSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
    le_lnBinSteps_right _ _ _ _ _ _ _ _ _ _ _ _, lenSteps_graph hq, lenSteps_graph hp, rfl⟩)
lemma lenSteps_or {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) (i : V) :
    lenSteps W T n (p ^⋎ q) i =
      lnBinSteps W T 150 n (descCountF W n q) (formulaLen LAct p) (formulaLen LAct q) i
        (shiftsV (lenSteps W T n q (i + 1))) (shiftsV (lenSteps W T n p (i + descCountF W n q + 1 + shiftsV (lenSteps W T n q (i + 1)))))
        (lenSteps W T n q (i + 1)) (lenSteps W T n p (i + descCountF W n q + 1 + shiftsV (lenSteps W T n q (i + 1)))) :=
  lenSteps_eq_of_graph (by simp [hp, hq]) (LenFGraph.or_iff.mpr ⟨_, _, le_lnBinSteps_left _ _ _ _ _ _ _ _ _ _ _ _,
    le_lnBinSteps_right _ _ _ _ _ _ _ _ _ _ _ _, lenSteps_graph hq, lenSteps_graph hp, rfl⟩)
lemma lenSteps_all {p : V} (hp : IsSemiformula LAct (n + 1) p) (i : V) :
    lenSteps W T n (^∀ p) i =
      lnQuantSteps W T 151 n (formulaLen LAct p) i (shiftsV (lenSteps W T (n + 1) p (i + 1))) (lenSteps W T (n + 1) p (i + 1)) :=
  lenSteps_eq_of_graph (by simp [hp]) (LenFGraph.all_iff.mpr ⟨_, le_lnQuantSteps _ _ _ _ _ _ _ _, lenSteps_graph hp, rfl⟩)
lemma lenSteps_exs {p : V} (hp : IsSemiformula LAct (n + 1) p) (i : V) :
    lenSteps W T n (^∃ p) i =
      lnQuantSteps W T 152 n (formulaLen LAct p) i (shiftsV (lenSteps W T (n + 1) p (i + 1))) (lenSteps W T (n + 1) p (i + 1)) :=
  lenSteps_eq_of_graph (by simp [hp]) (LenFGraph.exs_iff.mpr ⟨_, le_lnQuantSteps _ _ _ _ _ _ _ _, lenSteps_graph hp, rfl⟩)

/-- The structural facts of the producer, packaged: `NoDrop'`, `shiftsV + 1 ≤ 2|r|`, `len ≤ 14|r|`. -/
theorem lenSteps_struct {W : V} (hWp : W = certPieces) (T : V) {n r : V} (hr : IsSemiformula LAct n r) (i : V) :
    NoDrop' (lenSteps W T n r i) ∧ shiftsV (lenSteps W T n r i) + 1 ≤ 2 * formulaLen LAct r ∧
    len (lenSteps W T n r i) ≤ 14 * formulaLen LAct r :=
  ⟨(lenFGraph_noDrop_shifts hWp T hr i _ (lenSteps_graph hr)).1, (lenFGraph_noDrop_shifts hWp T hr i _ (lenSteps_graph hr)).2,
    lenFGraph_len W T hr i _ (lenSteps_graph hr)⟩

end lenFFun

/-! ### 5.7 Applicability: the term/vector lists run and leave the numeral length facts -/

section lenOKHelpers

/-- The side conditions of a length pass: the cap `E` bounds the arity part (`13·D` — the numeral sums
`bnum a + bnum b + 1` at `a, b ≤ D`) and the offset part (`5·D` — the eigenvariable indices, which move
with the shifts). -/
def LenPre (D n i E Γ : V) : Prop := 2 * n + 13 * D + 8 ≤ E ∧ i + 5 * D + 2 ≤ E ∧ IsFormulaSet LAct Γ
instance lenPre_definable : 𝚫₁-Relation₅ (LenPre : V → V → V → V → V → Prop) := by
  unfold LenPre; definability
/-- The vector-level side conditions (one more unit of offset room). -/
def LenPreV (D n i E Γ : V) : Prop := 2 * n + 13 * D + 8 ≤ E ∧ i + 5 * D + 3 ≤ E ∧ IsFormulaSet LAct Γ
instance lenPreV_definable : 𝚫₁-Relation₅ (LenPreV : V → V → V → V → V → Prop) := by
  unfold LenPreV; definability
/-- The conclusion: applicable at cap `8`, `neg F` in the final context. -/
def LenPost (tbl E Γ y F : V) : Prop := ListOK tbl E ((8 : ℕ) : V) Γ y ∧ neg LAct F ∈ finalCtx Γ y
instance lenPost_definable : 𝚫₁-Relation₅ (LenPost : V → V → V → V → V → Prop) := by
  unfold LenPost; definability
/-- The vector conclusion: applicable, the length vector's graph fact and its sum fact in the final context. -/
def LenPostV (tbl E Γ y F₁ F₂ : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ y ∧ neg LAct F₁ ∈ finalCtx Γ y ∧ neg LAct F₂ ∈ finalCtx Γ y
instance lenPostV_definable : 𝚫₁.Definable (fun v : Fin 6 → V ↦ LenPostV (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold LenPostV; definability

lemma isSemiterm_bnum_add (a b : V) : IsSemiterm LAct 0 (bnum a ^+ bnum b) := by simp [isSemiterm_bnum_LAct]
lemma isSemiterm_bnum_succ (a : V) : IsSemiterm LAct 0 (bnum a ^+ (𝟏 : V)) := by simp [isSemiterm_bnum_LAct]
lemma isSemiterm_bnum_add_succ (a b : V) : IsSemiterm LAct 0 (bnum a ^+ bnum b ^+ (𝟏 : V)) := by simp [isSemiterm_bnum_LAct]

lemma E_bnum {z D E : V} (hz : z ≤ D) (hE : 6 * D + 1 ≤ E) : termLen LAct (bnum z) ≤ E :=
  le_trans (termLen_bnum_le z)
    (le_trans (add_le_add (mul_le_mul_of_nonneg_left (le_trans (length_le z) hz) zero_le) (le_refl (1 : V))) hE)
lemma E_bnum_add {a b D E : V} (ha : a ≤ D) (hb : b ≤ D) (hE : 12 * D + 3 ≤ E) : termLen LAct (bnum a ^+ bnum b) ≤ E := by
  rw [termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_bnum_LAct 0 a).isUTerm (isSemiterm_bnum_LAct 0 b).isUTerm]
  calc termLen LAct (bnum a) + termLen LAct (bnum b) + 1 ≤ (6 * D + 1) + (6 * D + 1) + 1 :=
        add_le_add (add_le_add (E_bnum ha le_rfl) (E_bnum hb le_rfl)) (le_refl (1 : V))
    _ = 12 * D + 3 := by ring
    _ ≤ E := hE
lemma E_bnum_succ {a D E : V} (ha : a ≤ D) (hE : 6 * D + 3 ≤ E) : termLen LAct (bnum a ^+ (𝟏 : V)) ≤ E := by
  rw [termLen_bnum_add_one]
  calc termLen LAct (bnum a) + 2 ≤ (6 * D + 1) + 2 := add_le_add (E_bnum ha le_rfl) (le_refl (2 : V))
    _ = 6 * D + 3 := by ring
    _ ≤ E := hE
lemma E_bnum_add_succ {a b D E : V} (ha : a ≤ D) (hb : b ≤ D) (hE : 12 * D + 5 ≤ E) :
    termLen LAct (bnum a ^+ bnum b ^+ (𝟏 : V)) ≤ E := by
  rw [termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_bnum_add a b).isUTerm qqOne_uterm_LAct, termLen_qqOne isFunc_LAct_oneIndex]
  calc termLen LAct (bnum a ^+ bnum b) + 1 + 1 ≤ (12 * D + 3) + 1 + 1 :=
        add_le_add (add_le_add (E_bnum_add ha hb le_rfl) (le_refl (1 : V))) (le_refl (1 : V))
    _ = 12 * D + 5 := by ring
    _ ≤ E := hE

/-- The bounds a `LenPre` hands to the witnesses. -/
lemma LenPre.arity {D n i E Γ : V} (h : LenPre D n i E Γ) : 2 * n + 13 * D + 8 ≤ E := h.1
lemma LenPre.off {D n i E Γ : V} (h : LenPre D n i E Γ) : i + 5 * D + 2 ≤ E := h.2.1
lemma LenPre.fset {D n i E Γ : V} (h : LenPre D n i E Γ) : IsFormulaSet LAct Γ := h.2.2
lemma LenPre.arityD {D n i E Γ : V} (h : LenPre D n i E Γ) : 13 * D + 8 ≤ E :=
  le_trans (by rw [add_assoc]; exact le_add_self) h.1
lemma LenPre.eight {D n i E Γ : V} (h : LenPre D n i E Γ) : (8 : V) ≤ E := le_trans le_add_self h.1
lemma LenPre.one {D n i E Γ : V} (h : LenPre D n i E Γ) : (1 : V) ≤ E := le_trans (by norm_num) h.eight
lemma LenPre.eCTVn {D n i E Γ : V} (h : LenPre D n i E Γ) : termLen LAct (cTV n) ≤ E :=
  termLen_cTV_le (le_trans (add_le_add (le_self_add : 2 * n ≤ 2 * n + 13 * D) (by norm_num : (1 : V) ≤ 8)) h.1)
lemma LenPre.eCTVle {D n i E Γ : V} (h : LenPre D n i E Γ) {m : V} (hm : m ≤ D) : termLen LAct (cTV m) ≤ E :=
  termLen_cTV_le (le_trans (add_le_add (le_trans (mul_le_mul_of_nonneg_left hm zero_le)
    (mul_le_mul_of_nonneg_right (by norm_num : (2 : V) ≤ 13) zero_le)) (by norm_num : (1 : V) ≤ 8)) h.arityD)
lemma LenPre.eCTVsmall {D n i E Γ : V} (h : LenPre D n i E Γ) {m : V} (hm : m ≤ 3) : termLen LAct (cTV m) ≤ E :=
  termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left hm zero_le) (le_refl (1 : V)))
    (le_trans (by norm_num) h.eight))
lemma LenPre.eBnum {D n i E Γ : V} (h : LenPre D n i E Γ) {z : V} (hz : z ≤ D) : termLen LAct (bnum z) ≤ E :=
  E_bnum hz (le_trans (add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (6 : V) ≤ 13) zero_le)
    (by norm_num : (1 : V) ≤ 8)) h.arityD)
lemma LenPre.eBnumAdd {D n i E Γ : V} (h : LenPre D n i E Γ) {a b : V} (ha : a ≤ D) (hb : b ≤ D) :
    termLen LAct (bnum a ^+ bnum b) ≤ E :=
  E_bnum_add ha hb (le_trans (add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (12 : V) ≤ 13) zero_le)
    (by norm_num : (3 : V) ≤ 8)) h.arityD)
lemma LenPre.eBnumSucc {D n i E Γ : V} (h : LenPre D n i E Γ) {a : V} (ha : a ≤ D) : termLen LAct (bnum a ^+ (𝟏 : V)) ≤ E :=
  E_bnum_succ ha (le_trans (add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (6 : V) ≤ 13) zero_le)
    (by norm_num : (3 : V) ≤ 8)) h.arityD)
lemma LenPre.eBnumAddSucc {D n i E Γ : V} (h : LenPre D n i E Γ) {a b : V} (ha : a ≤ D) (hb : b ≤ D) :
    termLen LAct (bnum a ^+ bnum b ^+ (𝟏 : V)) ≤ E :=
  E_bnum_add_succ ha hb (le_trans (add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (12 : V) ≤ 13) zero_le)
    (by norm_num : (5 : V) ≤ 8)) h.arityD)
/-- Two offset bounds used at every leaf: `i + 1 ≤ i + 5D + 2` and `i + 1 + 1 ≤ i + 5D + 2`. -/
lemma off_i {i D : V} : i + 1 ≤ i + 5 * D + 2 :=
  le_trans (add_le_add (le_refl i) (by norm_num : (1 : V) ≤ 2)) (add_le_add le_self_add (le_refl (2 : V)))
lemma off_i1 {i D : V} : i + 1 + 1 ≤ i + 5 * D + 2 :=
  le_trans (le_of_eq (show i + 1 + 1 = i + 2 by ring)) (add_le_add le_self_add (le_refl (2 : V)))
/-- An eigenvariable index `m` with `m + 1 ≤ i + 5D + 2` fits. -/
lemma LenPre.eFvar {D n i E Γ : V} (h : LenPre D n i E Γ) {m : V} (hm : m + 1 ≤ i + 5 * D + 2) : termLen LAct (^&m : V) ≤ E :=
  termLen_fvar_le (le_trans hm h.2.1)
lemma LenPre.eVRef {D n i E Γ : V} (h : LenPre D n i E Γ) {c j : V} (hc : c + 1 ≤ i + 5 * D + 2) : termLen LAct (vRef c j) ≤ E :=
  termLen_vRef_le (le_trans hc h.2.1)
lemma LenPre.eFvar0 {D n i E Γ : V} (h : LenPre D n i E Γ) : termLen LAct (^&(0 : V) : V) ≤ E :=
  termLen_fvar_le (by rw [zero_add]; exact h.one)

lemma LenPreV.toPre {D n i E Γ : V} (h : LenPreV D n i E Γ) : LenPre D n i E Γ :=
  ⟨h.1, le_trans (add_le_add (le_refl (i + 5 * D)) (by norm_num)) h.2.1, h.2.2⟩
lemma LenPreV.fset {D n i E Γ : V} (h : LenPreV D n i E Γ) : IsFormulaSet LAct Γ := h.2.2
lemma LenPreV.eFvar {D n i E Γ : V} (h : LenPreV D n i E Γ) {m : V} (hm : m + 1 ≤ i + 5 * D + 3) : termLen LAct (^&m : V) ≤ E :=
  termLen_fvar_le (le_trans hm h.2.1)
lemma LenPreV.eVRef {D n i E Γ : V} (h : LenPreV D n i E Γ) {c j : V} (hc : c + 1 ≤ i + 5 * D + 3) : termLen LAct (vRef c j) ≤ E :=
  termLen_vRef_le (le_trans hc h.2.1)
/-- Replace the context of a `LenPre`/`LenPreV` (the bounds are context-free). -/
lemma LenPre.ctx {D n i E Γ Γ' : V} (h : LenPre D n i E Γ) (hΓ' : IsFormulaSet LAct Γ') : LenPre D n i E Γ' := ⟨h.1, h.2.1, hΓ'⟩
lemma LenPreV.ctx {D n i E Γ Γ' : V} (h : LenPreV D n i E Γ) (hΓ' : IsFormulaSet LAct Γ') : LenPreV D n i E Γ' := ⟨h.1, h.2.1, hΓ'⟩

/-! Transport of the four RESULT fact shapes through a cut-admitting list. -/

lemma tlenFact_transport {Γ S l m : V} (hS : NoDrop' S) (h : neg LAct (tlenFact (bnum l) (^&m)) ∈ Γ) :
    neg LAct (tlenFact (bnum l) (^&(m + shiftsV S))) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_tlenFact (isSemiterm_bnum_LAct 0 l) (by simp)),
    shiftIterV_tlenFact (isSemiterm_bnum_LAct 0 l) (by simp), termShiftIterV_bnum, termShiftIterV_fvar] at this
lemma lenFact_transport {Γ S l m : V} (hS : NoDrop' S) (h : neg LAct (lenFact (bnum l) (^&m)) ∈ Γ) :
    neg LAct (lenFact (bnum l) (^&(m + shiftsV S))) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_lenFact (isSemiterm_bnum_LAct 0 l) (by simp)),
    shiftIterV_lenFact (isSemiterm_bnum_LAct 0 l) (by simp), termShiftIterV_bnum, termShiftIterV_fvar] at this
lemma tlvFact_transport {Γ S m c : V} (hS : NoDrop' S) (h : neg LAct (tlvFact (vRef 0 m) (cTV m) (vRef c m)) ∈ Γ) :
    neg LAct (tlvFact (vRef (shiftsV S) m) (cTV m) (vRef (c + shiftsV S) m)) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_tlvFact (isSemiterm_vRef _ _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _)),
    shiftIterV_tlvFact (isSemiterm_vRef _ _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _),
    termShiftIterV_vRef, termShiftIterV_vRef, termShiftIterV_cTV, zero_add] at this
lemma listSumFact_transport {Γ S σ m : V} (hS : NoDrop' S) (h : neg LAct (listSumFact (bnum σ) (vRef 0 m)) ∈ Γ) :
    neg LAct (listSumFact (bnum σ) (vRef (shiftsV S) m)) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_listSumFact (isSemiterm_bnum_LAct 0 σ) (isSemiterm_vRef _ _)),
    shiftIterV_listSumFact (isSemiterm_bnum_LAct 0 σ) (isSemiterm_vRef _ _), termShiftIterV_bnum, termShiftIterV_vRef,
    zero_add] at this
lemma isFuncFact_transport {Γ S k f : V} (hS : NoDrop' S) (h : neg LAct (isFuncFact (cTV k) (cTV f)) ∈ Γ) :
    neg LAct (isFuncFact (cTV k) (cTV f)) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)),
    shiftIterV_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _), termShiftIterV_cTV, termShiftIterV_cTV] at this

/-- A single intro step as a one-element list: its `shiftsV` is `1`. -/
lemma shiftsV_single_tag2 {s : V} (h : sTag s = 2) : shiftsV (?[s] : V) = 1 := by
  rw [shiftsV_single, if_pos (Or.inl h)]
lemma noDrop'_single_tag2 {s : V} (h : sTag s = 2) : NoDrop' (?[s] : V) := noDrop'_single (noDrop'_tag2 h)

end lenOKHelpers

section lenTOK

/-- The term-level invariant (Π₁ motive): with the dossier at `i`, the list is applicable and leaves
`tlenFact (bnum |t|) &(i + shifts)`. -/
def TLenOK (tbl Wd W T n t : V) : Prop :=
  ∀ i y E Γ : V, LenTGraph W T n t i y → LenPre (termLen LAct t) n i E Γ → DossT Wd Γ n t i →
    LenPost tbl E Γ y (tlenFact (bnum (termLen LAct t)) (^&(i + shiftsV y)))
instance tLenOK_definable : 𝚷₁.Definable (fun v : Fin 6 → V ↦ TLenOK (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold TLenOK LenTGraph; definability

/-- The leaf lists are applicable (`bvar` at row 153 with `termLen_bvar`, `fvar` at 154 with `termLen_fvar`):
the leaf's own shape fact is needed in the SHIFTED context (after `termLenTotal`). -/
lemma lnLeafSteps_ok {tbl N N' B' W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWp : W = certPieces) {n z i E Γ : V} {c : V}
    (hP : LenPre (z + 1) n i E Γ)
    (hfact : (c = 153 ∧ neg LAct (bvarFact (^&(i + 1)) (cTV z)) ∈ setShift LAct Γ) ∨
      (c = 154 ∧ neg LAct (fvarFact (^&(i + 1)) (cTV z)) ∈ setShift LAct Γ)) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnLeafSteps W T c z i) ∧
    neg LAct (tlenFact (bnum (z + 1)) (^&(i + 1))) ∈ finalCtx Γ (lnLeafSteps W T c z i) := by
  have hΓ := hP.fset
  have hi0 : termLen LAct (^&i : V) ≤ E := hP.eFvar off_i
  have hi1 : termLen LAct (^&(i + 1) : V) ≤ E := hP.eFvar off_i1
  have hz : termLen LAct (cTV z) ≤ E := hP.eCTVle le_self_add
  have hz1' : termLen LAct (cTV (z + 1)) ≤ E := hP.eCTVle le_rfl
  have hb : termLen LAct (bnum (z + 1)) ≤ E := hP.eBnum le_rfl
  -- s₁ : termLenTotal [&i]
  obtain ⟨ok₁, _, cx₁⟩ := cok_termLenTotal htbl hC hWp hΓ (wt := ^&i) (by simp) hi0
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (tlenFact (^&(0 : V)) (^&(i + 1)))) (setShift LAct Γ) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hlen₁ : neg LAct (tlenFact (^&(0 : V)) (^&(i + 1))) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  -- s₂ : the leaf row at [cT z, &(i+1), &0]
  have step₂ : StepOK tbl E ((8 : ℕ) : V) Γ₁ (mkStep W c ?[cTV z, ^&(i + 1), ^&0]) ∧
      ctxAfter Γ₁ (mkStep W c ?[cTV z, ^&(i + 1), ^&0]) = insert (neg LAct (eqFactB (^&0) (cTV z ^+ (𝟏 : V)))) Γ₁ := by
    rcases hfact with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
    · obtain ⟨ok, _, cx⟩ := cok_termLenBvar htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 z) hz (by simp) hi1 (by simp) hP.eFvar0
        (by rw [hΓ₁]; exact mem_insert_of_mem' hf) hlen₁
      exact ⟨ok, cx⟩
    · obtain ⟨ok, _, cx⟩ := cok_termLenFvar htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 z) hz (by simp) hi1 (by simp) hP.eFvar0
        (by rw [hΓ₁]; exact mem_insert_of_mem' hf) hlen₁
      exact ⟨ok, cx⟩
  obtain ⟨ok₂, cx₂⟩ := step₂
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (cTV z ^+ (𝟏 : V)))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- s₃ : the closed cT (z+1) = bnum (z+1)
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (cTEqFact (z + 1)) (cTEqCode T (z + 1))) :=
    stepOK_sLemma hΓ₂s (lemmaOK_cTEq htblN (z + 1))
  have cx₃ := ctxAfter_sLemma Γ₂ (cTEqFact (z + 1)) (cTEqCode T (z + 1))
  set Γ₃ := insert (neg LAct (cTEqFact (z + 1))) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- s₄ : eqTrans [&0, cT (z+1), bnum (z+1)]
  obtain ⟨ok₄, _, cx₄⟩ := cok_eqTrans htbl hC hWp hΓ₃s (by simp) hP.eFvar0 (cTV_semiterm_LAct 0 _) hz1' (isSemiterm_bnum_LAct 0 _) hb
    (by rw [hΓ₃, hΓ₂, cTV_succ]; exact mem_insert_of_mem' mem_insert_self')
    (by rw [hΓ₃]; exact mem_insert_self')
  set Γ₄ := insert (neg LAct (eqFactB (^&0) (bnum (z + 1)))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- s₅ : congTLenNum [&(i+1), &0, bnum (z+1)]
  obtain ⟨ok₅, _, cx₅⟩ := cok_congTLenNum htbl hC hWp hΓ₄s (by simp) hi1 (by simp) hP.eFvar0 (isSemiterm_bnum_LAct 0 _) hb
    (by rw [hΓ₄]; exact mem_insert_self')
    (by rw [hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hlen₁)))
  refine ⟨?_, ?_⟩
  · rw [lnLeafSteps]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    exact listOK_single ok₅
  · rw [lnLeafSteps, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_single, cx₅]
    exact mem_insert_self'


/-- The tails of the vector/function lists, named (definitional unfoldings of the builders). -/
noncomputable def lnAdjTail (W T n m ct lt σ' i st sv : V) : V :=
  ?[mkStep W 17 ?[bnum lt, vRef 0 m],
    mkStep W 38 ?[cTV m, cTV n, vRef (i + 1 + ct + (st + sv + 1)) m],
    mkStep W 39 ?[cTV m, vRef (i + 1 + ct + (st + sv + 1)) m],
    mkStep W 139 ?[cTV n, cTV m, vRef (i + 1 + ct + (st + sv + 1)) m, ^&(i + (st + sv + 1)), ^&(i + 1 + (st + sv + 1)),
      bnum lt, vRef 1 m, ^&0],
    sLemma (addFact lt σ') (addCode T lt σ'),
    mkStep W 185 ?[^&0, vRef 1 m, bnum lt, bnum σ', bnum (lt + σ')]]
lemma lnAdjSteps_eq (W T n m ct lt σ' i st sv yt yv : V) :
    lnAdjSteps W T n m ct lt σ' i st sv yt yv = appendV yt (appendV yv (lnAdjTail W T n m ct lt σ' i st sv)) := rfl
noncomputable def lnFuncTail (W T k f σ i sv : V) : V :=
  ?[mkStep W (funcRow k f) 0,
    mkStep W 156 ?[^&(i + sv)],
    mkStep W 144 ?[cTV k, cTV f, vRef (i + 1 + sv + 1) k, ^&(i + sv + 1), vRef 1 k, bnum σ, ^&0],
    sLemma (succFact σ) (succCode T σ),
    mkStep W 123 ?[^&0, bnum σ ^+ (𝟏 : V), bnum (σ + 1)],
    mkStep W 146 ?[^&(i + sv + 1), ^&0, bnum (σ + 1)]]
lemma lnFuncSteps_eq (W T k f σ i sv yv : V) : lnFuncSteps W T k f σ i sv yv = appendV yv (lnFuncTail W T k f σ i sv) := rfl

/-- The empty vector's list is applicable and leaves `tlvFact 𝟎 (cT 0) 𝟎`, `listSumFact (bnum 0) 𝟎`. -/
lemma lnNilSteps_ok {tbl N W : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (hWp : W = certPieces) {E Γ : V}
    (h8 : (8 : V) ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnNilSteps W) ∧
    neg LAct (tlvFact (vRef 0 0) (cTV 0) (vRef 0 0)) ∈ finalCtx Γ (lnNilSteps W) ∧
    neg LAct (listSumFact (bnum 0) (vRef 0 0)) ∈ finalCtx Γ (lnNilSteps W) := by
  have hc0 : termLen LAct (cTV 0) ≤ E := E_cT_le_two (by norm_num) h8
  obtain ⟨ok₁, _, cx₁⟩ := cok_termLenVecNil htbl hC hWp hΓ (wx := cTV 0) (cTV_semiterm_LAct 0 0) hc0
  have hΓ₁ : IsFormulaSet LAct (insert (neg LAct (tlvFact (𝟎 : V) (𝟎 : V) (𝟎 : V))) Γ) := by
    rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  obtain ⟨ok₂, _, cx₂⟩ := cok_listSumNil htbl hC hWp hΓ₁ (wx := cTV 0) (cTV_semiterm_LAct 0 0) hc0
  refine ⟨?_, ?_, ?_⟩
  · rw [lnNilSteps]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    exact listOK_single ok₂
  · rw [lnNilSteps, finalCtx_cons, cx₁, finalCtx_single, cx₂, vRef_zero, cTV_zero]
    exact mem_insert_of_mem' mem_insert_self'
  · rw [lnNilSteps, finalCtx_cons, cx₁, finalCtx_single, cx₂, vRef_zero, bnum_zero]
    exact mem_insert_self'

/-- The walk's `adjoinTotal` (row 17) and the two `utvPi` bridge rows (38/39), read from the certification pieces. -/
lemma mkStep_certPieces_17 {W : V} (hWp : W = certPieces) (ev : V) : mkStep W 17 ev = mkStep walkPieces 17 ev := by
  rw [hWp, show (17 : V) = ((17 : ℕ) : V) by simp, mkStep_certPieces_lt 17 (by decide)]

set_option maxHeartbeats 2000000 in
/-- **The adjoin tail is applicable**: in the context after the entry's and the tail's lists (their result
facts at the shifted offsets, the parent vector's dossier transported to `i + st + sv`), it leaves the new
length vector `&0` with `tlvFact &0 (cT m + 1) &(i + S)` and `listSumFact (bnum (lt + σ')) &0`. -/
lemma lnAdjTail_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {n k v m i E Γ : V} (hv : IsSemitermVec LAct k n v) (hm : m + 1 ≤ k) (hk : k ≤ 2)
    {ct lt σ' st sv : V} (hct : ct = descCountT Wd n v.[k - (m + 1)]) (hlt : lt = termLen LAct v.[k - (m + 1)])
    (hct_le : ct + 1 ≤ 2 * lt) (hst : st + 1 ≤ 2 * lt) (hsv : sv ≤ 2 * σ')
    (hP : LenPreV (lt + σ') n i E Γ)
    (hT : neg LAct (tlenFact (bnum lt) (^&(i + 1 + st + sv))) ∈ Γ)
    (hM : neg LAct (tlvFact (vRef 0 m) (cTV m) (vRef (i + 1 + ct + st + sv) m)) ∈ Γ)
    (hSum : neg LAct (listSumFact (bnum σ') (vRef 0 m)) ∈ Γ)
    (hD : DossV Wd Γ n k v (m + 1) (i + st + sv)) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnAdjTail W T n m ct lt σ' i st sv) ∧
    neg LAct (tlvFact (^&0) (cTV m ^+ (𝟏 : V)) (^&(i + (st + sv + 1)))) ∈ finalCtx Γ (lnAdjTail W T n m ct lt σ' i st sv) ∧
    neg LAct (listSumFact (bnum (lt + σ')) (^&0)) ∈ finalCtx Γ (lnAdjTail W T n m ct lt σ' i st sv) := by
  have hW : WalkTable tbl := hC.walkTable
  have hΓ := hP.fset
  have hmk : m ≤ k := le_trans le_self_add hm
  have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
  have hlt' : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt'
  set S := st + sv + 1 with hS
  -- the witness bounds
  have hD1 : lt ≤ lt + σ' := le_self_add
  have hD2 : σ' ≤ lt + σ' := le_add_self
  have hbt : termLen LAct (bnum lt) ≤ E := hP.toPre.eBnum hD1
  have hbσ : termLen LAct (bnum σ') ≤ E := hP.toPre.eBnum hD2
  have hbs : termLen LAct (bnum (lt + σ')) ≤ E := hP.toPre.eBnum le_rfl
  have hcm : termLen LAct (cTV m) ≤ E := hP.toPre.eCTVsmall (le_trans hmk (le_trans hk (by norm_num)))
  have hcn : termLen LAct (cTV n) ≤ E := hP.toPre.eCTVn
  have hr0 : termLen LAct (vRef 0 m) ≤ E := termLen_vRef_le (by rw [zero_add]; exact hP.toPre.one)
  have hr1 : termLen LAct (vRef 1 m) ≤ E := termLen_vRef_le (le_trans (by norm_num) hP.toPre.eight)
  have hctle : ct ≤ 2 * lt := le_trans le_self_add hct_le
  have hSle : S ≤ 2 * lt + 2 * σ' := by
    rw [hS]
    calc st + sv + 1 = (st + 1) + sv := by ring
      _ ≤ 2 * lt + 2 * σ' := add_le_add hst hsv
  have hoff : i + 1 + ct + S + 1 ≤ i + 5 * (lt + σ') + 3 :=
    calc i + 1 + ct + S + 1 ≤ i + 1 + 2 * lt + (2 * lt + 2 * σ') + 1 :=
          add_le_add (add_le_add (add_le_add (le_refl (i + 1)) hctle) hSle) (le_refl (1 : V))
      _ = i + (4 * lt + 2 * σ' + 2) := by ring
      _ ≤ i + (4 * lt + 2 * σ' + 2 + (lt + 3 * σ' + 1)) := add_le_add (le_refl i) le_self_add
      _ = i + 5 * (lt + σ') + 3 := by ring
  have hrt : termLen LAct (vRef (i + 1 + ct + S) m) ≤ E := hP.eVRef hoff
  have hfS : termLen LAct (^&(i + S) : V) ≤ E := hP.eFvar
    (calc i + S + 1 ≤ i + S + 1 + (1 + ct) := le_self_add
      _ = i + 1 + ct + S + 1 := by ring
      _ ≤ i + 5 * (lt + σ') + 3 := hoff)
  have hf1S : termLen LAct (^&(i + 1 + S) : V) ≤ E := hP.eFvar
    (calc i + 1 + S + 1 ≤ i + 1 + S + 1 + ct := le_self_add
      _ = i + 1 + ct + S + 1 := by ring
      _ ≤ i + 5 * (lt + σ') + 3 := hoff)
  -- s₁ : adjoinTotal [bnum lt, ⟨M⟩]  (walk row 17)
  have er := mkStep_certPieces_17 hWp (?[bnum lt, vRef 0 m] : V)
  obtain ⟨ok₁, tag₁, cx₁⟩ := ok_adjoinTotal htbl hW rfl hΓ (isSemiterm_bnum_LAct 0 lt) hbt (isSemiterm_vRef 0 m) hr0
  rw [← er] at ok₁ tag₁ cx₁
  rw [termShift_bnum, termShift_vRef, zero_add, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (adjFact (^&(0 : V)) (bnum lt) (vRef 1 m))) (setShift LAct Γ) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hnd₁ : NoDrop' (?[mkStep W 17 ?[bnum lt, vRef 0 m]] : V) := noDrop'_single_tag2 tag₁
  have hs₁ : shiftsV (?[mkStep W 17 ?[bnum lt, vRef 0 m]] : V) = 1 := shiftsV_single_tag2 tag₁
  -- the transported facts and dossier
  have hT₁ : neg LAct (tlenFact (bnum lt) (^&(i + 1 + S))) ∈ Γ₁ := by
    have := tlenFact_transport hnd₁ hT
    rwa [hs₁, finalCtx_single, cx₁, show i + 1 + st + sv + 1 = i + 1 + S by rw [hS]; ring] at this
  have hM₁ : neg LAct (tlvFact (vRef 1 m) (cTV m) (vRef (i + 1 + ct + S) m)) ∈ Γ₁ := by
    have := tlvFact_transport hnd₁ hM
    rwa [hs₁, finalCtx_single, cx₁, show i + 1 + ct + st + sv + 1 = i + 1 + ct + S by rw [hS]; ring] at this
  have hSum₁ : neg LAct (listSumFact (bnum σ') (vRef 1 m)) ∈ Γ₁ := by
    have := listSumFact_transport hnd₁ hSum
    rwa [hs₁, finalCtx_single, cx₁] at this
  have hadjM : neg LAct (adjFact (^&(0 : V)) (bnum lt) (vRef 1 m)) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  have hD₁ : DossV Wd Γ₁ n k v (m + 1) (i + S) := by
    have := dossV_transport' hnd₁ hD
    rwa [hs₁, finalCtx_single, cx₁, show i + st + sv + 1 = i + S by rw [hS]; ring] at this
  obtain ⟨hadj, htvP, hDt, hDv⟩ := dossV_succ htbl hW hWd hv hm hD₁
  rw [← hct] at hadj hDv
  rw [show i + S + 1 = i + 1 + S by ring] at hadj hDt
  rw [show i + 1 + S + ct = i + 1 + ct + S by ring] at hadj
  rw [show i + S + 1 + ct = i + 1 + ct + S by ring] at hDv
  have htPi : neg LAct (tPiFact (cTV n) (^&(i + 1 + S))) ∈ Γ₁ := dossT_tPi htbl hW hWd ht hDt
  have htv : neg LAct (tvPiFact (cTV m) (cTV n) (vRef (i + 1 + ct + S) m)) ∈ Γ₁ := dossV_tvPi htbl hW hWd hv hmk hDv
  -- s₂ : row 38 on the tail
  have er₂ : mkStep W 38 (?[cTV m, cTV n, vRef (i + 1 + ct + S) m] : V) = mkStep walkPieces 38 ?[cTV m, cTV n, vRef (i + 1 + ct + S) m] := by
    rw [hWp, mkStep_certPieces_38]
  obtain ⟨ok₂, _, cx₂⟩ := ok_isUTermVecOfSemitermVecLAct htbl hW rfl hΓ₁s (cTV_semiterm_LAct 0 _) hcm (cTV_semiterm_LAct 0 _) hcn
    (isSemiterm_vRef _ _) hrt htv
  rw [← er₂] at ok₂ cx₂
  set Γ₂ := insert (neg LAct (utvSigmaFact (cTV m) (vRef (i + 1 + ct + S) m))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- s₃ : row 39
  have er₃ : mkStep W 39 (?[cTV m, vRef (i + 1 + ct + S) m] : V) = mkStep walkPieces 39 ?[cTV m, vRef (i + 1 + ct + S) m] := by
    rw [hWp, mkStep_certPieces_39]
  obtain ⟨ok₃, _, cx₃⟩ := ok_isUTermVecSigmaPiLAct htbl hW rfl hΓ₂s (cTV_semiterm_LAct 0 _) hcm (isSemiterm_vRef _ _) hrt
    (by rw [hΓ₂]; exact mem_insert_self')
  rw [← er₃] at ok₃ cx₃
  set Γ₃ := insert (neg LAct (utvPiFact (cTV m) (vRef (i + 1 + ct + S) m))) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- s₄ : termLenVecAdj
  obtain ⟨ok₄, _, cx₄⟩ := cok_termLenVecAdj htbl hC hWp hΓ₃s (cTV_semiterm_LAct 0 _) hcn (cTV_semiterm_LAct 0 _) hcm
    (isSemiterm_vRef _ _) hrt (by simp) hfS (by simp) hf1S (isSemiterm_bnum_LAct 0 _) hbt (isSemiterm_vRef _ _) hr1 (by simp) hP.toPre.eFvar0
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' htPi))
    (by rw [hΓ₃]; exact mem_insert_self')
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' hT₁))
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' hM₁))
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' hadj))
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' hadjM))
  set Γ₄ := insert (neg LAct (tlvFact (^&0) (cTV m ^+ (𝟏 : V)) (^&(i + S)))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- s₅ : the closed addFact
  have ok₅ : StepOK tbl E ((8 : ℕ) : V) Γ₄ (sLemma (addFact lt σ') (addCode T lt σ')) :=
    stepOK_sLemma hΓ₄s (lemmaOK_add htblN lt σ')
  have cx₅ := ctxAfter_sLemma Γ₄ (addFact lt σ') (addCode T lt σ')
  set Γ₅ := insert (neg LAct (addFact lt σ')) Γ₄ with hΓ₅
  have hΓ₅s : IsFormulaSet LAct Γ₅ := by rw [← cx₅]; exact isFormulaSet_ctxAfter 8 htbl ok₅
  -- s₆ : listSumAdjI [&0, ⟨M⟩, bnum lt, bnum σ', bnum (lt + σ')]
  obtain ⟨ok₆, _, cx₆⟩ := cok_listSumAdjI htbl hC hWp hΓ₅s (by simp) hP.toPre.eFvar0 (isSemiterm_vRef _ _) hr1
    (isSemiterm_bnum_LAct 0 _) hbt (isSemiterm_bnum_LAct 0 _) hbσ (isSemiterm_bnum_LAct 0 _) hbs
    (by rw [hΓ₅, hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hSum₁))))
    (by rw [hΓ₅, hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hadjM))))
    (by rw [hΓ₅]; exact mem_insert_self')
  refine ⟨?_, ?_, ?_⟩
  · rw [lnAdjTail]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    refine listOK_cons ok₅ ?_
    rw [cx₅]
    exact listOK_single ok₆
  · rw [lnAdjTail, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_cons, cx₅,
      finalCtx_single, cx₆]
    exact mem_insert_of_mem' (mem_insert_of_mem' mem_insert_self')
  · rw [lnAdjTail, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_cons, cx₅,
      finalCtx_single, cx₆]
    exact mem_insert_self'


/-- A leaf's shape fact, moved into the shifted context (after the node's `termLenTotal`). -/
lemma bvarFact_setShift {Γ i z : V} (h : neg LAct (bvarFact (^&i) (cTV z)) ∈ Γ) :
    neg LAct (bvarFact (^&(i + 1)) (cTV z)) ∈ setShift LAct Γ := by
  have := mem_setShift_of_mem h
  rwa [← shiftIterV_one, shiftIterV_neg (isFormula_bvarFact (by simp) (cTV_semiterm_LAct 0 _)),
    shiftIterV_bvarFact (by simp) (cTV_semiterm_LAct 0 _), termShiftIterV_fvar, termShiftIterV_cTV] at this
lemma fvarFact_setShift {Γ i z : V} (h : neg LAct (fvarFact (^&i) (cTV z)) ∈ Γ) :
    neg LAct (fvarFact (^&(i + 1)) (cTV z)) ∈ setShift LAct Γ := by
  have := mem_setShift_of_mem h
  rwa [← shiftIterV_one, shiftIterV_neg (isFormula_fvarFact (by simp) (cTV_semiterm_LAct 0 _)),
    shiftIterV_fvarFact (by simp) (cTV_semiterm_LAct 0 _), termShiftIterV_fvar, termShiftIterV_cTV] at this

lemma subset_insert' {x Γ : V} : Γ ⊆ insert x Γ := fun _ h ↦ mem_insert_of_mem' h

set_option maxHeartbeats 2000000 in
/-- **The function tail is applicable**: after the vector's list (its two result facts, the node's dossier
transported to `i + sv`), it leaves `tlenFact (bnum (σ + 1)) &(i + sv + 1)`. -/
lemma lnFuncTail_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {n k f v i E Γ : V} (hkf : LAct.IsFunc k f) (hv : IsSemitermVec LAct k n v)
    {σ sv : V} (hσ : σ = listSum (termLenVec LAct k v)) (hsv : sv ≤ 2 * σ) (hP : LenPre (σ + 1) n i E Γ)
    (hM : neg LAct (tlvFact (vRef 0 k) (cTV k) (vRef (i + 1 + sv) k)) ∈ Γ)
    (hSum : neg LAct (listSumFact (bnum σ) (vRef 0 k)) ∈ Γ)
    (hD : DossT Wd Γ n (^func k f v) (i + sv)) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnFuncTail W T k f σ i sv) ∧
    neg LAct (tlenFact (bnum (σ + 1)) (^&(i + sv + 1))) ∈ finalCtx Γ (lnFuncTail W T k f σ i sv) := by
  have hW : WalkTable tbl := hC.walkTable
  have hΓ := hP.fset
  -- witness bounds
  have hbσ : termLen LAct (bnum σ) ≤ E := hP.eBnum le_self_add
  have hbσ1 : termLen LAct (bnum (σ + 1)) ≤ E := hP.eBnum le_rfl
  have hbs : termLen LAct (bnum σ ^+ (𝟏 : V)) ≤ E := hP.eBnumSucc le_self_add
  have hr1 : termLen LAct (vRef 1 k) ≤ E := termLen_vRef_le (le_trans (by norm_num) hP.eight)
  have hoff : i + 1 + sv + 1 + 1 ≤ i + 5 * (σ + 1) + 2 :=
    calc i + 1 + sv + 1 + 1 ≤ i + 1 + 2 * σ + 1 + 1 := add_le_add (add_le_add (add_le_add (le_refl _) hsv) (le_refl _)) (le_refl _)
      _ = i + (2 * σ + 3) := by ring
      _ ≤ i + (2 * σ + 3 + (3 * σ + 4)) := add_le_add (le_refl i) le_self_add
      _ = i + 5 * (σ + 1) + 2 := by ring
  have hrv : termLen LAct (vRef (i + 1 + sv + 1) k) ≤ E := hP.eVRef hoff
  have hfsv : termLen LAct (^&(i + sv) : V) ≤ E := hP.eFvar
    (calc i + sv + 1 ≤ i + sv + 1 + 2 := le_self_add
      _ = i + 1 + sv + 1 + 1 := by ring
      _ ≤ i + 5 * (σ + 1) + 2 := hoff)
  have hfsv1 : termLen LAct (^&(i + sv + 1) : V) ≤ E := hP.eFvar
    (calc i + sv + 1 + 1 ≤ i + sv + 1 + 1 + 1 := le_self_add
      _ = i + 1 + sv + 1 + 1 := by ring
      _ ≤ i + 5 * (σ + 1) + 2 := hoff)
  -- s₀ : the closed symbol row
  have er₀ : mkStep W (funcRow k f) 0 = mkStep walkPieces (funcRow k f) 0 := by rw [hWp, mkStep_certPieces_funcRow]
  obtain ⟨ok₀, _, cx₀, hEk, hEf⟩ := funcConst_ok htbl hW rfl hkf hP.eight hΓ
  rw [← er₀] at ok₀ cx₀
  set Γ₀ := insert (neg LAct (isFuncFact (cTV k) (cTV f))) Γ with hΓ₀
  have hΓ₀s : IsFormulaSet LAct Γ₀ := by rw [← cx₀]; exact isFormulaSet_ctxAfter 8 htbl ok₀
  -- s₁ : termLenTotal [&(i + sv)]
  obtain ⟨ok₁, tag₁, cx₁⟩ := cok_termLenTotal htbl hC hWp hΓ₀s (wt := ^&(i + sv)) (by simp) hfsv
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (tlenFact (^&(0 : V)) (^&(i + sv + 1)))) (setShift LAct Γ₀) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hnd₁ : NoDrop' (?[mkStep W 156 ?[^&(i + sv)]] : V) := noDrop'_single_tag2 tag₁
  have hs₁ : shiftsV (?[mkStep W 156 ?[^&(i + sv)]] : V) = 1 := shiftsV_single_tag2 tag₁
  have hlen₁ : neg LAct (tlenFact (^&(0 : V)) (^&(i + sv + 1))) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  have hM₁ : neg LAct (tlvFact (vRef 1 k) (cTV k) (vRef (i + 1 + sv + 1) k)) ∈ Γ₁ := by
    have := tlvFact_transport hnd₁ (mem_insert_of_mem' hM : _ ∈ Γ₀)
    rwa [hs₁, finalCtx_single, cx₁] at this
  have hSum₁ : neg LAct (listSumFact (bnum σ) (vRef 1 k)) ∈ Γ₁ := by
    have := listSumFact_transport hnd₁ (mem_insert_of_mem' hSum : _ ∈ Γ₀)
    rwa [hs₁, finalCtx_single, cx₁] at this
  have hisF₁ : neg LAct (isFuncFact (cTV k) (cTV f)) ∈ Γ₁ := by
    have := isFuncFact_transport hnd₁ (mem_insert_self' : _ ∈ Γ₀)
    rwa [finalCtx_single, cx₁] at this
  have hD₁ : DossT Wd Γ₁ n (^func k f v) (i + sv + 1) := by
    have := dossT_transport' hnd₁ (hD.mono (subset_insert' : Γ ⊆ Γ₀))
    rwa [hs₁, finalCtx_single, cx₁] at this
  obtain ⟨hfF, htPi, hutv, _⟩ := dossT_func htbl hW hWd hkf hv hD₁
  rw [show i + sv + 1 + 1 = i + 1 + sv + 1 by ring] at hfF hutv
  -- s₂ : termLenFuncCert [cT k, cT f, ⟨v⟩, &(i+sv+1), ⟨M⟩, bnum σ, &0]
  obtain ⟨ok₂, _, cx₂⟩ := cok_termLenFuncCert htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hEf
    (isSemiterm_vRef _ _) hrv (by simp) hfsv1 (isSemiterm_vRef _ _) hr1 (isSemiterm_bnum_LAct 0 _) hbσ (by simp) hP.eFvar0
    hisF₁ hutv hfF hM₁ hSum₁ hlen₁
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (bnum σ ^+ (𝟏 : V)))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- s₃ : the closed succFact
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (succFact σ) (succCode T σ)) := stepOK_sLemma hΓ₂s (lemmaOK_succ htblN σ)
  have cx₃ := ctxAfter_sLemma Γ₂ (succFact σ) (succCode T σ)
  set Γ₃ := insert (neg LAct (succFact σ)) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- s₄ : eqTrans [&0, bnum σ + 1, bnum (σ+1)]
  obtain ⟨ok₄, _, cx₄⟩ := cok_eqTrans htbl hC hWp hΓ₃s (by simp) hP.eFvar0 (isSemiterm_bnum_succ σ) hbs (isSemiterm_bnum_LAct 0 _) hbσ1
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' mem_insert_self')
    (by rw [hΓ₃]; exact mem_insert_self')
  set Γ₄ := insert (neg LAct (eqFactB (^&0) (bnum (σ + 1)))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- s₅ : congTLenNum [&(i+sv+1), &0, bnum (σ+1)]
  obtain ⟨ok₅, _, cx₅⟩ := cok_congTLenNum htbl hC hWp hΓ₄s (by simp) hfsv1 (by simp) hP.eFvar0 (isSemiterm_bnum_LAct 0 _) hbσ1
    (by rw [hΓ₄]; exact mem_insert_self')
    (by rw [hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hlen₁)))
  refine ⟨?_, ?_⟩
  · rw [lnFuncTail]
    refine listOK_cons ok₀ ?_
    rw [cx₀]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    exact listOK_single ok₅
  · rw [lnFuncTail, finalCtx_cons, cx₀, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄,
      finalCtx_single, cx₅]
    exact mem_insert_self'

set_option maxHeartbeats 4000000 in
/-- **The vector-level length lists are applicable** (entries' invariant as a hypothesis, the
`descVecAux_ok` pattern): for the last `m` entries at `i` they leave the length vector at `&0` with
`tlvFact ⟨M⟩ (cT m) ⟨v⟩` and `listSumFact (bnum Σ) ⟨M⟩`. -/
lemma lenVGraph_ok_aux {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (n : V) {k v : V} (hk : k ≤ 2) (hv : IsSemitermVec LAct k n v)
    (ih : ∀ a < k, TLenOK tbl Wd W T n v.[a]) :
    ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ ∀ i z E Γ : V, LenVGraph W T n k v m i z →
      LenPreV (listSum (termLenVec LAct m (takeLast v m))) n i E Γ → DossV Wd Γ n k v m i →
      LenPostV tbl E Γ z (tlvFact (vRef 0 m) (cTV m) (vRef (i + shiftsV z) m))
        (listSumFact (bnum (listSum (termLenVec LAct m (takeLast v m)))) (vRef 0 m)) := by
  have hW : WalkTable tbl := hC.walkTable
  have hvlen : len v = k := hv.lh
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => simp only [LenVGraph]; definability
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i z E Γ hz hP hD
    rw [LenVGraph.zero_iff.mp hz, (lnNilSteps_struct hWp).2, add_zero]
    obtain ⟨ok, h1, h2⟩ := lnNilSteps_ok htbl hC hWp hP.toPre.eight hP.fset
    refine ⟨ok, ?_, ?_⟩
    · simpa [vRef_zero] using h1
    · simpa using h2
  | succ m ihm =>
    intro hm
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    have hmk : m ≤ k := le_trans le_self_add hm
    obtain ⟨hU, hrest⟩ := ihm hmk
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    intro i z E Γ hz hP hD
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    rw [hnth'] at hyt hyv ⊢
    rw [htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hP ⊢
    set ct := descCountT W n v.[k - (m + 1)] with hct'
    set lt := termLen LAct v.[k - (m + 1)] with hlt'
    set σ' := listSum (termLenVec LAct m (takeLast v m)) with hσ'
    have hct : ct = descCountT Wd n v.[k - (m + 1)] := by rw [hct', hWp, hWd]; exact descCountT_certPieces n _ ht
    have hct_le : ct + 1 ≤ 2 * lt := by rw [hct]; exact descCountT_walk_le htbl hW hWd ht
    obtain ⟨hndT, hsT⟩ := lenTGraph_noDrop_shifts hWp T n _ ht (i + 1) yt hyt
    obtain ⟨hndV, hsV⟩ := lenVGraph_noDrop_shifts hWp T n hv m hmk _ yv hyv
    -- the entry's list
    have hPt : LenPre lt n (i + 1) E Γ :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left le_self_add zero_le)) (le_refl 8)) hP.1,
       le_trans (le_of_eq (show i + 1 + 5 * lt + 2 = i + 5 * lt + 3 by ring))
         (le_trans (add_le_add (add_le_add (le_refl i) (mul_le_mul_of_nonneg_left le_self_add zero_le)) (le_refl 3)) hP.2.1),
       hP.fset⟩
    obtain ⟨hadjD, _, hDt, hDv⟩ := dossV_succ htbl hW hWd hv hm hD
    have hih := ih _ hlt
    unfold TLenOK at hih
    obtain ⟨okT, hfT⟩ := hih (i + 1) yt E Γ hyt hPt hDt
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yt) := finalCtx_isFormulaSet 8 htbl hP.fset okT
    -- the tail's list
    have hDv₁ : DossV Wd (finalCtx Γ yt) n k v m (i + 1 + ct + shiftsV yt) := by
      have := dossV_transport' hndT hDv
      rwa [← hct] at this
    have h4 : 1 + ct + shiftsV yt + 1 ≤ 4 * lt := by
      calc 1 + ct + shiftsV yt + 1 = (ct + 1) + (shiftsV yt + 1) := by ring
        _ ≤ 2 * lt + 2 * lt := add_le_add hct_le hsT
        _ = 4 * lt := by ring
    have hoffV : i + 1 + ct + shiftsV yt + 5 * σ' + 3 ≤ E :=
      calc i + 1 + ct + shiftsV yt + 5 * σ' + 3 = i + (1 + ct + shiftsV yt) + 5 * σ' + 3 := by ring
        _ ≤ i + 4 * lt + 5 * σ' + 3 :=
            add_le_add (add_le_add (add_le_add (le_refl i) (le_trans le_self_add h4)) (le_refl (5 * σ'))) (le_refl (3 : V))
        _ ≤ i + 5 * lt + 5 * σ' + 3 :=
            add_le_add (add_le_add (add_le_add (le_refl i) (mul_le_mul_of_nonneg_right (by norm_num : (4 : V) ≤ 5) zero_le))
              (le_refl (5 * σ'))) (le_refl (3 : V))
        _ = i + 5 * (lt + σ') + 3 := by ring
        _ ≤ E := hP.2.1
    have hPv : LenPreV σ' n (i + 1 + ct + shiftsV yt) E (finalCtx Γ yt) :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left le_add_self zero_le)) (le_refl 8)) hP.1,
       hoffV, hΓ₁⟩
    obtain ⟨okV, hM, hSum⟩ := hrest _ yv E _ hyv hPv hDv₁
    have hΓ₂ : IsFormulaSet LAct (finalCtx (finalCtx Γ yt) yv) := finalCtx_isFormulaSet 8 htbl hΓ₁ okV
    have hT₂ : neg LAct (tlenFact (bnum lt) (^&(i + 1 + shiftsV yt + shiftsV yv))) ∈ finalCtx (finalCtx Γ yt) yv :=
      tlenFact_transport hndV hfT
    have hD₂ : DossV Wd (finalCtx (finalCtx Γ yt) yv) n k v (m + 1) (i + shiftsV yt + shiftsV yv) :=
      dossV_transport' hndV (dossV_transport' hndT hD)
    have hPv' : LenPreV (lt + σ') n i E (finalCtx (finalCtx Γ yt) yv) := hP.ctx hΓ₂
    obtain ⟨okTail, hres1, hres2⟩ := lnAdjTail_ok htbl hC htblN hWd hWp hv hm hk hct hlt' hct_le hsT hsV hPv' hT₂ hM hSum hD₂
    obtain ⟨_, hsh⟩ := lnAdjSteps_struct hWp T n m ct lt σ' i (shiftsV yt) (shiftsV yv) yt yv hndT hndV
    refine ⟨?_, ?_, ?_⟩
    · rw [lnAdjSteps_eq]; exact listOK_appendV okT (listOK_appendV okV okTail)
    · rw [hsh, lnAdjSteps_eq, finalCtx_appendV, finalCtx_appendV, vRef_of_ne (succ_ne_zero' m), vRef_of_ne (succ_ne_zero' m),
        cTV_succ, show i + (shiftsV yt + (shiftsV yv + 1)) = i + (shiftsV yt + shiftsV yv + 1) by ring]
      exact hres1
    · rw [lnAdjSteps_eq, finalCtx_appendV, finalCtx_appendV, vRef_of_ne (succ_ne_zero' m)]
      exact hres2

set_option maxHeartbeats 4000000 in
/-- **The term-level length lists are applicable** (with the vector level as the inner induction). -/
theorem lenTGraph_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) (n : V) : ∀ t, IsSemiterm LAct n t → TLenOK tbl Wd W T n t := by
  have hW : WalkTable tbl := hC.walkTable
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · unfold TLenOK LenTGraph; definability
  · -- bvar
    intro z _ i y E Γ hy hP hD
    rw [LenTGraph.bvar_iff.mp hy, (lnLeafSteps_struct hWp (Or.inl rfl) T z i).2]
    rw [termLen_bvar] at hP ⊢
    obtain ⟨hb, _⟩ := dossT_bvar htbl hW hWd hD
    exact lnLeafSteps_ok htbl hC htblN hWp hP (Or.inl ⟨rfl, bvarFact_setShift hb⟩)
  · -- fvar
    intro a i y E Γ hy hP hD
    rw [LenTGraph.fvar_iff.mp hy, (lnLeafSteps_struct hWp (Or.inr rfl) T a i).2]
    rw [termLen_fvar] at hP ⊢
    obtain ⟨hb, _⟩ := dossT_fvar htbl hW hWd hD
    exact lnLeafSteps_ok htbl hC htblN hWp hP (Or.inr ⟨rfl, fvarFact_setShift hb⟩)
  · -- func
    intro k f v hkf hv ih i y E Γ hy hP hD
    have hk : k ≤ 2 := arity_le_two hkf
    have hvlen : len v = k := hv.lh
    have key := lenVGraph_ok_aux htbl hC htblN hWd hWp n hk hv ih
    -- the function node
    obtain ⟨yv, _, hyv, rfl⟩ := LenTGraph.func_iff.mp hy
    have htl : takeLast v k = v := by rw [← hvlen]; exact takeLast_len_self v
    obtain ⟨_, hrest⟩ := key k le_rfl
    rw [htl] at hrest
    rw [termLen_func hkf hv.isUTerm] at hP ⊢
    obtain ⟨_, _, _, hDv⟩ := dossT_func htbl hW hWd hkf hv hD
    have hPv : LenPreV (listSum (termLenVec LAct k v)) n (i + 1) E Γ :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left le_self_add zero_le)) (le_refl 8)) hP.1,
       le_trans (le_of_eq (show i + 1 + 5 * listSum (termLenVec LAct k v) + 3 = i + 5 * listSum (termLenVec LAct k v) + 4 by ring))
         (le_trans (add_le_add (le_refl (i + 5 * listSum (termLenVec LAct k v))) (by norm_num : (4 : V) ≤ 7))
           (le_of_eq (by ring) |>.trans hP.2.1)),
       hP.fset⟩
    obtain ⟨okV, hM, hSum⟩ := hrest (i + 1) yv E Γ hyv hPv hDv
    obtain ⟨hndV, hsV⟩ := lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) yv hyv
    rw [htl] at hsV
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yv) := finalCtx_isFormulaSet 8 htbl hP.fset okV
    have hD₁ : DossT Wd (finalCtx Γ yv) n (^func k f v) (i + shiftsV yv) := dossT_transport' hndV hD
    obtain ⟨okTail, hres⟩ := lnFuncTail_ok htbl hC htblN hWd hWp hkf hv rfl hsV (hP.ctx hΓ₁) hM hSum hD₁
    obtain ⟨_, hsh⟩ := lnFuncSteps_struct hWp T k f _ i _ yv hndV
    refine ⟨by rw [lnFuncSteps_eq]; exact listOK_appendV okV okTail, ?_⟩
    rw [hsh, lnFuncSteps_eq, finalCtx_appendV, ← add_assoc]
    exact hres

end lenTOK

/-! ### 5.8 Applicability of the formula lists: `lenFGraph_ok` and the named `lenSteps_ok` -/

section lenFOK

/-- The tails of the formula lists, named. -/
noncomputable def lnAtomTail (W T c k R σ i sv : V) : V :=
  ?[mkStep W (relRow R) 0,
    mkStep W 155 ?[^&(i + sv)],
    mkStep W c ?[cTV k, cTV R, vRef (i + 1 + sv + 1) k, ^&(i + sv + 1), vRef 1 k, bnum σ, ^&0],
    sLemma (succFact σ) (succCode T σ),
    mkStep W 123 ?[^&0, bnum σ ^+ (𝟏 : V), bnum (σ + 1)],
    mkStep W 145 ?[^&(i + sv + 1), ^&0, bnum (σ + 1)]]
lemma lnAtomSteps_eq (W T c k R σ i sv yv : V) : lnAtomSteps W T c k R σ i sv yv = appendV yv (lnAtomTail W T c k R σ i sv) := rfl
noncomputable def lnBinTail (W T c n cq lp lq i sq sp : V) : V :=
  ?[mkStep W 155 ?[^&(i + (sq + sp))],
    mkStep W c ?[cTV n, ^&(i + cq + 1 + (sq + sp) + 1), ^&(i + 1 + (sq + sp) + 1), ^&(i + (sq + sp) + 1), bnum lp, bnum lq, ^&0],
    sLemma (addFact lp lq) (addCode T lp lq),
    mkStep W 184 ?[bnum lp ^+ bnum lq, bnum (lp + lq)],
    sLemma (succFact (lp + lq)) (succCode T (lp + lq)),
    mkStep W 123 ?[^&0, bnum lp ^+ bnum lq ^+ (𝟏 : V), bnum (lp + lq) ^+ (𝟏 : V)],
    mkStep W 123 ?[^&0, bnum (lp + lq) ^+ (𝟏 : V), bnum (lp + lq + 1)],
    mkStep W 145 ?[^&(i + (sq + sp) + 1), ^&0, bnum (lp + lq + 1)]]
lemma lnBinSteps_eq (W T c n cq lp lq i sq sp yq yp : V) :
    lnBinSteps W T c n cq lp lq i sq sp yq yp = appendV yq (appendV yp (lnBinTail W T c n cq lp lq i sq sp)) := rfl
noncomputable def lnQuantTail (W T c n lp i sb : V) : V :=
  ?[mkStep W 155 ?[^&(i + sb)],
    mkStep W c ?[cTV n, ^&(i + 1 + sb + 1), ^&(i + sb + 1), bnum lp, ^&0],
    sLemma (succFact lp) (succCode T lp),
    mkStep W 123 ?[^&0, bnum lp ^+ (𝟏 : V), bnum (lp + 1)],
    mkStep W 145 ?[^&(i + sb + 1), ^&0, bnum (lp + 1)]]
lemma lnQuantSteps_eq (W T c n lp i sb yb : V) : lnQuantSteps W T c n lp i sb yb = appendV yb (lnQuantTail W T c n lp i sb) := rfl

lemma verumFact_setShift {Γ i : V} (h : neg LAct (verumFact (^&i)) ∈ Γ) : neg LAct (verumFact (^&(i + 1))) ∈ setShift LAct Γ := by
  have := mem_setShift_of_mem h
  rwa [← shiftIterV_one, shiftIterV_neg (isFormula_verumFact (by simp)), shiftIterV_verumFact (by simp), termShiftIterV_fvar] at this
lemma falsumFact_setShift {Γ i : V} (h : neg LAct (falsumFact (^&i)) ∈ Γ) : neg LAct (falsumFact (^&(i + 1))) ∈ setShift LAct Γ := by
  have := mem_setShift_of_mem h
  rwa [← shiftIterV_one, shiftIterV_neg (isFormula_falsumFact (by simp)), shiftIterV_falsumFact (by simp), termShiftIterV_fvar] at this

/-- The constant lists are applicable (`verum` at 147, `falsum` at 148). -/
lemma lnConstSteps_ok {tbl N W : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (hWp : W = certPieces) {n i E Γ : V} {c : V}
    (hP : LenPre 1 n i E Γ)
    (hfact : (c = 147 ∧ neg LAct (verumFact (^&(i + 1))) ∈ setShift LAct Γ) ∨
      (c = 148 ∧ neg LAct (falsumFact (^&(i + 1))) ∈ setShift LAct Γ)) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnConstSteps W c i) ∧
    neg LAct (lenFact (bnum 1) (^&(i + 1))) ∈ finalCtx Γ (lnConstSteps W c i) := by
  have hΓ := hP.fset
  have hi0 : termLen LAct (^&i : V) ≤ E := hP.eFvar off_i
  have hi1 : termLen LAct (^&(i + 1) : V) ≤ E := hP.eFvar off_i1
  have hb1 : termLen LAct (bnum 1) ≤ E := hP.eBnum le_rfl
  obtain ⟨ok₁, _, cx₁⟩ := cok_formulaLenTotal htbl hC hWp hΓ (wp := ^&i) (by simp) hi0
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (lenFact (^&(0 : V)) (^&(i + 1)))) (setShift LAct Γ) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hlen₁ : neg LAct (lenFact (^&(0 : V)) (^&(i + 1))) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  have step₂ : StepOK tbl E ((8 : ℕ) : V) Γ₁ (mkStep W c ?[^&(i + 1), ^&0]) ∧
      ctxAfter Γ₁ (mkStep W c ?[^&(i + 1), ^&0]) = insert (neg LAct (eqFactB (^&0) (𝟏 : V))) Γ₁ := by
    rcases hfact with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
    · obtain ⟨ok, _, cx⟩ := cok_formulaLenVerum htbl hC hWp hΓ₁s (by simp) hi1 (by simp) hP.eFvar0
        (by rw [hΓ₁]; exact mem_insert_of_mem' hf) hlen₁
      exact ⟨ok, cx⟩
    · obtain ⟨ok, _, cx⟩ := cok_formulaLenFalsum htbl hC hWp hΓ₁s (by simp) hi1 (by simp) hP.eFvar0
        (by rw [hΓ₁]; exact mem_insert_of_mem' hf) hlen₁
      exact ⟨ok, cx⟩
  obtain ⟨ok₂, cx₂⟩ := step₂
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (𝟏 : V))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  obtain ⟨ok₃, _, cx₃⟩ := cok_congLenNum htbl hC hWp hΓ₂s (by simp) hi1 (by simp) hP.eFvar0 (isSemiterm_bnum_LAct 0 _) hb1
    (by rw [hΓ₂, bnum_one]; exact mem_insert_self')
    (by rw [hΓ₂]; exact mem_insert_of_mem' hlen₁)
  refine ⟨?_, ?_⟩
  · rw [lnConstSteps]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    exact listOK_single ok₃
  · rw [lnConstSteps, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_single, cx₃]
    exact mem_insert_self'

set_option maxHeartbeats 2000000 in
/-- **The quantifier tail is applicable** (`all` at 151 via `dossF_all`, `exs` at 152 via `dossF_exs`). -/
lemma lnQuantTail_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {n p i E Γ : V} (hp : IsSemiformula LAct (n + 1) p) {c lp sb : V}
    (hlp : lp = formulaLen LAct p) (hsb : sb + 1 ≤ 2 * lp) (hP : LenPre (lp + 1) n i E Γ)
    (hb : neg LAct (lenFact (bnum lp) (^&(i + 1 + sb))) ∈ Γ)
    (hD : (c = 151 ∧ DossF Wd Γ n (^∀ p) (i + sb)) ∨ (c = 152 ∧ DossF Wd Γ n (^∃ p) (i + sb))) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnQuantTail W T c n lp i sb) ∧
    neg LAct (lenFact (bnum (lp + 1)) (^&(i + sb + 1))) ∈ finalCtx Γ (lnQuantTail W T c n lp i sb) := by
  have hW : WalkTable tbl := hC.walkTable
  have hΓ := hP.fset
  have hbp : termLen LAct (bnum lp) ≤ E := hP.eBnum le_self_add
  have hbp1 : termLen LAct (bnum (lp + 1)) ≤ E := hP.eBnum le_rfl
  have hbs : termLen LAct (bnum lp ^+ (𝟏 : V)) ≤ E := hP.eBnumSucc le_self_add
  have hoff : i + 1 + sb + 1 + 1 ≤ i + 5 * (lp + 1) + 2 :=
    calc i + 1 + sb + 1 + 1 = i + (sb + 1) + 2 := by ring
      _ ≤ i + 2 * lp + 2 := add_le_add (add_le_add (le_refl i) hsb) (le_refl 2)
      _ ≤ i + 2 * lp + 2 + (3 * lp + 5) := le_self_add
      _ = i + 5 * (lp + 1) + 2 := by ring
  have hfsb : termLen LAct (^&(i + sb) : V) ≤ E := hP.eFvar
    (calc i + sb + 1 ≤ i + sb + 1 + 2 := le_self_add
      _ = i + 1 + sb + 1 + 1 := by ring
      _ ≤ i + 5 * (lp + 1) + 2 := hoff)
  have hfsb1 : termLen LAct (^&(i + sb + 1) : V) ≤ E := hP.eFvar
    (calc i + sb + 1 + 1 ≤ i + sb + 1 + 1 + 1 := le_self_add
      _ = i + 1 + sb + 1 + 1 := by ring
      _ ≤ i + 5 * (lp + 1) + 2 := hoff)
  have hf1sb1 : termLen LAct (^&(i + 1 + sb + 1) : V) ≤ E := hP.eFvar hoff
  -- s₁ : formulaLenTotal [&(i + sb)]
  obtain ⟨ok₁, tag₁, cx₁⟩ := cok_formulaLenTotal htbl hC hWp hΓ (wp := ^&(i + sb)) (by simp) hfsb
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (lenFact (^&(0 : V)) (^&(i + sb + 1)))) (setShift LAct Γ) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hnd₁ : NoDrop' (?[mkStep W 155 ?[^&(i + sb)]] : V) := noDrop'_single_tag2 tag₁
  have hs₁ : shiftsV (?[mkStep W 155 ?[^&(i + sb)]] : V) = 1 := shiftsV_single_tag2 tag₁
  have hlen₁ : neg LAct (lenFact (^&(0 : V)) (^&(i + sb + 1))) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  have hb₁ : neg LAct (lenFact (bnum lp) (^&(i + 1 + sb + 1))) ∈ Γ₁ := by
    have := lenFact_transport hnd₁ hb
    rwa [hs₁, finalCtx_single, cx₁] at this
  -- the node's shape facts after the shift
  have hshape : StepOK tbl E ((8 : ℕ) : V) Γ₁ (mkStep W c ?[cTV n, ^&(i + 1 + sb + 1), ^&(i + sb + 1), bnum lp, ^&0]) ∧
      ctxAfter Γ₁ (mkStep W c ?[cTV n, ^&(i + 1 + sb + 1), ^&(i + sb + 1), bnum lp, ^&0]) =
        insert (neg LAct (eqFactB (^&0) (bnum lp ^+ (𝟏 : V)))) Γ₁ := by
    rcases hD with ⟨rfl, hD⟩ | ⟨rfl, hD⟩
    · have hD₁ : DossF Wd Γ₁ n (^∀ p) (i + sb + 1) := by
        have := dossF_transport' hnd₁ hD
        rwa [hs₁, finalCtx_single, cx₁] at this
      obtain ⟨hall, _, hDp⟩ := dossF_all htbl hW hWd hp hD₁
      rw [show i + sb + 1 + 1 = i + 1 + sb + 1 by ring] at hall hDp
      have hpi : neg LAct (piFact (cTV n ^+ (𝟏 : V)) (^&(i + 1 + sb + 1))) ∈ Γ₁ := by
        rw [← cTV_succ]; exact dossF_pi htbl hW hWd hp hDp
      obtain ⟨ok, _, cx⟩ := cok_formulaLenAll htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hP.eCTVn (by simp) hf1sb1 (by simp) hfsb1
        (isSemiterm_bnum_LAct 0 _) hbp (by simp) hP.eFvar0 hpi hall hb₁ hlen₁
      exact ⟨ok, cx⟩
    · have hD₁ : DossF Wd Γ₁ n (^∃ p) (i + sb + 1) := by
        have := dossF_transport' hnd₁ hD
        rwa [hs₁, finalCtx_single, cx₁] at this
      obtain ⟨hexs, _, hDp⟩ := dossF_exs htbl hW hWd hp hD₁
      rw [show i + sb + 1 + 1 = i + 1 + sb + 1 by ring] at hexs hDp
      have hpi : neg LAct (piFact (cTV n ^+ (𝟏 : V)) (^&(i + 1 + sb + 1))) ∈ Γ₁ := by
        rw [← cTV_succ]; exact dossF_pi htbl hW hWd hp hDp
      obtain ⟨ok, _, cx⟩ := cok_formulaLenExs htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hP.eCTVn (by simp) hf1sb1 (by simp) hfsb1
        (isSemiterm_bnum_LAct 0 _) hbp (by simp) hP.eFvar0 hpi hexs hb₁ hlen₁
      exact ⟨ok, cx⟩
  obtain ⟨ok₂, cx₂⟩ := hshape
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (bnum lp ^+ (𝟏 : V)))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (succFact lp) (succCode T lp)) := stepOK_sLemma hΓ₂s (lemmaOK_succ htblN lp)
  have cx₃ := ctxAfter_sLemma Γ₂ (succFact lp) (succCode T lp)
  set Γ₃ := insert (neg LAct (succFact lp)) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, _, cx₄⟩ := cok_eqTrans htbl hC hWp hΓ₃s (by simp) hP.eFvar0 (isSemiterm_bnum_succ lp) hbs (isSemiterm_bnum_LAct 0 _) hbp1
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' mem_insert_self')
    (by rw [hΓ₃]; exact mem_insert_self')
  set Γ₄ := insert (neg LAct (eqFactB (^&0) (bnum (lp + 1)))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  obtain ⟨ok₅, _, cx₅⟩ := cok_congLenNum htbl hC hWp hΓ₄s (by simp) hfsb1 (by simp) hP.eFvar0 (isSemiterm_bnum_LAct 0 _) hbp1
    (by rw [hΓ₄]; exact mem_insert_self')
    (by rw [hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hlen₁)))
  refine ⟨?_, ?_⟩
  · rw [lnQuantTail]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    exact listOK_single ok₅
  · rw [lnQuantTail, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_single, cx₅]
    exact mem_insert_self'

set_option maxHeartbeats 2000000 in
/-- **The binary tail is applicable** (`and` at 149 via `dossF_and`, `or` at 150 via `dossF_or`). -/
lemma lnBinTail_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {n p q i E Γ : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q)
    {c cq lp lq sq sp : V} (hcq : cq = descCountF Wd n q) (hlp : lp = formulaLen LAct p) (hlq : lq = formulaLen LAct q)
    (hcq_le : cq + 1 ≤ 2 * lq) (hsq : sq + 1 ≤ 2 * lq) (hsp : sp + 1 ≤ 2 * lp) (hP : LenPre (lp + lq + 1) n i E Γ)
    (hfq : neg LAct (lenFact (bnum lq) (^&(i + 1 + sq + sp))) ∈ Γ)
    (hfp : neg LAct (lenFact (bnum lp) (^&(i + cq + 1 + sq + sp))) ∈ Γ)
    (hD : (c = 149 ∧ DossF Wd Γ n (p ^⋏ q) (i + sq + sp)) ∨ (c = 150 ∧ DossF Wd Γ n (p ^⋎ q) (i + sq + sp))) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnBinTail W T c n cq lp lq i sq sp) ∧
    neg LAct (lenFact (bnum (lp + lq + 1)) (^&(i + (sq + sp) + 1))) ∈ finalCtx Γ (lnBinTail W T c n cq lp lq i sq sp) := by
  have hW : WalkTable tbl := hC.walkTable
  have hΓ := hP.fset
  set S := sq + sp with hS
  have hDp : lp ≤ lp + lq + 1 := le_trans le_self_add le_self_add
  have hDq : lq ≤ lp + lq + 1 := le_trans le_add_self le_self_add
  have hDs : lp + lq ≤ lp + lq + 1 := le_self_add
  have hbp : termLen LAct (bnum lp) ≤ E := hP.eBnum hDp
  have hbq : termLen LAct (bnum lq) ≤ E := hP.eBnum hDq
  have hbs : termLen LAct (bnum (lp + lq)) ≤ E := hP.eBnum hDs
  have hbs1 : termLen LAct (bnum (lp + lq + 1)) ≤ E := hP.eBnum le_rfl
  have hbpq : termLen LAct (bnum lp ^+ bnum lq) ≤ E := hP.eBnumAdd hDp hDq
  have hbpq1 : termLen LAct (bnum lp ^+ bnum lq ^+ (𝟏 : V)) ≤ E := hP.eBnumAddSucc hDp hDq
  have hbs' : termLen LAct (bnum (lp + lq) ^+ (𝟏 : V)) ≤ E := hP.eBnumSucc hDs
  have hSle : S + 2 ≤ 2 * lq + 2 * lp := by
    rw [hS]
    calc sq + sp + 2 = (sq + 1) + (sp + 1) := by ring
      _ ≤ 2 * lq + 2 * lp := add_le_add hsq hsp
  have hcqle : cq ≤ 2 * lq := le_trans le_self_add hcq_le
  have hoff : i + cq + 1 + S + 1 + 1 ≤ i + 5 * (lp + lq + 1) + 2 :=
    calc i + cq + 1 + S + 1 + 1 = i + cq + (S + 2) + 1 := by ring
      _ ≤ i + 2 * lq + (2 * lq + 2 * lp) + 1 := add_le_add (add_le_add (add_le_add (le_refl i) hcqle) hSle) (le_refl 1)
      _ = i + (4 * lq + 2 * lp + 1) := by ring
      _ ≤ i + (4 * lq + 2 * lp + 1 + (lq + 3 * lp + 6)) := add_le_add (le_refl i) le_self_add
      _ = i + 5 * (lp + lq + 1) + 2 := by ring
  have hfS : termLen LAct (^&(i + S) : V) ≤ E := hP.eFvar
    (calc i + S + 1 ≤ i + S + 1 + (cq + 1 + 1) := le_self_add
      _ = i + cq + 1 + S + 1 + 1 := by ring
      _ ≤ i + 5 * (lp + lq + 1) + 2 := hoff)
  have hfS1 : termLen LAct (^&(i + S + 1) : V) ≤ E := hP.eFvar
    (calc i + S + 1 + 1 ≤ i + S + 1 + 1 + (cq + 1) := le_self_add
      _ = i + cq + 1 + S + 1 + 1 := by ring
      _ ≤ i + 5 * (lp + lq + 1) + 2 := hoff)
  have hf1S1 : termLen LAct (^&(i + 1 + S + 1) : V) ≤ E := hP.eFvar
    (calc i + 1 + S + 1 + 1 ≤ i + 1 + S + 1 + 1 + cq := le_self_add
      _ = i + cq + 1 + S + 1 + 1 := by ring
      _ ≤ i + 5 * (lp + lq + 1) + 2 := hoff)
  have hfcq : termLen LAct (^&(i + cq + 1 + S + 1) : V) ≤ E := hP.eFvar hoff
  -- s₁ : formulaLenTotal [&(i + S)]
  obtain ⟨ok₁, tag₁, cx₁⟩ := cok_formulaLenTotal htbl hC hWp hΓ (wp := ^&(i + S)) (by simp) hfS
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (lenFact (^&(0 : V)) (^&(i + S + 1)))) (setShift LAct Γ) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hnd₁ : NoDrop' (?[mkStep W 155 ?[^&(i + S)]] : V) := noDrop'_single_tag2 tag₁
  have hs₁ : shiftsV (?[mkStep W 155 ?[^&(i + S)]] : V) = 1 := shiftsV_single_tag2 tag₁
  have hlen₁ : neg LAct (lenFact (^&(0 : V)) (^&(i + S + 1))) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  have hfq₁ : neg LAct (lenFact (bnum lq) (^&(i + 1 + S + 1))) ∈ Γ₁ := by
    have := lenFact_transport hnd₁ hfq
    rwa [hs₁, finalCtx_single, cx₁, show i + 1 + sq + sp + 1 = i + 1 + S + 1 by rw [hS]; ring] at this
  have hfp₁ : neg LAct (lenFact (bnum lp) (^&(i + cq + 1 + S + 1))) ∈ Γ₁ := by
    have := lenFact_transport hnd₁ hfp
    rwa [hs₁, finalCtx_single, cx₁, show i + cq + 1 + sq + sp + 1 = i + cq + 1 + S + 1 by rw [hS]; ring] at this
  -- s₂ : the row at [cT n, &p, &q, &r, bnum lp, bnum lq, &0]
  have hshape : StepOK tbl E ((8 : ℕ) : V) Γ₁
        (mkStep W c ?[cTV n, ^&(i + cq + 1 + S + 1), ^&(i + 1 + S + 1), ^&(i + S + 1), bnum lp, bnum lq, ^&0]) ∧
      ctxAfter Γ₁ (mkStep W c ?[cTV n, ^&(i + cq + 1 + S + 1), ^&(i + 1 + S + 1), ^&(i + S + 1), bnum lp, bnum lq, ^&0]) =
        insert (neg LAct (eqFactB (^&0) (bnum lp ^+ bnum lq ^+ (𝟏 : V)))) Γ₁ := by
    rcases hD with ⟨rfl, hD⟩ | ⟨rfl, hD⟩
    · have hD₁ : DossF Wd Γ₁ n (p ^⋏ q) (i + S + 1) := by
        have := dossF_transport' hnd₁ hD
        rwa [hs₁, finalCtx_single, cx₁, show i + sq + sp + 1 = i + S + 1 by rw [hS]; ring] at this
      obtain ⟨hand, _, hDq, hDp⟩ := dossF_and htbl hW hWd hp hq hD₁
      rw [← hcq] at hand hDp
      rw [show i + S + 1 + cq + 1 = i + cq + 1 + S + 1 by ring, show i + S + 1 + 1 = i + 1 + S + 1 by ring] at hand
      rw [show i + S + 1 + cq + 1 = i + cq + 1 + S + 1 by ring] at hDp
      rw [show i + S + 1 + 1 = i + 1 + S + 1 by ring] at hDq
      have hpip : neg LAct (piFact (cTV n) (^&(i + cq + 1 + S + 1))) ∈ Γ₁ := dossF_pi htbl hW hWd hp hDp
      have hpiq : neg LAct (piFact (cTV n) (^&(i + 1 + S + 1))) ∈ Γ₁ := dossF_pi htbl hW hWd hq hDq
      obtain ⟨ok, _, cx⟩ := cok_formulaLenAnd htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hP.eCTVn (by simp) hfcq (by simp) hf1S1
        (by simp) hfS1 (isSemiterm_bnum_LAct 0 _) hbp (isSemiterm_bnum_LAct 0 _) hbq (by simp) hP.eFvar0
        hpip hpiq hand hfp₁ hfq₁ hlen₁
      exact ⟨ok, cx⟩
    · have hD₁ : DossF Wd Γ₁ n (p ^⋎ q) (i + S + 1) := by
        have := dossF_transport' hnd₁ hD
        rwa [hs₁, finalCtx_single, cx₁, show i + sq + sp + 1 = i + S + 1 by rw [hS]; ring] at this
      obtain ⟨hor, _, hDq, hDp⟩ := dossF_or htbl hW hWd hp hq hD₁
      rw [← hcq] at hor hDp
      rw [show i + S + 1 + cq + 1 = i + cq + 1 + S + 1 by ring, show i + S + 1 + 1 = i + 1 + S + 1 by ring] at hor
      rw [show i + S + 1 + cq + 1 = i + cq + 1 + S + 1 by ring] at hDp
      rw [show i + S + 1 + 1 = i + 1 + S + 1 by ring] at hDq
      have hpip : neg LAct (piFact (cTV n) (^&(i + cq + 1 + S + 1))) ∈ Γ₁ := dossF_pi htbl hW hWd hp hDp
      have hpiq : neg LAct (piFact (cTV n) (^&(i + 1 + S + 1))) ∈ Γ₁ := dossF_pi htbl hW hWd hq hDq
      obtain ⟨ok, _, cx⟩ := cok_formulaLenOr htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hP.eCTVn (by simp) hfcq (by simp) hf1S1
        (by simp) hfS1 (isSemiterm_bnum_LAct 0 _) hbp (isSemiterm_bnum_LAct 0 _) hbq (by simp) hP.eFvar0
        hpip hpiq hor hfp₁ hfq₁ hlen₁
      exact ⟨ok, cx⟩
  obtain ⟨ok₂, cx₂⟩ := hshape
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (bnum lp ^+ bnum lq ^+ (𝟏 : V)))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- s₃ : addFact lp lq
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (addFact lp lq) (addCode T lp lq)) := stepOK_sLemma hΓ₂s (lemmaOK_add htblN lp lq)
  have cx₃ := ctxAfter_sLemma Γ₂ (addFact lp lq) (addCode T lp lq)
  set Γ₃ := insert (neg LAct (addFact lp lq)) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- s₄ : congSucc [bnum lp + bnum lq, bnum (lp + lq)]
  obtain ⟨ok₄, _, cx₄⟩ := cok_congSucc htbl hC hWp hΓ₃s (isSemiterm_bnum_add lp lq) hbpq (isSemiterm_bnum_LAct 0 _) hbs
    (by rw [hΓ₃]; exact mem_insert_self')
  set Γ₄ := insert (neg LAct (eqFactB (bnum lp ^+ bnum lq ^+ (𝟏 : V)) (bnum (lp + lq) ^+ (𝟏 : V)))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- s₅ : succFact (lp + lq)
  have ok₅ : StepOK tbl E ((8 : ℕ) : V) Γ₄ (sLemma (succFact (lp + lq)) (succCode T (lp + lq))) :=
    stepOK_sLemma hΓ₄s (lemmaOK_succ htblN (lp + lq))
  have cx₅ := ctxAfter_sLemma Γ₄ (succFact (lp + lq)) (succCode T (lp + lq))
  set Γ₅ := insert (neg LAct (succFact (lp + lq))) Γ₄ with hΓ₅
  have hΓ₅s : IsFormulaSet LAct Γ₅ := by rw [← cx₅]; exact isFormulaSet_ctxAfter 8 htbl ok₅
  -- s₆ : eqTrans [&0, bnum lp + bnum lq + 1, bnum (lp+lq) + 1]
  obtain ⟨ok₆, _, cx₆⟩ := cok_eqTrans htbl hC hWp hΓ₅s (by simp) hP.eFvar0 (isSemiterm_bnum_add_succ lp lq) hbpq1
    (isSemiterm_bnum_succ _) hbs'
    (by rw [hΓ₅, hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' mem_insert_self')))
    (by rw [hΓ₅, hΓ₄]; exact mem_insert_of_mem' mem_insert_self')
  set Γ₆ := insert (neg LAct (eqFactB (^&0) (bnum (lp + lq) ^+ (𝟏 : V)))) Γ₅ with hΓ₆
  have hΓ₆s : IsFormulaSet LAct Γ₆ := by rw [← cx₆]; exact isFormulaSet_ctxAfter 8 htbl ok₆
  -- s₇ : eqTrans [&0, bnum (lp+lq) + 1, bnum (lp+lq+1)]
  obtain ⟨ok₇, _, cx₇⟩ := cok_eqTrans htbl hC hWp hΓ₆s (by simp) hP.eFvar0 (isSemiterm_bnum_succ _) hbs' (isSemiterm_bnum_LAct 0 _) hbs1
    (by rw [hΓ₆]; exact mem_insert_self')
    (by rw [hΓ₆, hΓ₅]; exact mem_insert_of_mem' mem_insert_self')
  set Γ₇ := insert (neg LAct (eqFactB (^&0) (bnum (lp + lq + 1)))) Γ₆ with hΓ₇
  have hΓ₇s : IsFormulaSet LAct Γ₇ := by rw [← cx₇]; exact isFormulaSet_ctxAfter 8 htbl ok₇
  -- s₈ : congLenNum [&(i + S + 1), &0, bnum (lp+lq+1)]
  obtain ⟨ok₈, _, cx₈⟩ := cok_congLenNum htbl hC hWp hΓ₇s (by simp) hfS1 (by simp) hP.eFvar0 (isSemiterm_bnum_LAct 0 _) hbs1
    (by rw [hΓ₇]; exact mem_insert_self')
    (by rw [hΓ₇, hΓ₆, hΓ₅, hΓ₄, hΓ₃, hΓ₂]
        exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hlen₁))))))
  refine ⟨?_, ?_⟩
  · rw [lnBinTail]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    refine listOK_cons ok₅ ?_
    rw [cx₅]
    refine listOK_cons ok₆ ?_
    rw [cx₆]
    refine listOK_cons ok₇ ?_
    rw [cx₇]
    exact listOK_single ok₈
  · rw [lnBinTail, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_cons, cx₅,
      finalCtx_cons, cx₆, finalCtx_cons, cx₇, finalCtx_single, cx₈]
    exact mem_insert_self'

set_option maxHeartbeats 2000000 in
/-- **The atom tail is applicable** (`rel` at 142 via `dossF_rel`, `nrel` at 143 via `dossF_nrel`). -/
lemma lnAtomTail_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) {n k R v i E Γ : V} (hkR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v)
    {c σ sv : V} (hσ : σ = listSum (termLenVec LAct k v)) (hsv : sv ≤ 2 * σ) (hP : LenPre (σ + 1) n i E Γ)
    (hM : neg LAct (tlvFact (vRef 0 k) (cTV k) (vRef (i + 1 + sv) k)) ∈ Γ)
    (hSum : neg LAct (listSumFact (bnum σ) (vRef 0 k)) ∈ Γ)
    (hD : (c = 142 ∧ DossF Wd Γ n (^rel k R v) (i + sv)) ∨ (c = 143 ∧ DossF Wd Γ n (^nrel k R v) (i + sv))) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lnAtomTail W T c k R σ i sv) ∧
    neg LAct (lenFact (bnum (σ + 1)) (^&(i + sv + 1))) ∈ finalCtx Γ (lnAtomTail W T c k R σ i sv) := by
  have hW : WalkTable tbl := hC.walkTable
  have hΓ := hP.fset
  have hbσ : termLen LAct (bnum σ) ≤ E := hP.eBnum le_self_add
  have hbσ1 : termLen LAct (bnum (σ + 1)) ≤ E := hP.eBnum le_rfl
  have hbs : termLen LAct (bnum σ ^+ (𝟏 : V)) ≤ E := hP.eBnumSucc le_self_add
  have hr1 : termLen LAct (vRef 1 k) ≤ E := termLen_vRef_le (le_trans (by norm_num) hP.eight)
  have hoff : i + 1 + sv + 1 + 1 ≤ i + 5 * (σ + 1) + 2 :=
    calc i + 1 + sv + 1 + 1 ≤ i + 1 + 2 * σ + 1 + 1 := add_le_add (add_le_add (add_le_add (le_refl _) hsv) (le_refl _)) (le_refl _)
      _ = i + (2 * σ + 3) := by ring
      _ ≤ i + (2 * σ + 3 + (3 * σ + 4)) := add_le_add (le_refl i) le_self_add
      _ = i + 5 * (σ + 1) + 2 := by ring
  have hrv : termLen LAct (vRef (i + 1 + sv + 1) k) ≤ E := hP.eVRef hoff
  have hfsv : termLen LAct (^&(i + sv) : V) ≤ E := hP.eFvar
    (calc i + sv + 1 ≤ i + sv + 1 + 2 := le_self_add
      _ = i + 1 + sv + 1 + 1 := by ring
      _ ≤ i + 5 * (σ + 1) + 2 := hoff)
  have hfsv1 : termLen LAct (^&(i + sv + 1) : V) ≤ E := hP.eFvar
    (calc i + sv + 1 + 1 ≤ i + sv + 1 + 1 + 1 := le_self_add
      _ = i + 1 + sv + 1 + 1 := by ring
      _ ≤ i + 5 * (σ + 1) + 2 := hoff)
  -- s₀ : the closed relation-symbol row
  have er₀ : mkStep W (relRow R) 0 = mkStep walkPieces (relRow R) 0 := by rw [hWp, mkStep_certPieces_relRow]
  obtain ⟨ok₀, _, cx₀, hEk, hER⟩ := relConst_ok htbl hW rfl hkR hP.eight hΓ
  rw [← er₀] at ok₀ cx₀
  set Γ₀ := insert (neg LAct (isRelFact (cTV k) (cTV R))) Γ with hΓ₀
  have hΓ₀s : IsFormulaSet LAct Γ₀ := by rw [← cx₀]; exact isFormulaSet_ctxAfter 8 htbl ok₀
  -- s₁ : formulaLenTotal [&(i + sv)]
  obtain ⟨ok₁, tag₁, cx₁⟩ := cok_formulaLenTotal htbl hC hWp hΓ₀s (wp := ^&(i + sv)) (by simp) hfsv
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (lenFact (^&(0 : V)) (^&(i + sv + 1)))) (setShift LAct Γ₀) with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have hnd₁ : NoDrop' (?[mkStep W 155 ?[^&(i + sv)]] : V) := noDrop'_single_tag2 tag₁
  have hs₁ : shiftsV (?[mkStep W 155 ?[^&(i + sv)]] : V) = 1 := shiftsV_single_tag2 tag₁
  have hlen₁ : neg LAct (lenFact (^&(0 : V)) (^&(i + sv + 1))) ∈ Γ₁ := by rw [hΓ₁]; exact mem_insert_self'
  have hM₁ : neg LAct (tlvFact (vRef 1 k) (cTV k) (vRef (i + 1 + sv + 1) k)) ∈ Γ₁ := by
    have := tlvFact_transport hnd₁ (mem_insert_of_mem' hM : _ ∈ Γ₀)
    rwa [hs₁, finalCtx_single, cx₁] at this
  have hSum₁ : neg LAct (listSumFact (bnum σ) (vRef 1 k)) ∈ Γ₁ := by
    have := listSumFact_transport hnd₁ (mem_insert_of_mem' hSum : _ ∈ Γ₀)
    rwa [hs₁, finalCtx_single, cx₁] at this
  have hisR₁ : neg LAct (isRelFact (cTV k) (cTV R)) ∈ Γ₁ := by
    have := mem_finalCtx_of_mem' hnd₁ (mem_insert_self' : _ ∈ Γ₀)
    rwa [finalCtx_single, cx₁, shiftIterV_neg (isFormula_isRelFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)),
      shiftIterV_isRelFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _), termShiftIterV_cTV, termShiftIterV_cTV] at this
  have hshape : StepOK tbl E ((8 : ℕ) : V) Γ₁
        (mkStep W c ?[cTV k, cTV R, vRef (i + 1 + sv + 1) k, ^&(i + sv + 1), vRef 1 k, bnum σ, ^&0]) ∧
      ctxAfter Γ₁ (mkStep W c ?[cTV k, cTV R, vRef (i + 1 + sv + 1) k, ^&(i + sv + 1), vRef 1 k, bnum σ, ^&0]) =
        insert (neg LAct (eqFactB (^&0) (bnum σ ^+ (𝟏 : V)))) Γ₁ := by
    rcases hD with ⟨rfl, hD⟩ | ⟨rfl, hD⟩
    · have hD₁ : DossF Wd Γ₁ n (^rel k R v) (i + sv + 1) := by
        have := dossF_transport' hnd₁ (hD.mono (subset_insert' : Γ ⊆ Γ₀))
        rwa [hs₁, finalCtx_single, cx₁] at this
      obtain ⟨hrel, _, hutv, _⟩ := dossF_rel htbl hW hWd hkR hv hD₁
      rw [show i + sv + 1 + 1 = i + 1 + sv + 1 by ring] at hrel hutv
      obtain ⟨ok, _, cx⟩ := cok_formulaLenRelCert htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hER
        (isSemiterm_vRef _ _) hrv (by simp) hfsv1 (isSemiterm_vRef _ _) hr1 (isSemiterm_bnum_LAct 0 _) hbσ (by simp) hP.eFvar0
        hisR₁ hutv hrel hM₁ hSum₁ hlen₁
      exact ⟨ok, cx⟩
    · have hD₁ : DossF Wd Γ₁ n (^nrel k R v) (i + sv + 1) := by
        have := dossF_transport' hnd₁ (hD.mono (subset_insert' : Γ ⊆ Γ₀))
        rwa [hs₁, finalCtx_single, cx₁] at this
      obtain ⟨hrel, _, hutv, _⟩ := dossF_nrel htbl hW hWd hkR hv hD₁
      rw [show i + sv + 1 + 1 = i + 1 + sv + 1 by ring] at hrel hutv
      obtain ⟨ok, _, cx⟩ := cok_formulaLenNRelCert htbl hC hWp hΓ₁s (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hER
        (isSemiterm_vRef _ _) hrv (by simp) hfsv1 (isSemiterm_vRef _ _) hr1 (isSemiterm_bnum_LAct 0 _) hbσ (by simp) hP.eFvar0
        hisR₁ hutv hrel hM₁ hSum₁ hlen₁
      exact ⟨ok, cx⟩
  obtain ⟨ok₂, cx₂⟩ := hshape
  set Γ₂ := insert (neg LAct (eqFactB (^&0) (bnum σ ^+ (𝟏 : V)))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (succFact σ) (succCode T σ)) := stepOK_sLemma hΓ₂s (lemmaOK_succ htblN σ)
  have cx₃ := ctxAfter_sLemma Γ₂ (succFact σ) (succCode T σ)
  set Γ₃ := insert (neg LAct (succFact σ)) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, _, cx₄⟩ := cok_eqTrans htbl hC hWp hΓ₃s (by simp) hP.eFvar0 (isSemiterm_bnum_succ σ) hbs (isSemiterm_bnum_LAct 0 _) hbσ1
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' mem_insert_self')
    (by rw [hΓ₃]; exact mem_insert_self')
  set Γ₄ := insert (neg LAct (eqFactB (^&0) (bnum (σ + 1)))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  obtain ⟨ok₅, _, cx₅⟩ := cok_congLenNum htbl hC hWp hΓ₄s (by simp) hfsv1 (by simp) hP.eFvar0 (isSemiterm_bnum_LAct 0 _) hbσ1
    (by rw [hΓ₄]; exact mem_insert_self')
    (by rw [hΓ₄, hΓ₃, hΓ₂]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hlen₁)))
  refine ⟨?_, ?_⟩
  · rw [lnAtomTail]
    refine listOK_cons ok₀ ?_
    rw [cx₀]
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    exact listOK_single ok₅
  · rw [lnAtomTail, finalCtx_cons, cx₀, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄,
      finalCtx_single, cx₅]
    exact mem_insert_self'

/-- The formula-level invariant. -/
def FLenOK (tbl Wd W T n r : V) : Prop :=
  ∀ i y E Γ : V, LenFGraph W T n r i y → LenPre (formulaLen LAct r) n i E Γ → DossF Wd Γ n r i →
    LenPost tbl E Γ y (lenFact (bnum (formulaLen LAct r)) (^&(i + shiftsV y)))

set_option maxHeartbeats 4000000 in
/-- **The formula length lists are applicable.** -/
theorem lenFGraph_ok {tbl N N' B' Wd W T : V} (htbl : TableOK tbl N) (hC : CertTable tbl) (htblN : NumTableOK T N' B')
    (hWd : Wd = walkPieces) (hWp : W = certPieces) : ∀ {n r : V}, IsSemiformula LAct n r → FLenOK tbl Wd W T n r := by
  have hW : WalkTable tbl := hC.walkTable
  intro n r
  apply IsSemiformula.pi1_structural_induction (P := fun n r ↦ FLenOK tbl Wd W T n r)
  · unfold FLenOK LenFGraph; definability
  · -- rel
    intro n k R v hkR hv i y E Γ hy hP hD
    rw [LenFGraph.rel_iff.mp hy, (lnAtomSteps_struct hWp (Or.inl rfl) T k R _ i _ _
      (lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) _ (lenV_graph hv le_rfl)).1).2]
    rw [formulaLen_rel hkR hv.isUTerm] at hP ⊢
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨_, hrest⟩ := lenVGraph_ok_aux htbl hC htblN hWd hWp n (rel_arity_le_two hkR) hv
      (fun a ha ↦ lenTGraph_ok htbl hC htblN hWd hWp n _ (hv.nth ha)) k le_rfl
    rw [htl] at hrest
    obtain ⟨_, _, _, hDv⟩ := dossF_rel htbl hW hWd hkR hv hD
    set σ := listSum (termLenVec LAct k v) with hσ
    have hPv : LenPreV σ n (i + 1) E Γ :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left le_self_add zero_le)) (le_refl 8)) hP.1,
       le_trans (le_of_eq (show i + 1 + 5 * σ + 3 = i + 5 * σ + 4 by ring))
         (le_trans (add_le_add (le_refl (i + 5 * σ)) (by norm_num : (4 : V) ≤ 7)) (le_of_eq (by ring) |>.trans hP.2.1)),
       hP.fset⟩
    obtain ⟨okV, hM, hSum⟩ := hrest (i + 1) _ E Γ (lenV_graph hv le_rfl) hPv hDv
    obtain ⟨hndV, hsV⟩ := lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) _ (lenV_graph hv le_rfl)
    rw [htl] at hsV
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ (lenV W T n k v k (i + 1))) := finalCtx_isFormulaSet 8 htbl hP.fset okV
    have hD₁ : DossF Wd (finalCtx Γ (lenV W T n k v k (i + 1))) n (^rel k R v) (i + shiftsV (lenV W T n k v k (i + 1))) :=
      dossF_transport' hndV hD
    obtain ⟨okTail, hres⟩ := lnAtomTail_ok htbl hC htblN hWd hWp hkR hv rfl hsV (hP.ctx hΓ₁) hM hSum (Or.inl ⟨rfl, hD₁⟩)
    refine ⟨by rw [lnAtomSteps_eq]; exact listOK_appendV okV okTail, ?_⟩
    rw [lnAtomSteps_eq, finalCtx_appendV, ← add_assoc]
    exact hres
  · -- nrel
    intro n k R v hkR hv i y E Γ hy hP hD
    rw [LenFGraph.nrel_iff.mp hy, (lnAtomSteps_struct hWp (Or.inr rfl) T k R _ i _ _
      (lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) _ (lenV_graph hv le_rfl)).1).2]
    rw [formulaLen_nrel hkR hv.isUTerm] at hP ⊢
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    obtain ⟨_, hrest⟩ := lenVGraph_ok_aux htbl hC htblN hWd hWp n (rel_arity_le_two hkR) hv
      (fun a ha ↦ lenTGraph_ok htbl hC htblN hWd hWp n _ (hv.nth ha)) k le_rfl
    rw [htl] at hrest
    obtain ⟨_, _, _, hDv⟩ := dossF_nrel htbl hW hWd hkR hv hD
    set σ := listSum (termLenVec LAct k v) with hσ
    have hPv : LenPreV σ n (i + 1) E Γ :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left le_self_add zero_le)) (le_refl 8)) hP.1,
       le_trans (le_of_eq (show i + 1 + 5 * σ + 3 = i + 5 * σ + 4 by ring))
         (le_trans (add_le_add (le_refl (i + 5 * σ)) (by norm_num : (4 : V) ≤ 7)) (le_of_eq (by ring) |>.trans hP.2.1)),
       hP.fset⟩
    obtain ⟨okV, hM, hSum⟩ := hrest (i + 1) _ E Γ (lenV_graph hv le_rfl) hPv hDv
    obtain ⟨hndV, hsV⟩ := lenVGraph_noDrop_shifts hWp T n hv k le_rfl (i + 1) _ (lenV_graph hv le_rfl)
    rw [htl] at hsV
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ (lenV W T n k v k (i + 1))) := finalCtx_isFormulaSet 8 htbl hP.fset okV
    have hD₁ : DossF Wd (finalCtx Γ (lenV W T n k v k (i + 1))) n (^nrel k R v) (i + shiftsV (lenV W T n k v k (i + 1))) :=
      dossF_transport' hndV hD
    obtain ⟨okTail, hres⟩ := lnAtomTail_ok htbl hC htblN hWd hWp hkR hv rfl hsV (hP.ctx hΓ₁) hM hSum (Or.inr ⟨rfl, hD₁⟩)
    refine ⟨by rw [lnAtomSteps_eq]; exact listOK_appendV okV okTail, ?_⟩
    rw [lnAtomSteps_eq, finalCtx_appendV, ← add_assoc]
    exact hres
  · -- verum
    intro n i y E Γ hy hP hD
    rw [LenFGraph.verum_iff.mp hy, (lnConstSteps_struct hWp (Or.inl rfl) i).2]
    rw [formulaLen_verum] at hP ⊢
    obtain ⟨hf, _⟩ := dossF_verum htbl hW hWd hD
    exact lnConstSteps_ok htbl hC hWp hP (Or.inl ⟨rfl, verumFact_setShift hf⟩)
  · -- falsum
    intro n i y E Γ hy hP hD
    rw [LenFGraph.falsum_iff.mp hy, (lnConstSteps_struct hWp (Or.inr rfl) i).2]
    rw [formulaLen_falsum] at hP ⊢
    obtain ⟨hf, _⟩ := dossF_falsum htbl hW hWd hD
    exact lnConstSteps_ok htbl hC hWp hP (Or.inr ⟨rfl, falsumFact_setShift hf⟩)
  · -- and
    intro n p q hp hq ihp ihq i y E Γ hy hP hD
    unfold FLenOK at ihp ihq
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.and_iff.mp hy
    rw [formulaLen_and hp.isUFormula hq.isUFormula] at hP ⊢
    set cq := descCountF W n q with hcq'
    set lp := formulaLen LAct p with hlp
    set lq := formulaLen LAct q with hlq
    have hcq : cq = descCountF Wd n q := by rw [hcq', hWp, hWd]; exact descCountF_certPieces hq
    have hcq_le : cq + 1 ≤ 2 * lq := by rw [hcq]; exact descCountF_walk_le htbl hW hWd hq
    obtain ⟨hndq, hsq⟩ := lenFGraph_noDrop_shifts hWp T hq (i + 1) yq hyq
    obtain ⟨hndp, hsp⟩ := lenFGraph_noDrop_shifts hWp T hp _ yp hyp
    obtain ⟨_, _, hDq, hDp⟩ := dossF_and htbl hW hWd hp hq hD
    rw [← hcq] at hDp
    have hlqD : lq ≤ lp + lq + 1 := le_trans le_add_self le_self_add
    have hlpD : lp ≤ lp + lq + 1 := le_trans le_self_add le_self_add
    -- q's list at i + 1
    have h5q : 5 * lq + 1 ≤ 5 * (lp + lq + 1) := by
      rw [show 5 * (lp + lq + 1) = 5 * lq + 1 + (5 * lp + 4) by ring]; exact le_self_add
    have hPq : LenPre lq n (i + 1) E Γ :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left hlqD zero_le)) (le_refl 8)) hP.1,
       le_trans (le_of_eq (show i + 1 + 5 * lq + 2 = i + (5 * lq + 1) + 2 by ring))
         (le_trans (add_le_add (add_le_add (le_refl i) h5q) (le_refl 2)) hP.2.1),
       hP.fset⟩
    obtain ⟨okq, hfq⟩ := ihq (i + 1) yq E Γ hyq hPq hDq
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yq) := finalCtx_isFormulaSet 8 htbl hP.fset okq
    -- p's list at i + cq + 1 + shiftsV yq
    have hDp₁ : DossF Wd (finalCtx Γ yq) n p (i + cq + 1 + shiftsV yq) := dossF_transport' hndq hDp
    have h4q : cq + 1 + shiftsV yq + 1 ≤ 4 * lq := by
      calc cq + 1 + shiftsV yq + 1 = (cq + 1) + (shiftsV yq + 1) := by ring
        _ ≤ 2 * lq + 2 * lq := add_le_add hcq_le hsq
        _ = 4 * lq := by ring
    have hPp : LenPre lp n (i + cq + 1 + shiftsV yq) E (finalCtx Γ yq) :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left hlpD zero_le)) (le_refl 8)) hP.1,
       (calc i + cq + 1 + shiftsV yq + 5 * lp + 2 = i + (cq + 1 + shiftsV yq) + 5 * lp + 2 := by ring
          _ ≤ i + 4 * lq + 5 * lp + 2 :=
              add_le_add (add_le_add (add_le_add (le_refl i) (le_trans le_self_add h4q)) (le_refl (5 * lp))) (le_refl (2 : V))
          _ ≤ i + 4 * lq + 5 * lp + 2 + (lq + 5) := le_self_add
          _ = i + 5 * (lp + lq + 1) + 2 := by ring
          _ ≤ E := hP.2.1),
       hΓ₁⟩
    obtain ⟨okp, hfp⟩ := ihp _ yp E _ hyp hPp hDp₁
    have hΓ₂ : IsFormulaSet LAct (finalCtx (finalCtx Γ yq) yp) := finalCtx_isFormulaSet 8 htbl hΓ₁ okp
    have hfq₂ : neg LAct (lenFact (bnum lq) (^&(i + 1 + shiftsV yq + shiftsV yp))) ∈ finalCtx (finalCtx Γ yq) yp :=
      lenFact_transport hndp hfq
    have hD₂ : DossF Wd (finalCtx (finalCtx Γ yq) yp) n (p ^⋏ q) (i + shiftsV yq + shiftsV yp) :=
      dossF_transport' hndp (dossF_transport' hndq hD)
    obtain ⟨okTail, hres⟩ := lnBinTail_ok htbl hC htblN hWd hWp hp hq hcq hlp hlq hcq_le hsq hsp (hP.ctx hΓ₂) hfq₂ hfp
      (Or.inl ⟨rfl, hD₂⟩)
    obtain ⟨_, hsh⟩ := lnBinSteps_struct hWp (Or.inl rfl) T n cq lp lq i (shiftsV yq) (shiftsV yp) yq yp hndq hndp
    refine ⟨by rw [lnBinSteps_eq]; exact listOK_appendV okq (listOK_appendV okp okTail), ?_⟩
    rw [hsh, lnBinSteps_eq, finalCtx_appendV, finalCtx_appendV,
      show i + (shiftsV yq + (shiftsV yp + 1)) = i + (shiftsV yq + shiftsV yp) + 1 by ring]
    exact hres
  · -- or
    intro n p q hp hq ihp ihq i y E Γ hy hP hD
    unfold FLenOK at ihp ihq
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.or_iff.mp hy
    rw [formulaLen_or hp.isUFormula hq.isUFormula] at hP ⊢
    set cq := descCountF W n q with hcq'
    set lp := formulaLen LAct p with hlp
    set lq := formulaLen LAct q with hlq
    have hcq : cq = descCountF Wd n q := by rw [hcq', hWp, hWd]; exact descCountF_certPieces hq
    have hcq_le : cq + 1 ≤ 2 * lq := by rw [hcq]; exact descCountF_walk_le htbl hW hWd hq
    obtain ⟨hndq, hsq⟩ := lenFGraph_noDrop_shifts hWp T hq (i + 1) yq hyq
    obtain ⟨hndp, hsp⟩ := lenFGraph_noDrop_shifts hWp T hp _ yp hyp
    obtain ⟨_, _, hDq, hDp⟩ := dossF_or htbl hW hWd hp hq hD
    rw [← hcq] at hDp
    have hlqD : lq ≤ lp + lq + 1 := le_trans le_add_self le_self_add
    have hlpD : lp ≤ lp + lq + 1 := le_trans le_self_add le_self_add
    have h5q : 5 * lq + 1 ≤ 5 * (lp + lq + 1) := by
      rw [show 5 * (lp + lq + 1) = 5 * lq + 1 + (5 * lp + 4) by ring]; exact le_self_add
    have hPq : LenPre lq n (i + 1) E Γ :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left hlqD zero_le)) (le_refl 8)) hP.1,
       le_trans (le_of_eq (show i + 1 + 5 * lq + 2 = i + (5 * lq + 1) + 2 by ring))
         (le_trans (add_le_add (add_le_add (le_refl i) h5q) (le_refl 2)) hP.2.1),
       hP.fset⟩
    obtain ⟨okq, hfq⟩ := ihq (i + 1) yq E Γ hyq hPq hDq
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yq) := finalCtx_isFormulaSet 8 htbl hP.fset okq
    have hDp₁ : DossF Wd (finalCtx Γ yq) n p (i + cq + 1 + shiftsV yq) := dossF_transport' hndq hDp
    have h4q : cq + 1 + shiftsV yq + 1 ≤ 4 * lq := by
      calc cq + 1 + shiftsV yq + 1 = (cq + 1) + (shiftsV yq + 1) := by ring
        _ ≤ 2 * lq + 2 * lq := add_le_add hcq_le hsq
        _ = 4 * lq := by ring
    have hPp : LenPre lp n (i + cq + 1 + shiftsV yq) E (finalCtx Γ yq) :=
      ⟨le_trans (add_le_add (add_le_add (le_refl (2 * n)) (mul_le_mul_of_nonneg_left hlpD zero_le)) (le_refl 8)) hP.1,
       (calc i + cq + 1 + shiftsV yq + 5 * lp + 2 = i + (cq + 1 + shiftsV yq) + 5 * lp + 2 := by ring
          _ ≤ i + 4 * lq + 5 * lp + 2 :=
              add_le_add (add_le_add (add_le_add (le_refl i) (le_trans le_self_add h4q)) (le_refl (5 * lp))) (le_refl (2 : V))
          _ ≤ i + 4 * lq + 5 * lp + 2 + (lq + 5) := le_self_add
          _ = i + 5 * (lp + lq + 1) + 2 := by ring
          _ ≤ E := hP.2.1),
       hΓ₁⟩
    obtain ⟨okp, hfp⟩ := ihp _ yp E _ hyp hPp hDp₁
    have hΓ₂ : IsFormulaSet LAct (finalCtx (finalCtx Γ yq) yp) := finalCtx_isFormulaSet 8 htbl hΓ₁ okp
    have hfq₂ : neg LAct (lenFact (bnum lq) (^&(i + 1 + shiftsV yq + shiftsV yp))) ∈ finalCtx (finalCtx Γ yq) yp :=
      lenFact_transport hndp hfq
    have hD₂ : DossF Wd (finalCtx (finalCtx Γ yq) yp) n (p ^⋎ q) (i + shiftsV yq + shiftsV yp) :=
      dossF_transport' hndp (dossF_transport' hndq hD)
    obtain ⟨okTail, hres⟩ := lnBinTail_ok htbl hC htblN hWd hWp hp hq hcq hlp hlq hcq_le hsq hsp (hP.ctx hΓ₂) hfq₂ hfp
      (Or.inr ⟨rfl, hD₂⟩)
    obtain ⟨_, hsh⟩ := lnBinSteps_struct hWp (Or.inr rfl) T n cq lp lq i (shiftsV yq) (shiftsV yp) yq yp hndq hndp
    refine ⟨by rw [lnBinSteps_eq]; exact listOK_appendV okq (listOK_appendV okp okTail), ?_⟩
    rw [hsh, lnBinSteps_eq, finalCtx_appendV, finalCtx_appendV,
      show i + (shiftsV yq + (shiftsV yp + 1)) = i + (shiftsV yq + shiftsV yp) + 1 by ring]
    exact hres
  · -- all
    intro n p hp ih i y E Γ hy hP hD
    unfold FLenOK at ih
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.all_iff.mp hy
    rw [formulaLen_all hp.isUFormula] at hP ⊢
    set lp := formulaLen LAct p with hlp
    obtain ⟨hndb, hsb⟩ := lenFGraph_noDrop_shifts hWp T hp (i + 1) yb hyb
    obtain ⟨_, _, hDb⟩ := dossF_all htbl hW hWd hp hD
    have hPb : LenPre lp (n + 1) (i + 1) E Γ :=
      ⟨le_trans (le_of_eq (show 2 * (n + 1) + 13 * lp + 8 = 2 * n + (13 * lp + 2) + 8 by ring))
         (le_trans (add_le_add (add_le_add (le_refl (2 * n)) (by rw [show 13 * (lp + 1) = 13 * lp + 2 + 11 by ring]; exact le_self_add))
           (le_refl 8)) hP.1),
       le_trans (le_of_eq (show i + 1 + 5 * lp + 2 = i + (5 * lp + 1) + 2 by ring))
         (le_trans (add_le_add (add_le_add (le_refl i) (by rw [show 5 * (lp + 1) = 5 * lp + 1 + 4 by ring]; exact le_self_add))
           (le_refl 2)) hP.2.1),
       hP.fset⟩
    obtain ⟨okb, hfb⟩ := ih (i + 1) yb E Γ hyb hPb hDb
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yb) := finalCtx_isFormulaSet 8 htbl hP.fset okb
    obtain ⟨okTail, hres⟩ := lnQuantTail_ok htbl hC htblN hWd hWp hp hlp hsb (hP.ctx hΓ₁) hfb
      (Or.inl ⟨rfl, dossF_transport' hndb hD⟩)
    obtain ⟨_, hsh⟩ := lnQuantSteps_struct hWp (Or.inl rfl) T n lp i (shiftsV yb) yb hndb
    refine ⟨by rw [lnQuantSteps_eq]; exact listOK_appendV okb okTail, ?_⟩
    rw [hsh, lnQuantSteps_eq, finalCtx_appendV, ← add_assoc]
    exact hres
  · -- exs
    intro n p hp ih i y E Γ hy hP hD
    unfold FLenOK at ih
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.exs_iff.mp hy
    rw [formulaLen_exs hp.isUFormula] at hP ⊢
    set lp := formulaLen LAct p with hlp
    obtain ⟨hndb, hsb⟩ := lenFGraph_noDrop_shifts hWp T hp (i + 1) yb hyb
    obtain ⟨_, _, hDb⟩ := dossF_exs htbl hW hWd hp hD
    have hPb : LenPre lp (n + 1) (i + 1) E Γ :=
      ⟨le_trans (le_of_eq (show 2 * (n + 1) + 13 * lp + 8 = 2 * n + (13 * lp + 2) + 8 by ring))
         (le_trans (add_le_add (add_le_add (le_refl (2 * n)) (by rw [show 13 * (lp + 1) = 13 * lp + 2 + 11 by ring]; exact le_self_add))
           (le_refl 8)) hP.1),
       le_trans (le_of_eq (show i + 1 + 5 * lp + 2 = i + (5 * lp + 1) + 2 by ring))
         (le_trans (add_le_add (add_le_add (le_refl i) (by rw [show 5 * (lp + 1) = 5 * lp + 1 + 4 by ring]; exact le_self_add))
           (le_refl 2)) hP.2.1),
       hP.fset⟩
    obtain ⟨okb, hfb⟩ := ih (i + 1) yb E Γ hyb hPb hDb
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ yb) := finalCtx_isFormulaSet 8 htbl hP.fset okb
    obtain ⟨okTail, hres⟩ := lnQuantTail_ok htbl hC htblN hWd hWp hp hlp hsb (hP.ctx hΓ₁) hfb
      (Or.inr ⟨rfl, dossF_transport' hndb hD⟩)
    obtain ⟨_, hsh⟩ := lnQuantSteps_struct hWp (Or.inr rfl) T n lp i (shiftsV yb) yb hndb
    refine ⟨by rw [lnQuantSteps_eq]; exact listOK_appendV okb okTail, ?_⟩
    rw [hsh, lnQuantSteps_eq, finalCtx_appendV, ← add_assoc]
    exact hres

/-- **`lenSteps` is applicable and leaves the exact length** (§3.6 "lengths"): with `r`'s walk dossier at
offset `i` in a formula-set context whose cap `E` bounds the arity part (`2n + 13|r| + 8`) and the offset part
(`i + 5|r| + 2`), the list is `ListOK` at cap 8, cut-admitting (`NoDrop'`, tags 0/2/7 only), introduces
`shiftsV + 1 ≤ 2|r|` eigenvariables (one per node — NOT shift-free, the offsets move), has at most `14|r|`
steps, and leaves `lenFact (bnum |r|) &(i + shifts)` — the numeral length in the graph position — in its
final context. -/
theorem lenSteps_ok {tbl N N' B' Wd W T n r i E Γ : V} (htbl : TableOK tbl N) (hC : CertTable tbl)
    (htblN : NumTableOK T N' B') (hWd : Wd = walkPieces) (hWp : W = certPieces) (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 13 * formulaLen LAct r + 8 ≤ E) (hEi : i + 5 * formulaLen LAct r + 2 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hD : DossF Wd Γ n r i) :
    ListOK tbl E ((8 : ℕ) : V) Γ (lenSteps W T n r i) ∧ NoDrop' (lenSteps W T n r i) ∧
    shiftsV (lenSteps W T n r i) + 1 ≤ 2 * formulaLen LAct r ∧ len (lenSteps W T n r i) ≤ 14 * formulaLen LAct r ∧
    neg LAct (lenFact (bnum (formulaLen LAct r)) (^&(i + shiftsV (lenSteps W T n r i)))) ∈ finalCtx Γ (lenSteps W T n r i) := by
  have h := lenFGraph_ok htbl hC htblN hWd hWp hr
  unfold FLenOK at h
  obtain ⟨hok, hf⟩ := h i _ E Γ (lenSteps_graph hr) ⟨hE, hEi, hΓ⟩ hD
  obtain ⟨hnd, hs, hl⟩ := lenSteps_struct hWp T hr i
  exact ⟨hok, hnd, hs, hl, hf⟩

end lenFOK

/-! ### 5.9 The size discipline and the cost of `lenSteps` -/

section lenCost

/-- `SizeOK` is Δ₁ (needed as a Π₁ induction motive below). -/
instance stepSizeOK_definable : 𝚫₁-Relation₃ (StepSizeOK : V → V → V → Prop) := by
  unfold StepSizeOK sGoalS sGoalU sLemA sLemD sTag; definability
instance sizeOK_definable : 𝚫₁-Relation₃ (SizeOK : V → V → V → Prop) := by
  unfold SizeOK; definability

/-- The uniform size bounds of the closed `sLemma` facts at arguments `≤ L`: `Q = B'·cTE L` on the
formulas, `D = (L + 1)(‖L‖ + 2)·nodeCost N' B' (cTE L)` on the derivations. -/
noncomputable def lenQ (B' L : V) : V := B' * cTE L
noncomputable def lenD (N' B' L : V) : V := (L + 1) * (‖L‖ + 2) * nodeCost N' B' (cTE L)

lemma NumTableOK.peq {tbl N B : V} (h : NumTableOK tbl N B) : formulaLen LAct (Peq : V) ≤ B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPeq, -, -, -⟩ := h
  exact hPeq

lemma succ_fits {T N' B' L z : V} (htblN : NumTableOK T N' B') (hz : z ≤ L) :
    formulaLen LAct (succFact z) ≤ lenQ B' L ∧ dlen TAct (succCode T z) ≤ lenD N' B' L := by
  have hz1 : ‖z + 1‖ ≤ ‖L + 1‖ := length_monotone (add_le_add hz (le_refl (1 : V)))
  have hE : 6 * ‖z + 1‖ + 3 ≤ cTE L := by
    unfold cTE
    calc 6 * ‖z + 1‖ + 3 ≤ 12 * ‖L + 1‖ + 5 :=
          add_le_add (le_trans (mul_le_mul_of_nonneg_left hz1 zero_le) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num)
      _ ≤ 2 * L + 12 * ‖L + 1‖ + 5 := by rw [add_assoc]; exact le_add_self
  refine ⟨formulaLen_succFact_le htblN.peq hE, ?_⟩
  refine le_trans (dlen_succCode_le htblN z) ?_
  unfold lenD
  calc (‖z‖ + 1) * nodeCost N' B' (6 * ‖z + 1‖ + 3)
      ≤ (L + 1) * nodeCost N' B' (cTE L) :=
        mul_le_mul (add_le_add (le_trans (length_le z) hz) (le_refl 1)) (nodeCost_mono hE) zero_le zero_le
    _ = (L + 1) * 1 * nodeCost N' B' (cTE L) := by ring
    _ ≤ (L + 1) * (‖L‖ + 2) * nodeCost N' B' (cTE L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans (by norm_num) le_add_self) zero_le) zero_le

lemma add_fits {T N' B' L a b : V} (htblN : NumTableOK T N' B') (hab : a + b ≤ L) :
    formulaLen LAct (addFact a b) ≤ lenQ B' L ∧ dlen TAct (addCode T a b) ≤ lenD N' B' L := by
  have hab' : ‖a + b‖ ≤ ‖L‖ := length_monotone hab
  have hE : 12 * ‖a + b‖ + 3 ≤ cTE L := by
    unfold cTE
    calc 12 * ‖a + b‖ + 3 ≤ 12 * ‖L + 1‖ + 5 :=
          add_le_add (mul_le_mul_of_nonneg_left (le_trans hab' (length_monotone le_self_add)) zero_le) (by norm_num)
      _ ≤ 2 * L + 12 * ‖L + 1‖ + 5 := by rw [add_assoc]; exact le_add_self
  refine ⟨formulaLen_addFact_le htblN.peq hE, ?_⟩
  refine le_trans (dlen_addCode_le htblN a b) ?_
  unfold lenD
  exact mul_le_mul (mul_le_mul (add_le_add (le_trans (length_le a) (le_trans le_self_add hab)) (le_refl 1))
    (add_le_add hab' (le_refl 2)) zero_le zero_le) (nodeCost_mono hE) zero_le zero_le

lemma cTEq_fits {T N' B' L z : V} (htblN : NumTableOK T N' B') (hz : z ≤ L) :
    formulaLen LAct (cTEqFact z) ≤ lenQ B' L ∧ dlen TAct (cTEqCode T z) ≤ lenD N' B' L := by
  refine ⟨le_trans (formulaLen_cTEqFact_le htblN.peq) (mul_le_mul_of_nonneg_left (cTE_mono hz) zero_le), ?_⟩
  refine le_trans (dlen_cTEqCode_le htblN z) ?_
  unfold lenD
  exact mul_le_mul (mul_le_mul (add_le_add hz (le_refl 1)) (add_le_add (length_monotone hz) (le_refl 2)) zero_le zero_le)
    (nodeCost_mono (cTE_mono hz)) zero_le zero_le

/-! The lists are size-disciplined at `(lenQ B' L, lenD N' B' L)` whenever their numeral arguments are `≤ L`. -/

lemma sizeOK_lnLeafSteps {W T N' B' L c z i : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (hc : c = 153 ∨ c = 154)
    (hz : z + 1 ≤ L) : SizeOK (lenQ B' L) (lenD N' B' L) (lnLeafSteps W T c z i) := by
  obtain ⟨hA, hd⟩ := cTEq_fits (B' := B') htblN hz
  exact sizeOK_cons (stepSizeOK_horn2 (ctag_termLenTotal hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ctag_lnLeafRow hWp hc _))
    (sizeOK_cons (stepSizeOK_sLemma hA hd) (sizeOK_cons (stepSizeOK_horn0 (ctag_eqTrans hWp _))
    (sizeOK_single (stepSizeOK_horn0 (ctag_congTLenNum hWp _))))))
lemma sizeOK_lnNilSteps {W N' B' L : V} (hWp : W = certPieces) : SizeOK (lenQ B' L) (lenD N' B' L) (lnNilSteps W) :=
  sizeOK_cons (stepSizeOK_horn0 (ctag_termLenVecNil hWp _)) (sizeOK_single (stepSizeOK_horn0 (ctag_listSumNil hWp _)))
lemma sizeOK_lnAdjTail {W T N' B' L n m ct lt σ' i st sv : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B')
    (hs : lt + σ' ≤ L) : SizeOK (lenQ B' L) (lenD N' B' L) (lnAdjTail W T n m ct lt σ' i st sv) := by
  obtain ⟨hA, hd⟩ := add_fits (B' := B') htblN hs
  exact sizeOK_cons (stepSizeOK_horn2 (ctag_cert17 hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ctag_cert38 hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ctag_cert39 hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ctag_termLenVecAdj hWp _))
    (sizeOK_cons (stepSizeOK_sLemma hA hd) (sizeOK_single (stepSizeOK_horn0 (ctag_listSumAdjI hWp _)))))))
lemma sizeOK_lnFuncTail {W T N' B' L k f σ i sv : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (hσ : σ ≤ L) :
    SizeOK (lenQ B' L) (lenD N' B' L) (lnFuncTail W T k f σ i sv) := by
  obtain ⟨hA, hd⟩ := succ_fits (B' := B') htblN hσ
  exact sizeOK_cons (stepSizeOK_horn0 (ctag_certFuncRow hWp _ _ _)) (sizeOK_cons (stepSizeOK_horn2 (ctag_termLenTotal hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ctag_termLenFuncCert hWp _)) (sizeOK_cons (stepSizeOK_sLemma hA hd)
    (sizeOK_cons (stepSizeOK_horn0 (ctag_eqTrans hWp _)) (sizeOK_single (stepSizeOK_horn0 (ctag_congTLenNum hWp _)))))))
lemma sizeOK_lnConstSteps {W N' B' L c i : V} (hWp : W = certPieces) (hc : c = 147 ∨ c = 148) :
    SizeOK (lenQ B' L) (lenD N' B' L) (lnConstSteps W c i) :=
  sizeOK_cons (stepSizeOK_horn2 (ctag_formulaLenTotal hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ctag_lnConstRow hWp hc _))
    (sizeOK_single (stepSizeOK_horn0 (ctag_congLenNum hWp _))))
lemma sizeOK_lnQuantTail {W T N' B' L c n lp i sb : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (hc : c = 151 ∨ c = 152)
    (hlp : lp ≤ L) : SizeOK (lenQ B' L) (lenD N' B' L) (lnQuantTail W T c n lp i sb) := by
  obtain ⟨hA, hd⟩ := succ_fits (B' := B') htblN hlp
  exact sizeOK_cons (stepSizeOK_horn2 (ctag_formulaLenTotal hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ctag_lnQuantRow hWp hc _))
    (sizeOK_cons (stepSizeOK_sLemma hA hd) (sizeOK_cons (stepSizeOK_horn0 (ctag_eqTrans hWp _))
    (sizeOK_single (stepSizeOK_horn0 (ctag_congLenNum hWp _))))))
lemma sizeOK_lnBinTail {W T N' B' L c n cq lp lq i sq sp : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B')
    (hc : c = 149 ∨ c = 150) (hs : lp + lq ≤ L) : SizeOK (lenQ B' L) (lenD N' B' L) (lnBinTail W T c n cq lp lq i sq sp) := by
  obtain ⟨hA₁, hd₁⟩ := add_fits (B' := B') htblN hs
  obtain ⟨hA₂, hd₂⟩ := succ_fits (B' := B') htblN hs
  exact sizeOK_cons (stepSizeOK_horn2 (ctag_formulaLenTotal hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ctag_lnBinRow hWp hc _))
    (sizeOK_cons (stepSizeOK_sLemma hA₁ hd₁) (sizeOK_cons (stepSizeOK_horn0 (ctag_congSucc hWp _))
    (sizeOK_cons (stepSizeOK_sLemma hA₂ hd₂) (sizeOK_cons (stepSizeOK_horn0 (ctag_eqTrans hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ctag_eqTrans hWp _)) (sizeOK_single (stepSizeOK_horn0 (ctag_congLenNum hWp _)))))))))
lemma sizeOK_lnAtomTail {W T N' B' L c k R σ i sv : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (hc : c = 142 ∨ c = 143)
    (hσ : σ ≤ L) : SizeOK (lenQ B' L) (lenD N' B' L) (lnAtomTail W T c k R σ i sv) := by
  obtain ⟨hA, hd⟩ := succ_fits (B' := B') htblN hσ
  exact sizeOK_cons (stepSizeOK_horn0 (ctag_certRelRow hWp _ _)) (sizeOK_cons (stepSizeOK_horn2 (ctag_formulaLenTotal hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ctag_lnAtomRow hWp hc _)) (sizeOK_cons (stepSizeOK_sLemma hA hd)
    (sizeOK_cons (stepSizeOK_horn0 (ctag_eqTrans hWp _)) (sizeOK_single (stepSizeOK_horn0 (ctag_congLenNum hWp _)))))))

set_option maxHeartbeats 2000000 in
/-- The term/vector lists are size-disciplined at any `L ≥ |t|` (`≥ Σ` at the vector level). -/
lemma lenTGraph_sizeOK {W T N' B' : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (n L : V) :
    ∀ t, IsSemiterm LAct n t → termLen LAct t ≤ L → ∀ i y : V, LenTGraph W T n t i y → SizeOK (lenQ B' L) (lenD N' B' L) y := by
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_
  · simp only [LenTGraph]; definability
  · intro z _ hL i y hy
    rw [LenTGraph.bvar_iff.mp hy]; rw [termLen_bvar] at hL
    exact sizeOK_lnLeafSteps hWp htblN (Or.inl rfl) hL
  · intro a hL i y hy
    rw [LenTGraph.fvar_iff.mp hy]; rw [termLen_fvar] at hL
    exact sizeOK_lnLeafSteps hWp htblN (Or.inr rfl) hL
  · intro k f v hkf hv ih hL i y hy
    have hvlen : len v = k := hv.lh
    have key : ∀ m ≤ k, IsUTermVec LAct m (takeLast v m) ∧ (listSum (termLenVec LAct m (takeLast v m)) ≤ L →
        ∀ i z : V, LenVGraph W T n k v m i z → SizeOK (lenQ B' L) (lenD N' B' L) z) := by
      intro m
      induction m using ISigma1.pi1_succ_induction with
      | hP => simp only [LenVGraph]; definability
      | zero =>
        intro _
        refine ⟨by simp, ?_⟩
        intro _ i z hz
        rw [LenVGraph.zero_iff.mp hz]
        exact sizeOK_lnNilSteps hWp
      | succ m ihm =>
        intro hm
        have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
        have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
        have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
        have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
        obtain ⟨hU, hrest⟩ := ihm (le_trans le_self_add hm)
        have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
          rw [takeLast_succ_of_lt hjk, hvlen]
        refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
        intro hL i z hz
        rw [htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hL
        obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
        have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
          nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
        rw [hnth'] at hyt hyv ⊢
        rw [lnAdjSteps_eq]
        exact sizeOK_appendV (ih _ hlt (le_trans le_self_add hL) (i + 1) yt hyt)
          (sizeOK_appendV (hrest (le_trans le_add_self hL) _ yv hyv) (sizeOK_lnAdjTail hWp htblN hL))
    obtain ⟨yv, _, hyv, rfl⟩ := LenTGraph.func_iff.mp hy
    have htl : takeLast v k = v := by rw [← hvlen]; exact takeLast_len_self v
    obtain ⟨_, hrest⟩ := key k le_rfl
    rw [htl] at hrest
    rw [termLen_func hkf hv.isUTerm] at hL
    rw [lnFuncSteps_eq]
    exact sizeOK_appendV (hrest (le_trans le_self_add hL) (i + 1) yv hyv) (sizeOK_lnFuncTail hWp htblN (le_trans le_self_add hL))

lemma lenVGraph_sizeOK {W T N' B' : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (n L : V) {k v : V}
    (hv : IsSemitermVec LAct k n v) : ∀ m ≤ k, listSum (termLenVec LAct m (takeLast v m)) ≤ L →
      ∀ i z : V, LenVGraph W T n k v m i z → SizeOK (lenQ B' L) (lenD N' B' L) z := by
  have hvlen : len v = k := hv.lh
  intro m
  induction m using ISigma1.pi1_succ_induction with
  | hP => simp only [LenVGraph]; definability
  | zero =>
    intro _ _ i z hz
    rw [LenVGraph.zero_iff.mp hz]
    exact sizeOK_lnNilSteps hWp
  | succ m ihm =>
    intro hm hL i z hz
    have hjk : m < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one m) hm
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hm
    have hlt : k - (m + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (m + 1)] := hv.nth hlt
    have hU : IsUTermVec LAct m (takeLast v m) := (lenVGraph_len W T n hv m (le_trans le_self_add hm)).1
    have htake : takeLast v (m + 1) = v.[k - (m + 1)] ∷ takeLast v m := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    rw [htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin] at hL
    obtain ⟨yt, yv, _, _, hyt, hyv, rfl⟩ := LenVGraph.succ_iff.mp hz
    have hnth' : nthFromEnd v m = v.[k - (m + 1)] :=
      nthFromEnd_eq (a := k - (m + 1)) (by rw [hvlen, tsub_add_cancel_of_le hm])
    rw [hnth'] at hyt hyv ⊢
    rw [lnAdjSteps_eq]
    exact sizeOK_appendV (lenTGraph_sizeOK hWp htblN n L _ ht (le_trans le_self_add hL) (i + 1) yt hyt)
      (sizeOK_appendV (ihm (le_trans le_self_add hm) (le_trans le_add_self hL) _ yv hyv) (sizeOK_lnAdjTail hWp htblN hL))

set_option maxHeartbeats 2000000 in
/-- The formula lists are size-disciplined at any `L ≥ |r|`. -/
lemma lenFGraph_sizeOK {W T N' B' : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (L : V) :
    ∀ {n r : V}, IsSemiformula LAct n r → formulaLen LAct r ≤ L →
      ∀ i y : V, LenFGraph W T n r i y → SizeOK (lenQ B' L) (lenD N' B' L) y := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ formulaLen LAct r ≤ L → ∀ i y : V, LenFGraph W T n r i y → SizeOK (lenQ B' L) (lenD N' B' L) y)
  · simp only [LenFGraph]; definability
  · intro n k R v hkR hv hL i y hy
    rw [LenFGraph.rel_iff.mp hy, lnAtomSteps_eq]
    rw [formulaLen_rel hkR hv.isUTerm] at hL
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hV := lenVGraph_sizeOK hWp htblN n L hv k le_rfl
    rw [htl] at hV
    exact sizeOK_appendV (hV (le_trans le_self_add hL) (i + 1) _ (lenV_graph hv le_rfl))
      (sizeOK_lnAtomTail hWp htblN (Or.inl rfl) (le_trans le_self_add hL))
  · intro n k R v hkR hv hL i y hy
    rw [LenFGraph.nrel_iff.mp hy, lnAtomSteps_eq]
    rw [formulaLen_nrel hkR hv.isUTerm] at hL
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hV := lenVGraph_sizeOK hWp htblN n L hv k le_rfl
    rw [htl] at hV
    exact sizeOK_appendV (hV (le_trans le_self_add hL) (i + 1) _ (lenV_graph hv le_rfl))
      (sizeOK_lnAtomTail hWp htblN (Or.inr rfl) (le_trans le_self_add hL))
  · intro n _ i y hy
    rw [LenFGraph.verum_iff.mp hy]; exact sizeOK_lnConstSteps hWp (Or.inl rfl)
  · intro n _ i y hy
    rw [LenFGraph.falsum_iff.mp hy]; exact sizeOK_lnConstSteps hWp (Or.inr rfl)
  · intro n p q hp hq ihp ihq hL i y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.and_iff.mp hy
    rw [formulaLen_and hp.isUFormula hq.isUFormula] at hL
    rw [lnBinSteps_eq]
    exact sizeOK_appendV (ihq (le_trans (le_trans le_add_self le_self_add) hL) _ _ hyq)
      (sizeOK_appendV (ihp (le_trans (le_trans le_self_add le_self_add) hL) _ _ hyp)
        (sizeOK_lnBinTail hWp htblN (Or.inl rfl) (le_trans le_self_add hL)))
  · intro n p q hp hq ihp ihq hL i y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := LenFGraph.or_iff.mp hy
    rw [formulaLen_or hp.isUFormula hq.isUFormula] at hL
    rw [lnBinSteps_eq]
    exact sizeOK_appendV (ihq (le_trans (le_trans le_add_self le_self_add) hL) _ _ hyq)
      (sizeOK_appendV (ihp (le_trans (le_trans le_self_add le_self_add) hL) _ _ hyp)
        (sizeOK_lnBinTail hWp htblN (Or.inr rfl) (le_trans le_self_add hL)))
  · intro n p hp ih hL i y hy
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.all_iff.mp hy
    rw [formulaLen_all hp.isUFormula] at hL
    rw [lnQuantSteps_eq]
    exact sizeOK_appendV (ih (le_trans le_self_add hL) _ _ hyb) (sizeOK_lnQuantTail hWp htblN (Or.inl rfl) (le_trans le_self_add hL))
  · intro n p hp ih hL i y hy
    obtain ⟨yb, _, hyb, rfl⟩ := LenFGraph.exs_iff.mp hy
    rw [formulaLen_exs hp.isUFormula] at hL
    rw [lnQuantSteps_eq]
    exact sizeOK_appendV (ih (le_trans le_self_add hL) _ _ hyb) (sizeOK_lnQuantTail hWp htblN (Or.inr rfl) (le_trans le_self_add hL))

theorem sizeOK_lenSteps {W T N' B' n r i : V} (hWp : W = certPieces) (htblN : NumTableOK T N' B') (hr : IsSemiformula LAct n r) :
    SizeOK (lenQ B' (formulaLen LAct r)) (lenD N' B' (formulaLen LAct r)) (lenSteps W T n r i) :=
  lenFGraph_sizeOK hWp htblN _ hr le_rfl i _ (lenSteps_graph hr)

lemma ctxBoundG_mono_len {G Γ L L' : V} (h : L ≤ L') : ctxBoundG G Γ L ≤ ctxBoundG G Γ L' := by
  unfold ctxBoundG
  exact add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right h zero_le))
    (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul h h zero_le zero_le) h) zero_le)

/-- **The cost of `lenSteps`**: `14|r|` size-disciplined steps at cap 8 — `Frag1`'s `costSum_le_of_sizeOK` at
`L = 14|r|`, `Q = B'·cTE |r|` (the closed numeral facts), `D = (|r| + 1)(‖|r|‖ + 2)·nodeCost N' B' (cTE |r|)`
(their derivations, cubic in `‖|r|‖` per `NumSteps`). -/
theorem costSum_lenSteps_le {tbl N N' B' B Wd W T n r i E Γ : V} (htbl : TableOK tbl N) (hC : CertTable tbl)
    (htblN : NumTableOK T N' B') (hWd : Wd = walkPieces) (hWp : W = certPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hr : IsSemiformula LAct n r)
    (hE : 2 * n + 13 * formulaLen LAct r + 8 ≤ E) (hEi : i + 5 * formulaLen LAct r + 2 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hD : DossF Wd Γ n r i) :
    costSum N E Γ (lenSteps W T n r i) ≤
      14 * formulaLen LAct r * (costK N E B 8 (lenQ B' (formulaLen LAct r)) (lenD N' B' (formulaLen LAct r)) +
        (3 * ((8 : ℕ) : V) + 11) * (ctxBoundG (growK B E (lenQ B' (formulaLen LAct r))) Γ (14 * formulaLen LAct r) +
          (fvOccS LAct Γ + 14 * formulaLen LAct r * growK B E (lenQ B' (formulaLen LAct r))))) := by
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  obtain ⟨hok, _, _, hl, _⟩ := lenSteps_ok htbl hC htblN hWd hWp hr hE hEi hΓ hD
  have hsz := sizeOK_lenSteps (B' := B') hWp htblN hr (i := i)
  refine le_trans (costSum_le_of_sizeOK 8 hE1 htbl hBt hok hsz) ?_
  refine mul_le_mul hl ?_ zero_le zero_le
  refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (add_le_add (ctxBoundG_mono_len hl)
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hl zero_le))) zero_le)

end lenCost

/-! ### 4.8 Status of `certSubst` / `certFree` (2026-09-14, after Part 5 — `lenSteps` DONE, see §5.0–5.9)

**`lenSteps` LANDED** (Part 5): the term/vector fixpoint `LenT` (`lenT`/`lenV`) and the formula fixpoint
`LenF` (`lenSteps W T n r i`, `T` the `NumSteps` table), NOT shift-free — one `formulaLenTotal`/`termLenTotal`
eigenvariable per node and one `adjoinTotal` per vector entry, `shiftsV + 1 ≤ 2|r|`, `len ≤ 14|r|` — with
`lenSteps_ok` (`ListOK` at cap 8, `NoDrop'`, `lenFact (bnum |r|) &(i + shiftsV (lenSteps …))` in the final
context; the numeral in the GRAPH position, which `setLenInsertLe`/`dlenExs` consume; the offsets move, so
the consumer reads the root at `&(i + shiftsV …)`) and `costSum_lenSteps_le` (`Frag1`'s size discipline at
`Q = B'·cTE |r|`, `D = (|r| + 1)(‖|r|‖ + 2)·nodeCost N' B' (cTE |r|)`, `14|r|` steps — cubic in `‖|r|‖`).
The rows §4.7 asked for were APPENDED (index-stable): `congAdd` (cIdx 183, `x = x' → y = y' → x + y = x' + y'`),
`congSucc` (184, the one the binary node uses — `congAdd` at the closed `𝟏` would need the closed-constant
witness), and `listSumAdjI` (185, `listSumDef s M → adjoinDef M' l M → l + s = s' → listSumDef s' M'`: the
table's `listSumAdj` has all three `listSumDef` facts as ANTECEDENTS, so no `listSumDef s' M'` was derivable
for a non-empty `M'` — the atom case needed the intro form, at NUMERAL sums via `addFact`).

**`certSubst w` / `certFree` — NOT started (budget).** §4.7's three obstacles stand; what Part 5 now
provides towards them: (1) the template for a NON-shift-free pass whose offsets move with `shiftsV`
(`LenT`/`LenF`: sub-call offsets `i + … + shiftsV yq` in the blueprint, existence through `shiftsV_le_len`
+ the `W`-free length bounds, the `_ok` by `dossF_transport'` over `NoDrop'` lists and the per-fact
`*_transport` lemmas of §5.7) — exactly the discipline `certSubst`'s `qVec` totality steps need; (2) the
`congAdj` row (182) for the bvar leaf's parent-vector repair. Still to design: the `w`/`wt` parameter slot in
a sibling fixpoint, the image offset increment `descCountT (termSubst wv t)` per node, and `certFree` as
`substsSubsts1` + `freeCert` on top of `certSubst` at `qVec (fvar 0)` (`DESIGN_fragments` §4.5 item 2).
-/

/-! ## Part 6 — `certSubst`: the certified substitution (§3.6 "substs")

### 6.0 The `nth` chain: `nthFact &e ⟨v⟩ (cT d)` for the entry `d` of a walked (sub-)vector

The walk leaves adjoin facts only (`adjF &off &(off+1) ⟨tail⟩`, `dossV_succ`); the substitution rows
need `nthFact e w z` (`termSubstBvarCert`). The chain descends `d` adjoins from the sub-vector at
`&off` (the last `j` entries of `w`, its head `w.[s]`) to the entry, reads `nthAdjoinZero` there and
climbs back with `nthAdjoinSucc`, deriving `nthFact &e &off (cT d)` for `e` the walk offset of the
entry `w.[s + d]`. A fixpoint on `⟪s, j, d, off, e, y⟫` (parameters `W`, the entries' arity `m`, the
vector `w`): the sub-call is the DEEPER level `(s + 1, j − 1, d − 1, off + 1 + descCountT w.[s])`,
the offsets computed by addition only (no subtraction anywhere in the blueprint). -/

section nthChainBuilders

/-- The zero step at the sub-vector `&off` with tail `⟨tail⟩ = vRef (off + 1 + c) j'`:
`nthAdjoinZero [⟨tail⟩, &(off+1), &off]` → `nthFact &(off+1) &off 𝟎`. -/
noncomputable def ncZeroSteps (W c off j' : V) : V :=
  ?[mkStep W 179 ?[vRef (off + 1 + c) j', ^&(off + 1), ^&off]]

noncomputable def ncZeroStepsDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W c off j'. ∃ r, !vRefDef r (off + 1 + c) j' ∧ ∃ f₁, !qqFvarDef f₁ (off + 1) ∧ ∃ f₀, !qqFvarDef f₀ off ∧
    ∃ e₀, !mkVec₂Def e₀ f₁ f₀ ∧ ∃ e, !adjoinDef e r e₀ ∧ ∃ s, !mkStepDef s W 179 e ∧ !mkVec₁Def y s”

instance ncZeroSteps_defined : 𝚺₁-Function₄ (ncZeroSteps : V → V → V → V → V) via ncZeroStepsDef := .mk
  fun v ↦ by simp [ncZeroStepsDef, ncZeroSteps, numeral_eq_natCast, vRef_defined.iff, mkStep_defined.iff]
instance ncZeroSteps_definable : 𝚺₁-Function₄ (ncZeroSteps : V → V → V → V → V) := ncZeroSteps_defined.to_definable

/-- The climbing step at the sub-vector `&off` after the deeper chain `y'`:
`nthAdjoinSucc [cT d', ⟨tail⟩, &(off+1), &off, &e]` → `nthFact &e &off (cT d' + 1)`. -/
noncomputable def ncSuccSteps (W c off j' d' e y' : V) : V :=
  appendV y' ?[mkStep W 180 ?[cTV d', vRef (off + 1 + c) j', ^&(off + 1), ^&off, ^&e]]

noncomputable def ncSuccStepsDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W c off j' d' e y'. ∃ cd, !cTVGraph cd d' ∧ ∃ r, !vRefDef r (off + 1 + c) j' ∧ ∃ f₁, !qqFvarDef f₁ (off + 1) ∧
    ∃ f₀, !qqFvarDef f₀ off ∧ ∃ fe, !qqFvarDef fe e ∧
    ∃ e₀, !mkVec₂Def e₀ f₀ fe ∧ ∃ e₁, !adjoinDef e₁ f₁ e₀ ∧ ∃ e₂, !adjoinDef e₂ r e₁ ∧ ∃ ev, !adjoinDef ev cd e₂ ∧
    ∃ s, !mkStepDef s W 180 ev ∧ ∃ l, !mkVec₁Def l s ∧ !appendVDef y y' l”

instance ncSuccSteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ ncSuccSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) ncSuccStepsDef := .mk
  fun v ↦ by
    simp [ncSuccStepsDef, ncSuccSteps, numeral_eq_natCast, cTV.defined.iff, vRef_defined.iff, mkStep_defined.iff,
      appendV_defined.iff]
instance ncSuccSteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ ncSuccSteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  ncSuccSteps_defined.to_definable

lemma len_ncZeroSteps (W c off j' : V) : len (ncZeroSteps W c off j') = 1 := by simp [ncZeroSteps]
lemma len_ncSuccSteps (W c off j' d' e y' : V) : len (ncSuccSteps W c off j' d' e y') = len y' + 1 := by
  rw [ncSuccSteps, len_appendV, len_adjoin, len_nil, zero_add]

end nthChainBuilders

namespace NthC

/-- The cases on the unpacked tuple. -/
def Cases (W m w : V) (C : Set V) (s j d off e y : V) : Prop :=
  (d = 0 ∧ ∃ j' < j, j = j' + 1 ∧ e = off + 1 ∧ y = ncZeroSteps W (descCountT W m w.[s]) off j') ∨
  (∃ d' < d, d = d' + 1 ∧ ∃ j' < j, j = j' + 1 ∧ ∃ y' ≤ y,
    ⟪s + 1, j', d', off + 1 + descCountT W m w.[s], e, y'⟫ ∈ C ∧
    y = ncSuccSteps W (descCountT W m w.[s]) off j' d' e y')

def Phi (W m w : V) (C : Set V) (pr : V) : Prop :=
  ∃ s ≤ pr, ∃ q₁ ≤ pr, pr = ⟪s, q₁⟫ ∧ ∃ j ≤ q₁, ∃ q₂ ≤ q₁, q₁ = ⟪j, q₂⟫ ∧ ∃ d ≤ q₂, ∃ q₃ ≤ q₂, q₂ = ⟪d, q₃⟫ ∧
  ∃ off ≤ q₃, ∃ q₄ ≤ q₃, q₃ = ⟪off, q₄⟫ ∧ ∃ e ≤ q₄, ∃ y ≤ q₄, q₄ = ⟪e, y⟫ ∧ Cases W m w C s j d off e y

lemma phi_unpack (W m w : V) (C : Set V) (pr : V) :
    Phi W m w C pr ↔ ∃ s j d off e y, pr = ⟪s, j, d, off, e, y⟫ ∧ Cases W m w C s j d off e y := by
  constructor
  · rintro ⟨s, _, q₁, _, rfl, j, _, q₂, _, rfl, d, _, q₃, _, rfl, off, _, q₄, _, rfl, e, _, y, _, rfl, h⟩
    exact ⟨s, j, d, off, e, y, rfl, h⟩
  · rintro ⟨s, j, d, off, e, y, rfl, h⟩
    exact ⟨s, le_pair_left _ _, _, le_pair_right _ _, rfl, j, le_pair_left _ _, _, le_pair_right _ _, rfl,
      d, le_pair_left _ _, _, le_pair_right _ _, rfl, off, le_pair_left _ _, _, le_pair_right _ _, rfl,
      e, le_pair_left _ _, y, le_pair_right _ _, rfl, h⟩

lemma phi_of_cases {W m w : V} {C : Set V} {s j d off e y : V} (h : Cases W m w C s j d off e y) :
    Phi W m w C ⟪s, j, d, off, e, y⟫ := (phi_unpack W m w C _).mpr ⟨s, j, d, off, e, y, rfl, h⟩

lemma cases_of_phi {W m w : V} {C : Set V} {s j d off e y : V} (h : Phi W m w C ⟪s, j, d, off, e, y⟫) :
    Cases W m w C s j d off e y := by
  obtain ⟨s', j', d', off', e', y', h₁, h⟩ := (phi_unpack W m w C _).mp h
  rw [pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff, pair_ext_iff] at h₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h₁
  exact h

noncomputable def blueprint : Fixpoint.Blueprint 3 := ⟨.mkDelta
  (.mkSigma “pr C W m w.
    ∃ s <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr s q₁ ∧ ∃ j <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ j q₂ ∧ ∃ d <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ d q₃ ∧
    ∃ off <⁺ q₃, ∃ q₄ <⁺ q₃, !pairDef q₃ off q₄ ∧ ∃ e <⁺ q₄, ∃ y <⁺ q₄, !pairDef q₄ e y ∧
    ∃ t, !nthDef t w s ∧ ∃ c, !descCountTDef c W m t ∧
    ( (d = 0 ∧ ∃ j' < j, j = j' + 1 ∧ e = off + 1 ∧ ∃ z, !ncZeroStepsDef z W c off j' ∧ y = z) ∨
      (∃ d' < d, d = d' + 1 ∧ ∃ j' < j, j = j' + 1 ∧ ∃ y' <⁺ y,
        ∃ p₄, !pairDef p₄ e y' ∧ ∃ p₃, !pairDef p₃ (off + 1 + c) p₄ ∧ ∃ p₂, !pairDef p₂ d' p₃ ∧ ∃ p₁, !pairDef p₁ j' p₂ ∧
        :⟪s + 1, p₁⟫:∈ C ∧ ∃ z, !ncSuccStepsDef z W c off j' d' e y' ∧ y = z) )”)
  (.mkPi “pr C W m w.
    ∃ s <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr s q₁ ∧ ∃ j <⁺ q₁, ∃ q₂ <⁺ q₁, !pairDef q₁ j q₂ ∧ ∃ d <⁺ q₂, ∃ q₃ <⁺ q₂, !pairDef q₂ d q₃ ∧
    ∃ off <⁺ q₃, ∃ q₄ <⁺ q₃, !pairDef q₃ off q₄ ∧ ∃ e <⁺ q₄, ∃ y <⁺ q₄, !pairDef q₄ e y ∧
    ∀ t, !nthDef t w s → ∀ c, !descCountTDef c W m t →
    ( (d = 0 ∧ ∃ j' < j, j = j' + 1 ∧ e = off + 1 ∧ ∀ z, !ncZeroStepsDef z W c off j' → y = z) ∨
      (∃ d' < d, d = d' + 1 ∧ ∃ j' < j, j = j' + 1 ∧ ∃ y' <⁺ y,
        ∀ p₄, !pairDef p₄ e y' → ∀ p₃, !pairDef p₃ (off + 1 + c) p₄ → ∀ p₂, !pairDef p₂ d' p₃ → ∀ p₁, !pairDef p₁ j' p₂ →
        :⟪s + 1, p₁⟫:∈ C ∧ ∀ z, !ncSuccStepsDef z W c off j' d' e y' → y = z) )”)⟩

set_option maxHeartbeats 4000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1) (v 2)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, nth_defined.iff, descCountT_defined.iff, ncZeroSteps_defined.iff, ncSuccSteps_defined.iff,
        numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, Cases, nth_defined.iff, descCountT_defined.iff, ncZeroSteps_defined.iff,
        ncSuccSteps_defined.iff, numeral_eq_natCast]
  monotone := by
    intro C C' hC v pr h
    change Phi (v 0) (v 1) (v 2) C pr at h
    change Phi (v 0) (v 1) (v 2) C' pr
    rw [phi_unpack] at h ⊢
    obtain ⟨s, j, d, off, e, y, rfl, h⟩ := h
    refine ⟨s, j, d, off, e, y, rfl, ?_⟩
    rcases h with h | ⟨d', hd', rfl, j', hj', rfl, y', hy', h₁, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨d', hd', rfl, j', hj', rfl, y', hy', hC h₁, rfl⟩

instance : construction.Finite V where
  finite := by
    intro C v pr h
    change Phi (v 0) (v 1) (v 2) C pr at h
    change ∃ m, Phi (v 0) (v 1) (v 2) {y ∈ C | y < m} pr
    rw [phi_unpack] at h
    simp only [phi_unpack]
    obtain ⟨s, j, d, off, e, y, rfl, h⟩ := h
    rcases h with h | ⟨d', hd', hd, j', hj', hj, y', hy', h₁, hy⟩
    · exact ⟨0, s, j, d, off, e, y, rfl, Or.inl h⟩
    · exact ⟨⟪s + 1, j', d', off + 1 + descCountT (v 0) (v 1) (v 2).[s], e, y'⟫ + 1, s, j, d, off, e, y, rfl,
        Or.inr ⟨d', hd', hd, j', hj', hj, y', hy', ⟨h₁, lt_add_one _⟩, hy⟩⟩

lemma phi_iff (W m w : V) (C : Set V) (s j d off e y : V) :
    Phi W m w C ⟪s, j, d, off, e, y⟫ ↔
    ( (d = 0 ∧ ∃ j', j = j' + 1 ∧ e = off + 1 ∧ y = ncZeroSteps W (descCountT W m w.[s]) off j') ∨
      (∃ d' j' y', d = d' + 1 ∧ j = j' + 1 ∧ y' ≤ y ∧
        ⟪s + 1, j', d', off + 1 + descCountT W m w.[s], e, y'⟫ ∈ C ∧
        y = ncSuccSteps W (descCountT W m w.[s]) off j' d' e y') ) := by
  rw [show Phi W m w C ⟪s, j, d, off, e, y⟫ ↔ Cases W m w C s j d off e y from ⟨cases_of_phi, phi_of_cases⟩]
  unfold Cases
  constructor
  · rintro (⟨rfl, j', _, rfl, rfl, rfl⟩ | ⟨d', _, rfl, j', _, rfl, y', hy', h₁, rfl⟩)
    · exact Or.inl ⟨rfl, j', rfl, rfl, rfl⟩
    · exact Or.inr ⟨d', j', y', rfl, rfl, hy', h₁, rfl⟩
  · rintro (⟨rfl, j', rfl, rfl, rfl⟩ | ⟨d', j', y', rfl, rfl, hy', h₁, rfl⟩)
    · exact Or.inl ⟨rfl, j', lt_add_one _, rfl, rfl, rfl⟩
    · exact Or.inr ⟨d', lt_add_one _, rfl, j', lt_add_one _, rfl, y', hy', h₁, rfl⟩

end NthC

def NthCPacked (W m w pr : V) : Prop := NthC.construction.Fixpoint ![W, m, w] pr
/-- `NthCGraph W m w s j d off e y`: from the sub-vector at `&off` (the last `j` entries of `w`, head `w.[s]`),
the chain `y` derives `nthFact &e &off (cT d)`, `e` the walk offset of the entry `w.[s + d]`. -/
def NthCGraph (W m w s j d off e y : V) : Prop := NthCPacked W m w ⟪s, j, d, off, e, y⟫

noncomputable def nthCPackedDef : 𝚺₁.Semisentence 4 := .mkSigma “W m w pr. !NthC.blueprint.fixpointDef pr W m w”

instance nthCPacked_defined : 𝚺₁-Relation₄ (NthCPacked : V → V → V → V → Prop) via nthCPackedDef := .mk
  fun v ↦ by
    simp only [nthCPackedDef, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.constant_eq_singleton]
    rw [NthC.construction.eval_fixpointDef]
    rfl
instance nthCPacked_definable : 𝚺₁-Relation₄ (NthCPacked : V → V → V → V → Prop) := nthCPacked_defined.to_definable

noncomputable def nthCGraphDef : 𝚺₁.Semisentence 9 := .mkSigma
  “W m w s j d off e y. ∃ q₄, !pairDef q₄ e y ∧ ∃ q₃, !pairDef q₃ off q₄ ∧ ∃ q₂, !pairDef q₂ d q₃ ∧
    ∃ q₁, !pairDef q₁ j q₂ ∧ ∃ pr, !pairDef pr s q₁ ∧ !nthCPackedDef W m w pr”
instance nthCGraph_defined :
    𝚺₁.Defined (fun v : Fin 9 → V ↦ NthCGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) nthCGraphDef := .mk
  fun v ↦ by simp [nthCGraphDef, nthCPacked_defined.iff, NthCGraph]
instance nthCGraph_definable :
    𝚺₁.Definable (fun v : Fin 9 → V ↦ NthCGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  nthCGraph_defined.to_definable

lemma NthCGraph.case_iff {W m w s j d off e y : V} :
    NthCGraph W m w s j d off e y ↔
    ( (d = 0 ∧ ∃ j', j = j' + 1 ∧ e = off + 1 ∧ y = ncZeroSteps W (descCountT W m w.[s]) off j') ∨
      (∃ d' j' y', d = d' + 1 ∧ j = j' + 1 ∧ y' ≤ y ∧
        NthCGraph W m w (s + 1) j' d' (off + 1 + descCountT W m w.[s]) e y' ∧
        y = ncSuccSteps W (descCountT W m w.[s]) off j' d' e y') ) := by
  unfold NthCGraph NthCPacked
  rw [NthC.construction.case]
  exact NthC.phi_iff W m w _ s j d off e y

lemma NthCGraph.zero_iff {W m w s j off e y : V} :
    NthCGraph W m w s j 0 off e y ↔ ∃ j', j = j' + 1 ∧ e = off + 1 ∧ y = ncZeroSteps W (descCountT W m w.[s]) off j' := by
  rw [NthCGraph.case_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨d', _, _, h, _⟩)
    · exact h
    · exact absurd h (by simp)
  · intro h; exact Or.inl ⟨rfl, h⟩

lemma NthCGraph.succ_iff {W m w s j d' off e y : V} :
    NthCGraph W m w s j (d' + 1) off e y ↔ ∃ j' y', j = j' + 1 ∧ y' ≤ y ∧
      NthCGraph W m w (s + 1) j' d' (off + 1 + descCountT W m w.[s]) e y' ∧
      y = ncSuccSteps W (descCountT W m w.[s]) off j' d' e y' := by
  rw [NthCGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨d'', j', y', hd, rfl, hy', h₁, rfl⟩)
    · exact absurd h (by simp)
    · obtain rfl : d' = d'' := by simpa using hd
      exact ⟨j', y', rfl, hy', h₁, rfl⟩
  · rintro ⟨j', y', rfl, hy', h₁, rfl⟩
    exact Or.inr ⟨d', j', y', rfl, rfl, hy', h₁, rfl⟩

/-- `IsUTermVec j (takeLast v j)` for every `j ≤ k` of a semiterm vector. -/
lemma isUTermVec_takeLast {k n v : V} (hv : IsSemitermVec LAct k n v) : ∀ j ≤ k, IsUTermVec LAct j (takeLast v j) := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjk : j < len v := by rw [hv.lh]; exact lt_of_lt_of_le (lt_add_one j) hj
    rw [takeLast_succ_of_lt hjk, hv.lh]
    exact (ih (le_trans le_self_add hj)).adjoin (hv.nth (tsub_lt_self
      (lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj)
      (lt_of_lt_of_le _root_.zero_lt_one le_add_self))).isUTerm

section nthChainFun

/-- **Existence** (Σ₁ motive, offsets bounded by `B`; the potential `off + π₁ (descVecAux … j)` is CONSTANT along
the descent — the offset of the deeper sub-vector plus its count is the offset of this one plus this count). -/
lemma nthCGraph_exists_bounded (W m : V) {n w : V} (hv : IsSemitermVec LAct n m w) {B : V} (hn : n ≤ B) :
    ∀ d, ∀ s ≤ B, ∀ j ≤ B, ∀ off ≤ B, s + j = n → d < j →
      off + π₁ (descVecAux W m (descTVec W m n w) j) ≤ B → ∃ e y, NthCGraph W m w s j d off e y := by
  intro d
  induction d using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero =>
    intro s _ j _ off _ _ hd _
    rcases zero_or_succ j with rfl | ⟨j', rfl⟩
    · exact absurd hd (by simp)
    exact ⟨off + 1, _, NthCGraph.zero_iff.mpr ⟨j', rfl, rfl, rfl⟩⟩
  | succ d ih =>
    intro s hs j hj off hoff hsj hd hpot
    rcases zero_or_succ j with rfl | ⟨j', rfl⟩
    · exact absurd hd (by simp)
    have hjk : j' < len w := by rw [hv.lh, ← hsj]; exact lt_of_lt_of_le (lt_add_one j') le_add_self
    have hlt : n - (j' + 1) < n := tsub_lt_self (lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) (hsj ▸ le_add_self))
      (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have hnth : nthFromEnd (descTVec W m n w) j' = descT W m w.[n - (j' + 1)] := by
      rw [nthFromEnd_eq (a := n - (j' + 1)) (by rw [len_descTVec W m hv.isUTerm, tsub_add_cancel_of_le (hsj ▸ le_add_self)]),
        nth_descTVec W m hv.isUTerm hlt]
    have hs' : n - (j' + 1) = s := by rw [← hsj, add_tsub_cancel_right]
    have hpot' : off + 1 + descCountT W m w.[s] + π₁ (descVecAux W m (descTVec W m n w) j') ≤ B := by
      have : π₁ (descVecAux W m (descTVec W m n w) (j' + 1)) =
          π₁ (descVecAux W m (descTVec W m n w) j') + descCountT W m w.[s] + 1 := by
        rw [descVecAux_succ, hnth, adjNode, pi₁_pair, hs']; rfl
      rw [this] at hpot
      calc off + 1 + descCountT W m w.[s] + π₁ (descVecAux W m (descTVec W m n w) j')
          = off + (π₁ (descVecAux W m (descTVec W m n w) j') + descCountT W m w.[s] + 1) := by ring
        _ ≤ B := hpot
    obtain ⟨e, y', hy'⟩ := ih (s + 1) (le_trans (by rw [← hsj]; exact add_le_add (le_refl s) (by simp)) hn)
      j' (le_trans le_self_add hj) (off + 1 + descCountT W m w.[s]) (le_trans le_self_add hpot')
      (by rw [← hsj]; ring) (by simpa using hd) hpot'
    exact ⟨e, _, NthCGraph.succ_iff.mpr ⟨j', y', rfl, le_appendV_left _ _, hy', rfl⟩⟩

lemma nthCGraph_exists (W m : V) {n w : V} (hv : IsSemitermVec LAct n m w) {s j d off : V} (hsj : s + j = n) (hd : d < j) :
    ∃ e y, NthCGraph W m w s j d off e y :=
  nthCGraph_exists_bounded W m hv (B := s + j + off + π₁ (descVecAux W m (descTVec W m n w) j))
    (by rw [← hsj]; exact le_trans le_self_add le_self_add) d s
    (le_trans (le_trans le_self_add le_self_add) le_self_add) j (le_trans (le_trans le_add_self le_self_add) le_self_add)
    off (le_trans le_add_self le_self_add) hsj hd (by rw [add_assoc (s + j)]; exact le_add_self)

/-- **Uniqueness** (Π₁ motive). -/
lemma nthCGraph_unique (W m w : V) : ∀ d, ∀ s j off e₁ y₁ e₂ y₂,
    NthCGraph W m w s j d off e₁ y₁ → NthCGraph W m w s j d off e₂ y₂ → e₁ = e₂ ∧ y₁ = y₂ := by
  intro d
  induction d using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro s j off e₁ y₁ e₂ y₂ h₁ h₂
    obtain ⟨j₁, rfl, rfl, rfl⟩ := NthCGraph.zero_iff.mp h₁
    obtain ⟨j₂, hj, rfl, rfl⟩ := NthCGraph.zero_iff.mp h₂
    obtain rfl : j₁ = j₂ := by simpa using hj
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro s j off e₁ y₁ e₂ y₂ h₁ h₂
    obtain ⟨j₁, y₁', rfl, _, hg₁, rfl⟩ := NthCGraph.succ_iff.mp h₁
    obtain ⟨j₂, y₂', hj, _, hg₂, rfl⟩ := NthCGraph.succ_iff.mp h₂
    obtain rfl : j₁ = j₂ := by simpa using hj
    obtain ⟨rfl, rfl⟩ := ih _ _ _ _ _ _ _ hg₁ hg₂
    exact ⟨rfl, rfl⟩

lemma nthCGraph_existsUnique_total (W m w s j d off : V) :
    ∃! p, ((IsSemitermVec LAct (len w) m w ∧ s + j = len w ∧ d < j) → NthCGraph W m w s j d off (π₁ p) (π₂ p)) ∧
      (¬(IsSemitermVec LAct (len w) m w ∧ s + j = len w ∧ d < j) → p = 0) := by
  by_cases h : IsSemitermVec LAct (len w) m w ∧ s + j = len w ∧ d < j
  · obtain ⟨e, y, hy⟩ := nthCGraph_exists W m h.1 h.2.1 h.2.2 (off := off)
    refine ExistsUnique.intro ⟪e, y⟫ (by simpa [h] using hy) ?_
    intro p hp
    simp only [h, and_self, true_implies, not_true_eq_false, false_implies, and_true] at hp
    obtain ⟨rfl, rfl⟩ := nthCGraph_unique W m w d s j off _ _ _ _ hp hy
    exact (pair_unpair p).symm
  · simp [h]

/-- **The `nth` chain**: `nthChainP W m w s j d off = ⟪e, y⟫` — the entry offset `e` of `w.[s + d]` and the step list
`y` deriving `nthFact &e &off (cT d)` from the sub-vector at `&off` (the last `j` entries, head `w.[s]`);
`0` off the domain (`s + j = len w`, `d < j`, `w` a semiterm vector of arity `m`). -/
noncomputable def nthChainP (W m w s j d off : V) : V := Classical.choose! (nthCGraph_existsUnique_total W m w s j d off)
/-- The entry offset (`π₁`) and the chain (`π₂`). -/
noncomputable def nthChainE (W m w s j d off : V) : V := π₁ (nthChainP W m w s j d off)
noncomputable def nthChainL (W m w s j d off : V) : V := π₂ (nthChainP W m w s j d off)

theorem nthChain_graph {W m n w s j d off : V} (hv : IsSemitermVec LAct n m w) (hsj : s + j = n) (hd : d < j) :
    NthCGraph W m w s j d off (nthChainE W m w s j d off) (nthChainL W m w s j d off) := by
  have hlen : len w = n := hv.lh
  subst hlen
  exact (Classical.choose!_spec (nthCGraph_existsUnique_total W m w s j d off)).1 ⟨hv, hsj, hd⟩
lemma nthChain_eq_of_graph {W m n w s j d off e y : V} (hv : IsSemitermVec LAct n m w) (hsj : s + j = n) (hd : d < j)
    (hy : NthCGraph W m w s j d off e y) : nthChainE W m w s j d off = e ∧ nthChainL W m w s j d off = y :=
  nthCGraph_unique W m w d s j off _ _ _ _ (nthChain_graph hv hsj hd) hy

noncomputable def nthChainPDef : 𝚺₁.Semisentence 8 := .mkSigma
  “p W m w s j d off. ∃ k, !lenDef k w ∧
    ((!(isSemitermVec LAct).pi k m w ∧ s + j = k ∧ d < j) → ∃ e, !pi₁Def e p ∧ ∃ y, !pi₂Def y p ∧ !nthCGraphDef W m w s j d off e y) ∧
    ((!(isSemitermVec LAct).sigma k m w → s + j = k → j ≤ d) → p = 0)”

instance nthChainP_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ nthChainP (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) nthChainPDef := .mk
  fun v ↦ by
    simp [nthChainPDef, HierarchySymbol.Semiformula.val_sigma, nthCGraph_defined.iff,
      (IsSemitermVec.defined (L := LAct)).proper.iff', (IsSemitermVec.defined (L := LAct)).df, nthChainP,
      Classical.choose!_eq_iff_right]
instance nthChainP_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ nthChainP (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  nthChainP_defined.to_definable

noncomputable def nthChainEDef : 𝚺₁.Semisentence 8 := .mkSigma
  “e W m w s j d off. ∃ p, !nthChainPDef p W m w s j d off ∧ !pi₁Def e p”
noncomputable def nthChainLDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W m w s j d off. ∃ p, !nthChainPDef p W m w s j d off ∧ !pi₂Def y p”
instance nthChainE_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ nthChainE (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) nthChainEDef := .mk
  fun v ↦ by simp [nthChainEDef, nthChainP_defined.iff, nthChainE]
instance nthChainE_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ nthChainE (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  nthChainE_defined.to_definable
instance nthChainL_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ nthChainL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) nthChainLDef := .mk
  fun v ↦ by simp [nthChainLDef, nthChainP_defined.iff, nthChainL]
instance nthChainL_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ nthChainL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  nthChainL_defined.to_definable

end nthChainFun

/-! #### The equations, the structure and the applicability of the chain -/

section nthChainOK

lemma nthChain_zero {W m n w s j' off : V} (hv : IsSemitermVec LAct n m w) (hsj : s + (j' + 1) = n) :
    nthChainE W m w s (j' + 1) 0 off = off + 1 ∧
    nthChainL W m w s (j' + 1) 0 off = ncZeroSteps W (descCountT W m w.[s]) off j' :=
  nthChain_eq_of_graph hv hsj (by simp) (NthCGraph.zero_iff.mpr ⟨j', rfl, rfl, rfl⟩)

lemma nthChain_succ {W m n w s j' d' off : V} (hv : IsSemitermVec LAct n m w) (hsj : s + (j' + 1) = n) (hd : d' < j') :
    nthChainE W m w s (j' + 1) (d' + 1) off = nthChainE W m w (s + 1) j' d' (off + 1 + descCountT W m w.[s]) ∧
    nthChainL W m w s (j' + 1) (d' + 1) off =
      ncSuccSteps W (descCountT W m w.[s]) off j' d' (nthChainE W m w (s + 1) j' d' (off + 1 + descCountT W m w.[s]))
        (nthChainL W m w (s + 1) j' d' (off + 1 + descCountT W m w.[s])) :=
  nthChain_eq_of_graph hv hsj (by simpa using hd) (NthCGraph.succ_iff.mpr ⟨j', _, rfl, le_appendV_left _ _,
    nthChain_graph hv (by rw [← hsj]; ring) hd, rfl⟩)

/-- The chain is Horn-only, shift-free, and has `d + 1` steps. -/
lemma nthCGraph_struct {W : V} (hWp : W = certPieces) (m w : V) : ∀ d, ∀ s j off e y : V,
    NthCGraph W m w s j d off e y → NoDrop y ∧ shiftsV y = 0 ∧ HornOnly y ∧ len y = d + 1 := by
  intro d
  induction d using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro s j off e y hy
    obtain ⟨j', rfl, rfl, rfl⟩ := NthCGraph.zero_iff.mp hy
    have ht : sTag (mkStep W (179 : V) ?[vRef (off + 1 + descCountT W m w.[s]) j', ^&(off + 1), ^&off]) = 0 :=
      ctag_nthAdjoinZero hWp _
    exact ⟨noDrop_single (Or.inl ht), shiftsV_single_tag0 ht, hornOnly_single (Or.inl ht), by rw [len_ncZeroSteps, zero_add]⟩
  | succ d ih =>
    intro s j off e y hy
    obtain ⟨j', y', rfl, _, hy', rfl⟩ := NthCGraph.succ_iff.mp hy
    obtain ⟨hnd, hsh, hh, hl⟩ := ih _ _ _ _ _ hy'
    have ht : sTag (mkStep W (180 : V) ?[cTV d, vRef (off + 1 + descCountT W m w.[s]) j', ^&(off + 1), ^&off, ^&e]) = 0 :=
      ctag_nthAdjoinSucc hWp _
    refine ⟨noDrop_appendV hnd (noDrop_single (Or.inl ht)), ?_, hornOnly_appendV hh (hornOnly_single (Or.inl ht)), ?_⟩
    · rw [ncSuccSteps, shiftsV_appendV, hsh, shiftsV_single_tag0 ht, add_zero]
    · rw [len_ncSuccSteps, hl]

/-- The result of a chain at `(s, j, d, off)`: the fact `nthFact &e &off (cT d)`, the dossier of the entry
`w.[s + d]` at `e`, and the bound `e + 2|w.[s + d]| + 1 ≤ off + 2Σ|entries| + 2` (so every later witness at
`e` fits the same cap). -/
def NCRes (tbl Wd E Γ m w j s d off e y : V) : Prop :=
  PassPost tbl E Γ y (nthFact (^&e) (^&off) (cTV d)) ∧ DossT Wd Γ m w.[s + d] e ∧
  e + 2 * termLen LAct w.[s + d] + 1 ≤ off + 2 * listSum (termLenVec LAct j (takeLast w j)) + 2
instance ncRes_definable :
    𝚫₁.Definable (fun v : Fin 12 → V ↦ NCRes (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) := by
  unfold NCRes; definability

/-- **The chain is applicable** and leaves `nthFact &e ⟨sub-vector⟩ (cT d)` (Π₁ motive on `d`). -/
lemma nthCGraph_ok {tbl N : V} (htbl : TableOK tbl N) (hC : CertTable tbl) {Wd W : V} (hWd : Wd = walkPieces)
    (hWp : W = certPieces) {m n w : V} (hv : IsSemitermVec LAct n m w) :
    ∀ d, ∀ s j off e y E Γ : V, NthCGraph W m w s j d off e y → s + j = n → d < j →
      2 * m + 2 * n + 8 ≤ E → off + 2 * listSum (termLenVec LAct j (takeLast w j)) + 2 ≤ E → IsFormulaSet LAct Γ →
      DossV Wd Γ m n w j off → NCRes tbl Wd E Γ m w j s d off e y := by
  have hW : WalkTable tbl := hC.walkTable
  intro d
  induction d using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro s j off e y E Γ hy hsj hd hE hEo hΓ hD
    obtain ⟨j', rfl, rfl, rfl⟩ := NthCGraph.zero_iff.mp hy
    have hs_lt : s < n := by rw [← hsj]; exact lt_of_lt_of_le (lt_add_one s) (add_le_add (le_refl s) le_add_self)
    have hjn : j' + 1 ≤ n := by rw [← hsj]; exact le_add_self
    have hjk : j' < len w := by rw [hv.lh]; exact lt_of_lt_of_le (lt_add_one j') hjn
    have hs' : n - (j' + 1) = s := by rw [← hsj, add_tsub_cancel_right]
    obtain ⟨hadj, _, hDt, _⟩ := dossV_succ htbl hW hWd hv hjn hD
    rw [hs'] at hadj hDt
    have hc : descCountT W m w.[s] = descCountT Wd m w.[s] := by
      rw [hWp, hWd]; exact descCountT_certPieces m _ (hv.nth hs_lt)
    have hct : descCountT Wd m w.[s] + 1 ≤ 2 * termLen LAct w.[s] := descCountT_walk_le htbl hW hWd (hv.nth hs_lt)
    have hSum : listSum (termLenVec LAct (j' + 1) (takeLast w (j' + 1))) =
        termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j')) := by
      rw [takeLast_succ_of_lt hjk, hv.lh, hs', termLenVec_cons (hv.nth hs_lt).isUTerm (isUTermVec_takeLast hv j' (le_trans le_self_add hjn)),
        listSum_adjoin]
    unfold NCRes
    rw [hSum] at hEo ⊢
    rw [hc]
    have hE1 : off + 2 * termLen LAct w.[s] + 1 ≤ E :=
      calc off + 2 * termLen LAct w.[s] + 1 ≤ off + 2 * termLen LAct w.[s] + 1 + (2 * listSum (termLenVec LAct j' (takeLast w j')) + 1) :=
            le_self_add
        _ = off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 := by ring
        _ ≤ E := hEo
    have hEoff1 : off + 1 + 1 ≤ E :=
      calc off + 1 + 1 = off + 0 + 2 := by ring
        _ ≤ off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 :=
            add_le_add (add_le_add (le_refl off) zero_le) (le_refl 2)
        _ ≤ E := hEo
    have hEoff : off + 1 ≤ E := le_trans le_self_add hEoff1
    obtain ⟨ok₀, tag₀, ctx₀⟩ := cok_nthAdjoinZero htbl hC hWp hΓ (isSemiterm_vRef _ _) (E_vRef_ct hct hE1)
      (by simp) (termLen_fvar_le hEoff1) (by simp) (termLen_fvar_le hEoff) hadj
    refine ⟨⟨listOK_single ok₀, hornOnly_single (Or.inl tag₀), ?_⟩, by rw [add_zero]; exact hDt, ?_⟩
    · rw [ncZeroSteps, finalCtx_single, ctx₀, cTV_zero]; exact mem_insert_self'
    · rw [add_zero]
      calc off + 1 + 2 * termLen LAct w.[s] + 1 = off + 2 * termLen LAct w.[s] + 0 + 2 := by ring
        _ ≤ off + 2 * termLen LAct w.[s] + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 :=
            add_le_add (add_le_add (le_refl _) zero_le) (le_refl 2)
        _ = off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 := by ring
  | succ d ih =>
    intro s j off e y E Γ hy hsj hd hE hEo hΓ hD
    obtain ⟨j', y', rfl, _, hy', rfl⟩ := NthCGraph.succ_iff.mp hy
    have hs_lt : s < n := by rw [← hsj]; exact lt_of_lt_of_le (lt_add_one s) (add_le_add (le_refl s) le_add_self)
    have hjn : j' + 1 ≤ n := by rw [← hsj]; exact le_add_self
    have hjk : j' < len w := by rw [hv.lh]; exact lt_of_lt_of_le (lt_add_one j') hjn
    have hs' : n - (j' + 1) = s := by rw [← hsj, add_tsub_cancel_right]
    have hdj : d < j' := by simpa using hd
    have hj0 : j' ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hdj)
    obtain ⟨hadj, _, _, hDv⟩ := dossV_succ htbl hW hWd hv hjn hD
    rw [hs'] at hadj hDv
    have hc : descCountT W m w.[s] = descCountT Wd m w.[s] := by
      rw [hWp, hWd]; exact descCountT_certPieces m _ (hv.nth hs_lt)
    have hct : descCountT Wd m w.[s] + 1 ≤ 2 * termLen LAct w.[s] := descCountT_walk_le htbl hW hWd (hv.nth hs_lt)
    have hSum : listSum (termLenVec LAct (j' + 1) (takeLast w (j' + 1))) =
        termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j')) := by
      rw [takeLast_succ_of_lt hjk, hv.lh, hs', termLenVec_cons (hv.nth hs_lt).isUTerm (isUTermVec_takeLast hv j' (le_trans le_self_add hjn)),
        listSum_adjoin]
    unfold NCRes
    rw [hSum] at hEo ⊢
    rw [hc] at hy' ⊢
    -- the deeper chain
    have hEo' : off + 1 + descCountT Wd m w.[s] + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 ≤ E :=
      calc off + 1 + descCountT Wd m w.[s] + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2
          = off + (descCountT Wd m w.[s] + 1) + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 := by ring
        _ ≤ off + 2 * termLen LAct w.[s] + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 :=
            add_le_add (add_le_add (add_le_add (le_refl off) hct) (le_refl _)) (le_refl 2)
        _ = off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 := by ring
        _ ≤ E := hEo
    obtain ⟨⟨hokY, hhY, hfY⟩, hDe, hbe⟩ :=
      ih (s + 1) j' (off + 1 + descCountT Wd m w.[s]) e y' E Γ hy' (by rw [← hsj]; ring) hdj hE hEo' hΓ hDv
    obtain ⟨hndY, hsY, _, _⟩ := nthCGraph_struct hWp m w d (s + 1) j' (off + 1 + descCountT Wd m w.[s]) e y' hy'
    have hsub : Γ ⊆ finalCtx Γ y' := subset_finalCtx_of_shiftsV_zero hndY hsY
    have hΓ₁ : IsFormulaSet LAct (finalCtx Γ y') := finalCtx_isFormulaSet 8 htbl hΓ hokY
    -- the witness bounds
    have hE1 : off + 2 * termLen LAct w.[s] + 1 ≤ E :=
      calc off + 2 * termLen LAct w.[s] + 1 ≤ off + 2 * termLen LAct w.[s] + 1 + (2 * listSum (termLenVec LAct j' (takeLast w j')) + 1) :=
            le_self_add
        _ = off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 := by ring
        _ ≤ E := hEo
    have hEoff1 : off + 1 + 1 ≤ E :=
      calc off + 1 + 1 = off + 0 + 2 := by ring
        _ ≤ off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 :=
            add_le_add (add_le_add (le_refl off) zero_le) (le_refl 2)
        _ ≤ E := hEo
    have hEoff : off + 1 ≤ E := le_trans le_self_add hEoff1
    have hEe : e + 1 ≤ E :=
      calc e + 1 ≤ e + 1 + 2 * termLen LAct w.[s + 1 + d] := le_self_add
        _ = e + 2 * termLen LAct w.[s + 1 + d] + 1 := by ring
        _ ≤ E := le_trans hbe hEo'
    have hEd : 2 * d + 1 ≤ E :=
      calc 2 * d + 1 ≤ 2 * d + 2 := add_le_add (le_refl _) (by norm_num)
        _ = 2 * (d + 1) := by ring
        _ ≤ 2 * n := mul_le_mul_of_nonneg_left (le_trans (add_le_add (le_of_lt hdj) (le_refl 1)) hjn) zero_le
        _ ≤ 2 * m + 2 * n + 8 := le_trans le_add_self le_self_add
        _ ≤ E := hE
    -- the climbing step
    have hnth' : neg LAct (nthFact (^&e) (vRef (off + 1 + descCountT Wd m w.[s]) j') (cTV d)) ∈ finalCtx Γ y' := by
      rw [vRef_of_ne hj0]; exact hfY
    obtain ⟨ok₁, tag₁, ctx₁⟩ := cok_nthAdjoinSucc htbl hC hWp hΓ₁ (cTV_semiterm_LAct 0 _) (termLen_cTV_le hEd)
      (isSemiterm_vRef _ _) (E_vRef_ct hct hE1) (by simp) (termLen_fvar_le hEoff1) (by simp) (termLen_fvar_le hEoff)
      (by simp) (termLen_fvar_le hEe) (hsub hadj) hnth'
    refine ⟨⟨listOK_appendV hokY (listOK_single ok₁), hornOnly_appendV hhY (hornOnly_single (Or.inl tag₁)), ?_⟩,
      by rw [show s + (d + 1) = s + 1 + d by ring]; exact hDe, ?_⟩
    · rw [ncSuccSteps, finalCtx_appendV, finalCtx_single, ctx₁, cTV_succ]; exact mem_insert_self'
    · rw [show s + (d + 1) = s + 1 + d by ring]
      calc e + 2 * termLen LAct w.[s + 1 + d] + 1
          ≤ off + 1 + descCountT Wd m w.[s] + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 := hbe
        _ = off + (descCountT Wd m w.[s] + 1) + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 := by ring
        _ ≤ off + 2 * termLen LAct w.[s] + 2 * listSum (termLenVec LAct j' (takeLast w j')) + 2 :=
            add_le_add (add_le_add (add_le_add (le_refl off) hct) (le_refl _)) (le_refl 2)
        _ = off + 2 * (termLen LAct w.[s] + listSum (termLenVec LAct j' (takeLast w j'))) + 2 := by ring

end nthChainOK

end ArithS
