import ArithS.Necessitation.Prologue
import ArithS.Necessitation.Pin
import ArithS.Necessitation.NodeSize
import ArithS.Necessitation.Verify3

/-!
# ArithS.Necessitation.Bounds — CUBIC `all`/`exs` bounds: the verification list can run at `m = 4`

`Prologue.lean` §18 bounds the `all`/`exs` prologues by `450·(D+1)⁵` / `310·(D+1)⁵` (`len_proAll_le`, `len_proExs_le`,
and the shift bounds `shiftsV_pro*_le` through `shiftsV ≤ len`): the quintic is `Cert.len_certSubst_single_le`'s
`sfK L Q · |r|` with `L, Q` quadratic in the size. `Prologue` cannot use `Pin`'s LINEAR `sfL L Q = L + 24Q + 22`
(`Pin` imports `Prologue`), so its lemmas are PARAMETRIC in the substitution pass's length (`len_proAll_le_of ≤ 200D +
58 + Lc`, `len_proExs_le_of ≤ 93D + 19 + Lc`). This file sits above both and instantiates them:

* §1 `len_certSubst_single_le_cubic : len (certSubst W Wd 1 m w iw r i j) ≤ 144·p3 (D+1)` for a `SubstInv B` vector with
  `|r|, B ≤ D` (`Pin.len_certSubst_le_lin` at the `Cert` §6.7 caps `Q = (1+|r|)(1+|r|+B)`, `L = 12(|r|+2)(|r|+2+B)+2`).
* §2 the CUBIC lengths: `len_allCert_le_cubic ≤ 196·p3 (D+1)`, `len_proAll_le_cubic ≤ 402·p3 (D+1)`,
  `len_exsCert_le_cubic ≤ 189·p3 (D+1)`, `len_proExs_le_cubic ≤ 256·p3 (D+1)` (+ `'` forms in `(D+1)^3`) — the SAME
  hypotheses as `Prologue`'s quintic lemmas, so they are drop-in replacements. DEGREE 3 in `D` for both tags.
* §3 the shifts: (a) `shiftsV_proAll_le_cubic`/`shiftsV_proExs_le_cubic` (through `shiftsV ≤ len`, no E-room needed —
  the drop-in for `Verify3`'s `hSA`); (b) the SHARP forms from the `_ok`s' exact `shiftsV` expressions:
  `shiftsV_proAll_le_sharp ≤ 2·(1+D)(2+D)·D + 23D + 8` and `shiftsV_proExs_le_sharp ≤ 2·(1+D)(1+2D)·D + 12D + 3`
  (`allCertSig`/`exsSig` + three/one `proSig ≤ 6D+1`). The cubic term is `certSubst_ok`'s `2Q·|r|` with `Q` the
  `subFPre_single` cap `(1+|r|)(1+|r|+B)` — and that `Q` is QUADRATIC for an INHERENT reason: it bounds the term-length
  sum of the `qVec` iterate at depth `e ≤ |r|`, whose `e` bound-variable entries `#0, …, #(e-1)` have UNARY lengths
  `1, …, e` (`Σ_{i<e}(i+1)`, `Cert.listSum_termLenVec_le_of_substInv`), and every quantifier of `r` walks one such
  iterate (`≈ Q` eigenvariables each). So the shifts are cubic in `D` and cannot be brought lower without changing the
  certificate (one `qVecCert` step per depth) or the length measure (binary indices). `VarInv` does not help here:
  it bounds the SUBSTITUTED formula (`|free p| ≤ |shift p|`), not the iterate's vectors.
* §4 the arithmetic for the recursion at `m = 4`: `p4`, `p4_split : p4 y + m·p3 (y+m) ≤ p4 (y+m)`, `rec1₄`/`rec2₄`
  (`X ≤ Cs·p3 d → X + Cs·p4 y ≤ Cs·p4 d` for `d = y + m`, `m ≥ 1`), the caps `capE4`/`child_bound4`/`quad_cap3`/
  `lin_le_p3`, and the four node caps `allEQ_p3`/`alliE_p3`/`exsEQ_p3`/`exsiE_p3` + `allE_p4`/`exsE_p4` + `allNode_p4`
  + `axmLeaf_p4` in EXACTLY the shapes `Verify3.verifyGraph''_ok`'s `all`/`exs`/`axm` arms consume at `m = 6` —
  so the re-glue at `m = 4` (list `≤ Cs·p4 (dlen ρ)`, E-room `Ck·p4 (dlen ρ + 1)`, top degree `deg 4 = 16`) is a
  name-for-name copy of those arms. Also the LOCAL step `rec1_local`/`rec2_local` (`X ≤ Cs·p3 m → X + Cs·p3 y ≤
  Cs·p3 (y+m)`, `p3_add_le`): with per-node accounting (`D` bounded by the node's OWN size `m = setLen s + 1`, not by
  `dlen ρ`) the same cubic bounds would close at `m = 3` — but the `_ok`s take ONE `D` that also bounds the child
  sequent and (for `exs`) `|substs1 t p|`, which is only globally bounded; not done here.
* §5 the cost corollaries `costSum_proAll_le''`/`costSum_proExs_le''` (`costShape_mono` at the cubic lengths).

WHY `m = 4` AND NOT LESS: `Verify2.rec1` needs the node's own shift contribution `X ≤ Cs·d^{m-1}` where `d = dlen` of
the node bounds every size (`D = 2d`); with `X` cubic in `D`, `m - 1 = 3`.
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

/-! ## 0. Powers as explicit products: `p3` (`Verify3`), `p4` (new), and their laws -/

section powers

/-- `x⁴` as an explicit product (definability-friendly, like `Verify2.p5`/`p6` and `Verify3.p3`). -/
def p4 (x : V) : V := x * x * x * x

lemma pow3_eq_p3 (x : V) : x ^ 3 = p3 x := by simp only [p3]; ring
lemma pow4_eq_p4 (x : V) : x ^ 4 = p4 x := by simp only [p4]; ring

lemma p4_eq (x : V) : p4 x = x * p3 x := by simp only [p3, p4]; ring

lemma p4_mono {a b : V} (h : a ≤ b) : p4 a ≤ p4 b := by
  simp only [p4]
  exact mul_le_mul (mul_le_mul (mul_le_mul h h zero_le zero_le) h zero_le zero_le) h zero_le zero_le

lemma le_p3_self {d : V} (hd : 1 ≤ d) : d ≤ p3 d := by
  simp only [p3]
  calc d = 1 * 1 * d := by ring
    _ ≤ d * d * d := mul_le_mul (mul_le_mul hd hd zero_le zero_le) (le_refl d) zero_le zero_le

lemma sq_le_p3 {d : V} (hd : 1 ≤ d) : d * d ≤ p3 d := by
  simp only [p3]
  calc d * d = d * d * 1 := by ring
    _ ≤ d * d * d := mul_le_mul_of_nonneg_left hd zero_le

lemma le_p4_self {d : V} (hd : 1 ≤ d) : d ≤ p4 d := by
  rw [p4_eq]
  calc d = d * 1 := by ring
    _ ≤ d * p3 d := mul_le_mul_of_nonneg_left (one_le_p3 hd) zero_le

lemma one_le_p4 {d : V} (hd : 1 ≤ d) : 1 ≤ p4 d := le_trans hd (le_p4_self hd)

lemma p3_le_p4 {d : V} (hd : 1 ≤ d) : p3 d ≤ p4 d := by
  rw [p4_eq]
  calc p3 d = 1 * p3 d := by ring
    _ ≤ d * p3 d := mul_le_mul_of_nonneg_right hd zero_le

lemma p3_two_mul (x : V) : p3 (2 * x) = 8 * p3 x := by simp only [p3]; ring

lemma p3_succ_le {d : V} (hd : 1 ≤ d) : p3 (d + 1) ≤ 8 * p3 d := by
  rw [← p3_two_mul]
  exact p3_mono (by calc d + 1 ≤ d + d := add_le_add (le_refl d) hd
    _ = 2 * d := by ring)

lemma p3_add_le (y₁ y₂ : V) : p3 y₁ + p3 y₂ ≤ p3 (y₁ + y₂) := by
  simp only [p3]
  exact le_of_add_eq' (c := 3 * (y₁ * y₁) * y₂ + 3 * y₁ * (y₂ * y₂)) (by ring)

lemma p4_add_le (y₁ y₂ : V) : p4 y₁ + p4 y₂ ≤ p4 (y₁ + y₂) := by
  simp only [p4]
  exact le_of_add_eq' (c := 4 * (y₁ * y₁ * y₁) * y₂ + 6 * (y₁ * y₁) * (y₂ * y₂) + 4 * y₁ * (y₂ * y₂ * y₂)) (by ring)

end powers

/-! ## 1. The substitution certificate is CUBIC -/

section certSubstCubic

/-- `sfL L Q ≤ 144·(D+1)²` at the singleton caps `Q = (1+r)(1+r+B)`, `L = 12(r+2)(r+2+B) + 2` with `r, B ≤ D`. -/
lemma sfL_single_le {r B D : V} (hrD : r ≤ D) (hB : B ≤ D) :
    sfL (12 * ((1 + r + 1) * (1 + r + 1 + B)) + 2) ((1 + r) * (1 + r + B)) ≤ 144 * ((D + 1) * (D + 1)) := by
  unfold sfL
  have hX := one_le_sq D
  have h1 : 1 + r ≤ D + 1 := by rw [add_comm]; exact add_le_add hrD (le_refl 1)
  have h2 : 1 + r + 1 ≤ 2 * (D + 1) := by
    calc 1 + r + 1 ≤ (D + 1) + (D + 1) := add_le_add h1 le_add_self
      _ = 2 * (D + 1) := by ring
  have h3 : 1 + r + 1 + B ≤ 3 * (D + 1) := by
    calc 1 + r + 1 + B ≤ 2 * (D + 1) + (D + 1) := add_le_add h2 (le_trans hB le_self_add)
      _ = 3 * (D + 1) := by ring
  have h4 : 1 + r + B ≤ 2 * (D + 1) := by
    calc 1 + r + B ≤ (D + 1) + (D + 1) := add_le_add h1 (le_trans hB le_self_add)
      _ = 2 * (D + 1) := by ring
  calc 12 * ((1 + r + 1) * (1 + r + 1 + B)) + 2 + 24 * ((1 + r) * (1 + r + B)) + 22
      ≤ 12 * (2 * (D + 1) * (3 * (D + 1))) + 2 * ((D + 1) * (D + 1)) + 24 * ((D + 1) * (2 * (D + 1))) +
          22 * ((D + 1) * (D + 1)) :=
        add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 zero_le zero_le) zero_le)
          (le_mul_of_one_le_right zero_le hX)) (mul_le_mul_of_nonneg_left (mul_le_mul h1 h4 zero_le zero_le) zero_le))
          (le_mul_of_one_le_right zero_le hX)
    _ = 144 * ((D + 1) * (D + 1)) := by ring

/-- **The singleton substitution certificate is CUBIC**: `len (certSubst W Wd 1 m w iw r i j) ≤ 144·p3 (D+1)` for a
`SubstInv B` vector `w` (`Cert` §6.7) with `|r|, B ≤ D` — `Pin.len_certSubst_le_lin` at the caps
`listSum_termLenVec_qVecIterV_cap`/`len_qWalkP_cap`. (`Prologue.len_certSubst_single_le` gives `192·(D+1)⁵`, from
`Cert`'s `sfK`, quadratic in `Q`.) -/
theorem len_certSubst_single_le_cubic {Wd W m w iw r i j B D : V} (hw : IsSemitermVec LAct 1 m w) (hinv : SubstInv LAct B w)
    (hr : IsSemiformula LAct 1 r) (hrD : formulaLen LAct r ≤ D) (hB : B ≤ D) :
    len (certSubst W Wd 1 m w iw r i j) ≤ 144 * p3 (D + 1) := by
  have h := len_certSubst_le_lin (Wd := Wd) (W := W) (iw := iw) (i := i) (j := j) hw hr
    (listSum_termLenVec_qVecIterV_cap hw hinv) (len_qWalkP_cap (Wd := Wd) hw hinv)
  have hr1 : formulaLen LAct r ≤ D + 1 := le_trans hrD (le_self_add : D ≤ D + 1)
  refine le_trans h (le_trans (b := 144 * ((D + 1) * (D + 1)) * (D + 1))
    (mul_le_mul (sfL_single_le hrD hB) hr1 zero_le zero_le) ?_)
  exact le_of_eq (by simp only [p3]; ring)

/-- The same in `(D+1)^3`. -/
theorem len_certSubst_single_le_cubic' {Wd W m w iw r i j B D : V} (hw : IsSemitermVec LAct 1 m w) (hinv : SubstInv LAct B w)
    (hr : IsSemiformula LAct 1 r) (hrD : formulaLen LAct r ≤ D) (hB : B ≤ D) :
    len (certSubst W Wd 1 m w iw r i j) ≤ 144 * (D + 1) ^ 3 := by
  rw [pow3_eq_p3]; exact len_certSubst_single_le_cubic hw hinv hr hrD hB

end certSubstCubic

/-! ## 2. The cubic lengths of `allCert`/`proAll` and `exsCert`/`proExs` -/

section lengths

/-- **`allCert` is cubic**: `≤ 196·p3 (D+1)` for `|shift p|, |free p|, |p| ≤ D` (the hypotheses of `Prologue.len_allCert_le`). -/
theorem len_allCert_le_cubic {Wc : V} (hWc : Wc = certPieces) (Ww T s i : V) {p D : V} (hp : IsSemiformula LAct 1 p)
    (hspD : formulaLen LAct (shift LAct p) ≤ D) (hfpD : formulaLen LAct (free LAct p) ≤ D) (hpD : formulaLen LAct p ≤ D) :
    len (allCert Ww Wc T s p i) ≤ 196 * p3 (D + 1) := by
  have hD1 : (1 : V) ≤ D + 1 := le_add_self
  have hpow : D + 1 ≤ p3 (D + 1) := le_p3_self hD1
  have hcs : ∀ a b : V, len (certSubst Wc Ww 1 0 fvec 0 (shift LAct p) a b) ≤ 144 * p3 (D + 1) := fun a b ↦
    len_certSubst_single_le_cubic (isSemitermVec_fvec : IsSemitermVec LAct 1 0 (fvec : V))
      (substInv_fvec : SubstInv LAct 1 (fvec : V)) hp.shift hspD (le_trans (one_le_formulaLen_V hp.shift) hspD)
  have h := len_allCert_le_of Ww T s i hp hcs
  calc _ ≤ 12 * D + 12 * D + 12 * D + 144 * p3 (D + 1) + 16 :=
        le_trans h (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hspD zero_le)
          (mul_le_mul_of_nonneg_left hfpD zero_le)) (mul_le_mul_of_nonneg_left hpD zero_le)) le_rfl) le_rfl)
    _ = 36 * D + 16 + 144 * p3 (D + 1) := by ring
    _ ≤ 36 * p3 (D + 1) + 16 * p3 (D + 1) + 144 * p3 (D + 1) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_trans le_self_add hpow) zero_le)
          (le_mul_of_one_le_right zero_le (le_trans hD1 hpow))) le_rfl
    _ = 196 * p3 (D + 1) := by ring

/-- **`proAll` is cubic**: `≤ 402·p3 (D+1)` — the hypotheses of `Prologue.len_proAll_le` (which gives `450·(D+1)⁵`). -/
theorem len_proAll_le_cubic {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V} (hWl : Wl = layoutPieces)
    (hWc : Wc = certPieces) (Ww W T i : V) {s p D : V} (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∀ p) ∈ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D) :
    len (proAll Ww Wl Wc W T s p i) ≤ 402 * p3 (D + 1) := by
  have hD1 : (1 : V) ≤ D + 1 := le_add_self
  have hpow : D + 1 ≤ p3 (D + 1) := le_p3_self hD1
  have hpD : formulaLen LAct p ≤ D := by
    have := formulaLen_le_setLen_of_mem (L := LAct) hr
    rw [formulaLen_all hp.isUFormula] at this
    exact le_trans le_self_add (le_trans this hsD)
  have hcs : ∀ a b : V, len (certSubst Wc Ww 1 0 fvec 0 (shift LAct p) a b) ≤ 144 * p3 (D + 1) := fun a b ↦
    len_certSubst_single_le_cubic (isSemitermVec_fvec : IsSemitermVec LAct 1 0 (fvec : V))
      (substInv_fvec : SubstInv LAct 1 (fvec : V)) hp.shift hspD (le_trans (one_le_formulaLen_V hp.shift) hspD)
  have h := len_proAll_le_of htbl hP hWl hWc Ww W T i hs hp hsD hcD hspD hpD hcs
  calc _ ≤ 200 * D + 58 + 144 * p3 (D + 1) := h
    _ ≤ 200 * p3 (D + 1) + 58 * p3 (D + 1) + 144 * p3 (D + 1) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_trans le_self_add hpow) zero_le)
          (le_mul_of_one_le_right zero_le (le_trans hD1 hpow))) le_rfl
    _ = 402 * p3 (D + 1) := by ring

theorem len_proAll_le_cubic' {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V} (hWl : Wl = layoutPieces)
    (hWc : Wc = certPieces) (Ww W T i : V) {s p D : V} (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∀ p) ∈ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D) :
    len (proAll Ww Wl Wc W T s p i) ≤ 402 * (D + 1) ^ 3 := by
  rw [pow3_eq_p3]; exact len_proAll_le_cubic htbl hP hWl hWc Ww W T i hs hp hr hsD hcD hspD

/-- **`exsCert` is cubic**: `≤ 189·p3 (D+1)` for `|p|, |t|, |substs1 t p| ≤ D` (the hypotheses of `Prologue.len_exsCert_le`). -/
theorem len_exsCert_le_cubic {Wc : V} (Ww W T s i : V) {p t D : V} (hp : IsSemiformula LAct 1 p) (ht : IsSemiterm LAct 0 t)
    (hpD : formulaLen LAct p ≤ D) (htD : termLen LAct t ≤ D) (hptD : formulaLen LAct (substs1 LAct t p) ≤ D) :
    len (exsCert Ww Wc W T s p t i) ≤ 189 * p3 (D + 1) := by
  have hD1 : (1 : V) ≤ D + 1 := le_add_self
  have hpow : D + 1 ≤ p3 (D + 1) := le_p3_self hD1
  have hw : IsSemitermVec LAct 1 0 (t ∷ (0 : V)) := by simp [ht]
  have hcs : ∀ a b : V, len (certSubst Wc Ww 1 0 (t ∷ 0) a p b 0) ≤ 144 * p3 (D + 1) := fun a b ↦
    len_certSubst_single_le_cubic hw (substInv_single' ht) hp hpD htD
  have h := len_exsCert_le_of (Wc := Wc) Ww W T s i hp ht hcs
  calc _ ≤ 26 * D + 12 * D + 144 * p3 (D + 1) + 7 :=
        le_trans h (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left htD zero_le)
          (mul_le_mul_of_nonneg_left hptD zero_le)) le_rfl) le_rfl)
    _ = 38 * D + 7 + 144 * p3 (D + 1) := by ring
    _ ≤ 38 * p3 (D + 1) + 7 * p3 (D + 1) + 144 * p3 (D + 1) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_trans le_self_add hpow) zero_le)
          (le_mul_of_one_le_right zero_le (le_trans hD1 hpow))) le_rfl
    _ = 189 * p3 (D + 1) := by ring

/-- **`proExs` is cubic**: `≤ 256·p3 (D+1)` — the hypotheses of `Prologue.len_proExs_le` (which gives `310·(D+1)⁵`). -/
theorem len_proExs_le_cubic {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V} (hWl : Wl = layoutPieces)
    (hWc : Wc = certPieces) (Ww W T i : V) {s p t D : V} (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p)
    (hr : (^∃ p) ∈ s) (ht : IsSemiterm LAct 0 t) (hsD : setLen LAct s ≤ D)
    (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D) (htD : termLen LAct t ≤ D) :
    len (proExs Ww Wl Wc W T s p t i) ≤ 256 * p3 (D + 1) := by
  have hD1 : (1 : V) ≤ D + 1 := le_add_self
  have hpow : D + 1 ≤ p3 (D + 1) := le_p3_self hD1
  have hpD : formulaLen LAct p ≤ D := by
    have := formulaLen_le_setLen_of_mem (L := LAct) hr
    rw [formulaLen_exs hp.isUFormula] at this
    exact le_trans le_self_add (le_trans this hsD)
  have hw : IsSemitermVec LAct 1 0 (t ∷ (0 : V)) := by simp [ht]
  have hcs : ∀ a b : V, len (certSubst Wc Ww 1 0 (t ∷ 0) a p b 0) ≤ 144 * p3 (D + 1) := fun a b ↦
    len_certSubst_single_le_cubic hw (substInv_single' ht) hp hpD htD
  have h := len_proExs_le_of htbl hP hWl hWc Ww W T i hs hp ht hcD htD hcs
  calc _ ≤ 93 * D + 19 + 144 * p3 (D + 1) := h
    _ ≤ 93 * p3 (D + 1) + 19 * p3 (D + 1) + 144 * p3 (D + 1) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_trans le_self_add hpow) zero_le)
          (le_mul_of_one_le_right zero_le (le_trans hD1 hpow))) le_rfl
    _ = 256 * p3 (D + 1) := by ring

theorem len_proExs_le_cubic' {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V} (hWl : Wl = layoutPieces)
    (hWc : Wc = certPieces) (Ww W T i : V) {s p t D : V} (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p)
    (hr : (^∃ p) ∈ s) (ht : IsSemiterm LAct 0 t) (hsD : setLen LAct s ≤ D)
    (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D) (htD : termLen LAct t ≤ D) :
    len (proExs Ww Wl Wc W T s p t i) ≤ 256 * (D + 1) ^ 3 := by
  rw [pow3_eq_p3]; exact len_proExs_le_cubic htbl hP hWl hWc Ww W T i hs hp hr ht hsD hcD htD

end lengths

/-! ## 3. The shifts: cubic through `shiftsV ≤ len`, and the SHARP forms from the `_ok`s -/

section shifts

/-- The drop-in for `Verify3`'s `hSA`: `shiftsV (proAll …) ≤ 402·p3 (D+1)`, no E-room, no layout. -/
theorem shiftsV_proAll_le_cubic {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V} (hWl : Wl = layoutPieces)
    (hWc : Wc = certPieces) (Ww W T i : V) {s p D : V} (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∀ p) ∈ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D) :
    shiftsV (proAll Ww Wl Wc W T s p i) ≤ 402 * p3 (D + 1) :=
  le_trans (shiftsV_le_len _) (len_proAll_le_cubic htbl hP hWl hWc Ww W T i hs hp hr hsD hcD hspD)

theorem shiftsV_proExs_le_cubic {tbl N : V} (htbl : TableOK tbl N) (hP : ProTable tbl) {Wl Wc : V} (hWl : Wl = layoutPieces)
    (hWc : Wc = certPieces) (Ww W T i : V) {s p t D : V} (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p)
    (hr : (^∃ p) ∈ s) (ht : IsSemiterm LAct 0 t) (hsD : setLen LAct s ≤ D)
    (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D) (htD : termLen LAct t ≤ D) :
    shiftsV (proExs Ww Wl Wc W T s p t i) ≤ 256 * p3 (D + 1) :=
  le_trans (shiftsV_le_len _) (len_proExs_le_cubic htbl hP hWl hWc Ww W T i hs hp hr ht hsD hcD htD)

set_option maxHeartbeats 1000000 in
/-- **The SHARP shift bound of `proAll`** under `proAll_ok`'s hypotheses: `allCertSig ≤ 4D + 2 + 2·(1+D)(2+D)·D`
(`allCert_ok`; the cubic term is `certSubst_ok`'s `2Q·|shift p|` at `Q = (1+D)(1+D+1)`, `subFPre_single` with `B = 1`)
plus three layouts' `proSig ≤ 6D + 1` and the member count: `≤ 2·(1+D)(2+D)·D + 23D + 8`. -/
theorem shiftsV_proAll_le_sharp {tbl N N' B' Wl Wc W T s p i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∀ p) ∈ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : i + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    shiftsV (proAll walkPieces Wl Wc W T s p i) ≤ 2 * ((1 + D) * (1 + D + 1)) * D + 23 * D + 8 := by
  obtain ⟨_, _, hsh, _⟩ := proAll_ok htbl hP htblN hWl hWc hWp hs hp hr hsD hcD hspD hE hEQ hiE hΓ hLay
  obtain ⟨_, _, _, _, _, hcA, _⟩ := allCert_ok htbl hP hWc hs hp hr hsD hspD hE hEQ hiE hΓ hLay
  have hV : IsFormulaSet LAct (setShift LAct s) := hs.setShift
  have hfp : IsSemiformula LAct 0 (free LAct p) := hp.free
  have hk1 : 1 ≤ len (memberList s) := by
    obtain ⟨hlt, _⟩ := idxOf_spec hr
    have := lt_iff_succ_le.mp (lt_of_le_of_lt zero_le hlt); rwa [zero_add] at this
  have hkV1 : 1 ≤ len (memberList (setShift LAct s)) := one_le_len_memberList_setShift rfl hk1
  have hvD : setLen LAct (setShift LAct s) ≤ D := le_trans (setLen_le_insert _ _) hcD
  have hkD : len (memberList s) ≤ D := le_trans (len_memberList_le_setLen hs) hsD
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have hσV : proSig walkPieces Wl Wc W T (setShift LAct s) ≤ 6 * D + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hV hkV1 hvD hE8 hΓ
  have hσS : proSig walkPieces Wl Wc W T s ≤ 6 * D + 1 := proSig_le htbl hP hWc htblN hWl hWp hs hk1 hsD hE8 hΓ
  have hcI : IsFormulaSet LAct (insert (free LAct p) (setShift LAct s)) := IsFormulaSet.insert_iff.mpr ⟨hfp, hV⟩
  have hσI : proSig walkPieces Wl Wc W T (insert (free LAct p) (setShift LAct s)) ≤ 6 * D + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hcI (one_le_len_memberList_insert _ _) hcD hE8 hΓ
  rw [hsh]
  refine le_trans (add_le_add (add_le_add hcA (add_le_add hσV (add_le_add (add_le_add (le_refl 1)
    (add_le_add hkD (le_refl 1))) hσS))) (add_le_add (le_refl 1) hσI)) (le_of_eq (by ring))

set_option maxHeartbeats 1000000 in
/-- **The SHARP shift bound of `proExs`** under `proExs_ok`'s hypotheses: `exsSig ≤ 2·(1+D)(1+2D)·D + 6D + 1` (`exsCert_ok`;
the cubic term is `certSubst_ok`'s `2Q·|p|` at `Q = (1+D)(1+D+D)`, `subFPre_single` with `B = |t| ≤ D`) plus the
child's `proSig ≤ 6D + 1`: `≤ 2·(1+D)(1+2D)·D + 12D + 3`. -/
theorem shiftsV_proExs_le_sharp {tbl N N' B' Wl Wc W T s p t i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∃ p) ∈ s) (ht : IsSemiterm LAct 0 t)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D) (htD : termLen LAct t ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : i + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    shiftsV (proExs walkPieces Wl Wc W T s p t i) ≤ 2 * ((1 + D) * (1 + D + D)) * D + 12 * D + 3 := by
  have hptD : formulaLen LAct (substs1 LAct t p) ≤ D := le_trans (formulaLen_le_setLen_of_mem (by simp)) hcD
  obtain ⟨_, _, hsh, _⟩ := proExs_ok htbl hP htblN hWl hWc hWp hs hp hr ht hsD hcD htD hE hEQ hiE hΓ hLay
  obtain ⟨_, _, _, _, hsig, _⟩ := exsCert_ok htbl hP htblN hWc hWp hs hp hr ht hsD htD hptD hE hEQ hiE hΓ hLay
  have hpt : IsSemiformula LAct 0 (substs1 LAct t p) := hp.substs1 ht
  have hE8 : 13 * D + 18 * ‖D‖ + 8 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have hcI : IsFormulaSet LAct (insert (substs1 LAct t p) s) := IsFormulaSet.insert_iff.mpr ⟨hpt, hs⟩
  have hσI : proSig walkPieces Wl Wc W T (insert (substs1 LAct t p) s) ≤ 6 * D + 1 :=
    proSig_le htbl hP hWc htblN hWl hWp hcI (one_le_len_memberList_insert _ _) hcD hE8 hΓ
  rw [hsh]
  exact le_trans (add_le_add hsig (add_le_add (le_refl 1) hσI)) (le_of_eq (by ring))

end shifts

/-! ## 4. The arithmetic of the recursion at `m = 4` (and the LOCAL step at `m = 3`) -/

section recursion4

/-- `(y + m)⁴ ≥ y⁴ + m·(y + m)³` — the `p4` twin of `Verify2.p6_split`. -/
lemma p4_split (y m : V) : p4 y + m * p3 (y + m) ≤ p4 (y + m) := by
  rw [p4_eq (y + m), p4_eq y, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (p3_mono le_self_add) zero_le) (le_refl _)

/-- **The one-child recursion step at `m = 4`**: `X + Cs·y⁴ ≤ Cs·d⁴` when `d = y + m`, `m ≥ 1`, `X ≤ Cs·d³`
(`Verify2.rec1` with `p5/p6 ↦ p3/p4`). -/
lemma rec1₄ {Cs X y m d : V} (hm : 1 ≤ m) (hd : d = y + m) (hX : X ≤ Cs * p3 d) : X + Cs * p4 y ≤ Cs * p4 d := by
  have h := p4_split y m
  rw [← hd] at h
  calc X + Cs * p4 y ≤ Cs * p3 d + Cs * p4 y := add_le_add hX (le_refl _)
    _ = Cs * (p4 y + 1 * p3 d) := by ring
    _ ≤ Cs * (p4 y + m * p3 d) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hm zero_le)) zero_le
    _ ≤ Cs * p4 d := mul_le_mul_of_nonneg_left h zero_le

/-- The two-children recursion step at `m = 4`. -/
lemma rec2₄ {Cs X y₁ y₂ m d : V} (hm : 1 ≤ m) (hd : d = y₁ + y₂ + m) (hX : X ≤ Cs * p3 d) :
    X + Cs * p4 y₁ + Cs * p4 y₂ ≤ Cs * p4 d := by
  have h := rec1₄ (Cs := Cs) (X := X) (y := y₁ + y₂) hm hd hX
  calc X + Cs * p4 y₁ + Cs * p4 y₂ = X + Cs * (p4 y₁ + p4 y₂) := by ring
    _ ≤ X + Cs * p4 (y₁ + y₂) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (p4_add_le _ _) zero_le)
    _ ≤ Cs * p4 d := h

/-- A linear cap sits under `Cs·d³` for `d ≥ 1` and `Cs ≥ a + b`. -/
lemma lin_le_p3 {a b Cs d : V} (hd : 1 ≤ d) (hab : a + b ≤ Cs) : a * d + b ≤ Cs * p3 d := by
  calc a * d + b ≤ a * p3 d + b * p3 d := add_le_add (mul_le_mul_of_nonneg_left (le_p3_self hd) zero_le)
        (le_mul_of_one_le_right zero_le (one_le_p3 hd))
    _ = (a + b) * p3 d := by ring
    _ ≤ Cs * p3 d := mul_le_mul_of_nonneg_right hab zero_le

lemma capE4 {Ckv E e X a : V} (hE : Ckv * p4 e ≤ E) (ha : a ≤ Ckv) (hX : X ≤ a * p4 e) : X ≤ E :=
  le_trans hX (le_trans (mul_le_mul_of_nonneg_right ha zero_le) hE)

lemma capE4' {Ckv E e X a : V} (hE : Ckv * p4 e ≤ E) (he : 1 ≤ e) (ha : a ≤ Ckv) (hX : X ≤ a * e) : X ≤ E :=
  le_trans hX (le_trans (mul_le_mul ha (le_p4_self he) zero_le zero_le) hE)

/-- `Cs·y⁴ ≤ Cs·d⁴` for `y ≤ d`. -/
lemma child_bound4 {Cs y d : V} (h : y ≤ d) : Cs * p4 y ≤ Cs * p4 d := mul_le_mul_of_nonneg_left (p4_mono h) zero_le

lemma one_le_Cs_p4 {Cs d : V} (hCs : 1 ≤ Cs) (hd : 1 ≤ d) : 1 ≤ Cs * p4 d :=
  le_trans hCs (le_mul_of_one_le_right zero_le (one_le_p4 hd))

/-- The cubic caps: `2·(a·b)·c ≤ 2·ka·kb·kc·e³` for `a ≤ ka·e`, `b ≤ kb·e`, `c ≤ kc·e` (`Verify2.quad_cap` lands in `p6`). -/
lemma quad_cap3 {e a b c ka kb kc : V} (ha : a ≤ ka * e) (hb : b ≤ kb * e) (hc : c ≤ kc * e) :
    2 * (a * b) * c ≤ 2 * ka * kb * kc * p3 e := by
  calc 2 * (a * b) * c ≤ 2 * (ka * e * (kb * e)) * (kc * e) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul ha hb zero_le zero_le) zero_le) hc zero_le zero_le
    _ = 2 * ka * kb * kc * p3 e := by simp only [p3]; ring

/-- The uniform cubic prologue shift at `D = 2d`: `402·p3 (2(d+1)) = 3216·p3 (d+1)`. -/
lemma proSA_p3 (d : V) : 402 * p3 (2 * (d + 1)) = 3216 * p3 (d + 1) := by rw [p3_two_mul]; ring

/-- The node's own contribution under the recursion's budget: `402·p3 (2(d+1)) + 3 ≤ Cs·p3 d` for `d ≥ 1`, `Cs ≥ 25731`
(`Verify2.proSA_add_le_p5` at `m = 4`). -/
lemma proSA_add_le_p3 {Cs d : V} (hd : 1 ≤ d) (hCs : 25731 ≤ Cs) : 402 * p3 (2 * (d + 1)) + 3 ≤ Cs * p3 d := by
  rw [proSA_p3]
  have h1 : p3 (d + 1) ≤ 8 * p3 d := p3_succ_le hd
  calc 3216 * p3 (d + 1) + 3 ≤ 3216 * (8 * p3 d) + 3 * p3 d :=
        add_le_add (mul_le_mul_of_nonneg_left h1 zero_le) (le_mul_of_one_le_right zero_le (one_le_p3 hd))
    _ = 25731 * p3 d := by ring
    _ ≤ Cs * p3 d := mul_le_mul_of_nonneg_right hCs zero_le

/-- **The `all`/`exs` node's shift inequality at `m = 4`**, in the shape `Verify3`'s arms close with: the cubic prologue
shift (`SA = 402·p3 (2(d+1))` — `256 ≤ 402` covers `exs`), the child's `Cs·p4 y`, the node's `3`, under `Cs·p4 d` for
`d = y + m'`, `m' ≥ 1` (`m' = setLen s + 1`, resp. `setLen s + termLen t + 1`). -/
lemma allNode_p4 {Cs y m' d : V} (hd1 : 1 ≤ d) (hm : 1 ≤ m') (hdeq : d = y + m') (hCs : 25731 ≤ Cs) :
    402 * p3 (2 * (d + 1)) + Cs * p4 y + 3 ≤ Cs * p4 d := by
  calc 402 * p3 (2 * (d + 1)) + Cs * p4 y + 3 = (402 * p3 (2 * (d + 1)) + 3) + Cs * p4 y := by ring
    _ ≤ Cs * p4 d := rec1₄ hm hdeq (proSA_add_le_p3 hd1 hCs)

/-- The `axm` leaf at `m = 4`: `Cv·p3 (|p|+1) + 1 ≤ Csv·p4 d` for `|p| + 1 ≤ d`, `Cv + 1 ≤ Csv` (`Verify3`'s leaf glue). -/
lemma axmLeaf_p4 {Cv Csv a d : V} (had : a + 1 ≤ d) (hd1 : 1 ≤ d) (hCv : Cv + 1 ≤ Csv) :
    Cv * p3 (a + 1) + 1 ≤ Csv * p4 d := by
  calc Cv * p3 (a + 1) + 1 ≤ Cv * p4 d + 1 * p4 d :=
        add_le_add (mul_le_mul_of_nonneg_left (le_trans (p3_mono had) (p3_le_p4 hd1)) zero_le)
          (le_mul_of_one_le_right zero_le (one_le_p4 hd1))
    _ = (Cv + 1) * p4 d := by ring
    _ ≤ Csv * p4 d := mul_le_mul_of_nonneg_right hCv zero_le

/-! ### 4.1 The E-room caps of the `all`/`exs` arms at `D = 2d`, landing in `p3 (d+1)` / `p4 (d+1)` -/

lemma allEQ_p3 {D d : V} (hDe : D = 2 * d) :
    2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ 27 * p3 (d + 1) := by
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hD1 : 1 + D ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have hD2 : 1 + D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 0) (by rw [hDe]; ring)
  have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have h1 := quad_cap3 hD1 hD2 hD3
  have h2 : 4 * D + 11 ≤ 11 * (d + 1) := le_of_add_eq' (c := 3 * d) (by rw [hDe]; ring)
  calc 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11
      = 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + (4 * D + 11) := by ring
    _ ≤ 2 * 2 * 2 * 2 * p3 (d + 1) + 11 * (d + 1) := add_le_add h1 h2
    _ ≤ 2 * 2 * 2 * 2 * p3 (d + 1) + 11 * p3 (d + 1) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p3_self he1) zero_le)
    _ = 27 * p3 (d + 1) := by ring

lemma alliE_p3 {D d : V} (hDe : D = 2 * d) :
    0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ 96 * p3 (d + 1) := by
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hD0 : D ≤ 2 * (d + 1) := le_of_add_eq' (c := 2) (by rw [hDe]; ring)
  have hD1 : 1 + D ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have hD2 : 1 + D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 0) (by rw [hDe]; ring)
  have h1 := quad_cap3 hD1 hD2 hD0
  have h2 : 40 * D + 20 ≤ 80 * (d + 1) := le_of_add_eq' (c := 60) (by rw [hDe]; ring)
  calc 0 + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 = 2 * ((1 + D) * (1 + D + 1)) * D + (40 * D + 20) := by ring
    _ ≤ 2 * 2 * 2 * 2 * p3 (d + 1) + 80 * (d + 1) := add_le_add h1 h2
    _ ≤ 2 * 2 * 2 * 2 * p3 (d + 1) + 80 * p3 (d + 1) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p3_self he1) zero_le)
    _ = 96 * p3 (d + 1) := by ring

lemma exsEQ_p3 {D d : V} (hDe : D = 2 * d) :
    2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ 43 * p3 (d + 1) := by
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hD1 : 1 + D ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have hD2 : 1 + D + D ≤ 4 * (d + 1) := le_of_add_eq' (c := 3) (by rw [hDe]; ring)
  have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have h1 := quad_cap3 hD1 hD2 hD3
  have h2 : 4 * D + 11 ≤ 11 * (d + 1) := le_of_add_eq' (c := 3 * d) (by rw [hDe]; ring)
  calc 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11
      = 2 * ((1 + D) * (1 + D + D)) * (D + 1) + (4 * D + 11) := by ring
    _ ≤ 2 * 2 * 4 * 2 * p3 (d + 1) + 11 * (d + 1) := add_le_add h1 h2
    _ ≤ 2 * 2 * 4 * 2 * p3 (d + 1) + 11 * p3 (d + 1) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p3_self he1) zero_le)
    _ = 43 * p3 (d + 1) := by ring

lemma exsiE_p3 {D d : V} (hDe : D = 2 * d) :
    0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ 112 * p3 (d + 1) := by
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hD0 : D ≤ 2 * (d + 1) := le_of_add_eq' (c := 2) (by rw [hDe]; ring)
  have hD1 : 1 + D ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have hD2 : 1 + D + D ≤ 4 * (d + 1) := le_of_add_eq' (c := 3) (by rw [hDe]; ring)
  have h1 := quad_cap3 hD1 hD2 hD0
  have h2 : 40 * D + 20 ≤ 80 * (d + 1) := le_of_add_eq' (c := 60) (by rw [hDe]; ring)
  calc 0 + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 = 2 * ((1 + D) * (1 + D + D)) * D + (40 * D + 20) := by ring
    _ ≤ 2 * 2 * 4 * 2 * p3 (d + 1) + 80 * (d + 1) := add_le_add h1 h2
    _ ≤ 2 * 2 * 4 * 2 * p3 (d + 1) + 80 * p3 (d + 1) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_p3_self he1) zero_le)
    _ = 112 * p3 (d + 1) := by ring

/-- The `all` arm's E-cap (`vAll_ok`'s `hE` with `SA = 402·p3 (2(d+1))`, `B = Csv·p4 y`) at `m = 4`: `≤ 5·Csv·p4 (d+1)`
once `853 ≤ Csv`. -/
lemma allE_p4 {Csv D d y : V} (hd1 : 1 ≤ d) (hDe : D = 2 * d) (hy : y ≤ d) (hCs : 853 ≤ Csv) :
    402 * p3 (2 * (d + 1)) + 40 * D + 18 * ‖D‖ + Csv * p4 y + 40 ≤ 5 * Csv * p4 (d + 1) := by
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have hlin : 40 * D + 18 * ‖D‖ + 40 ≤ 196 * p4 (d + 1) := by
    calc 40 * D + 18 * ‖D‖ + 40 ≤ (40 + 18 + 40) * (D + 1) := lin_cap 40 18 40 D
      _ ≤ (40 + 18 + 40) * (2 * (d + 1)) := mul_le_mul_of_nonneg_left hD3 zero_le
      _ = 196 * (d + 1) := by ring
      _ ≤ 196 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
  have hSA : 402 * p3 (2 * (d + 1)) ≤ 3216 * p4 (d + 1) := by
    rw [proSA_p3]; exact mul_le_mul_of_nonneg_left (p3_le_p4 he1) zero_le
  have h3412 : (3412 : V) ≤ 4 * Csv := by
    calc (3412 : V) = 4 * 853 := by norm_num
      _ ≤ 4 * Csv := mul_le_mul_of_nonneg_left hCs zero_le
  calc 402 * p3 (2 * (d + 1)) + 40 * D + 18 * ‖D‖ + Csv * p4 y + 40
      = 402 * p3 (2 * (d + 1)) + (40 * D + 18 * ‖D‖ + 40) + Csv * p4 y := by ring
    _ ≤ 3216 * p4 (d + 1) + 196 * p4 (d + 1) + Csv * p4 (d + 1) :=
        add_le_add (add_le_add hSA hlin) (child_bound4 (le_trans hy le_self_add))
    _ = (3412 + Csv) * p4 (d + 1) := by ring
    _ ≤ (4 * Csv + Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h3412 (le_refl _)) zero_le
    _ = 5 * Csv * p4 (d + 1) := by ring

/-- The `exs` arm's E-cap (`vExs_ok`'s `hE`, two prologues and two children's budgets) at `m = 4`: `≤ 5·Csv·p4 (d+1)`
once `2236 ≤ Csv`. -/
lemma exsE_p4 {Csv D d y : V} (hd1 : 1 ≤ d) (hDe : D = 2 * d) (hy : y ≤ d) (hCs : 2236 ≤ Csv) :
    2 * (402 * p3 (2 * (d + 1))) + 60 * D + 18 * ‖D‖ + 2 * (Csv * p4 y) + 60 ≤ 5 * Csv * p4 (d + 1) := by
  have he1 : (1 : V) ≤ d + 1 := le_add_self
  have hD3 : D + 1 ≤ 2 * (d + 1) := le_of_add_eq' (c := 1) (by rw [hDe]; ring)
  have hlin : 60 * D + 18 * ‖D‖ + 60 ≤ 276 * p4 (d + 1) := by
    calc 60 * D + 18 * ‖D‖ + 60 ≤ (60 + 18 + 60) * (D + 1) := lin_cap 60 18 60 D
      _ ≤ (60 + 18 + 60) * (2 * (d + 1)) := mul_le_mul_of_nonneg_left hD3 zero_le
      _ = 276 * (d + 1) := by ring
      _ ≤ 276 * p4 (d + 1) := mul_le_mul_of_nonneg_left (le_p4_self he1) zero_le
  have hSA : 402 * p3 (2 * (d + 1)) ≤ 3216 * p4 (d + 1) := by
    rw [proSA_p3]; exact mul_le_mul_of_nonneg_left (p3_le_p4 he1) zero_le
  have h6708 : (6708 : V) ≤ 3 * Csv := by
    calc (6708 : V) = 3 * 2236 := by norm_num
      _ ≤ 3 * Csv := mul_le_mul_of_nonneg_left hCs zero_le
  calc 2 * (402 * p3 (2 * (d + 1))) + 60 * D + 18 * ‖D‖ + 2 * (Csv * p4 y) + 60
      = 2 * (402 * p3 (2 * (d + 1))) + (60 * D + 18 * ‖D‖ + 60) + 2 * (Csv * p4 y) := by ring
    _ ≤ 2 * (3216 * p4 (d + 1)) + 276 * p4 (d + 1) + 2 * (Csv * p4 (d + 1)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hSA zero_le) hlin)
          (mul_le_mul_of_nonneg_left (child_bound4 (le_trans hy le_self_add)) zero_le)
    _ = (6708 + 2 * Csv) * p4 (d + 1) := by ring
    _ ≤ (3 * Csv + 2 * Csv) * p4 (d + 1) := mul_le_mul_of_nonneg_right (add_le_add h6708 (le_refl _)) zero_le
    _ = 5 * Csv * p4 (d + 1) := by ring

/-! ### 4.2 The LOCAL step at `m = 3` (per-node accounting; not used by the current `_ok`s, see the header) -/

/-- `X ≤ Cs·m³ → X + Cs·y³ ≤ Cs·(y + m)³`: a node whose own contribution is cubic in its OWN size `m` closes at degree 3. -/
lemma rec1_local {Cs X y m d : V} (hd : d = y + m) (hX : X ≤ Cs * p3 m) : X + Cs * p3 y ≤ Cs * p3 d := by
  subst hd
  calc X + Cs * p3 y ≤ Cs * p3 m + Cs * p3 y := add_le_add hX (le_refl _)
    _ = Cs * (p3 y + p3 m) := by ring
    _ ≤ Cs * p3 (y + m) := mul_le_mul_of_nonneg_left (p3_add_le y m) zero_le

lemma rec2_local {Cs X y₁ y₂ m d : V} (hd : d = y₁ + y₂ + m) (hX : X ≤ Cs * p3 m) :
    X + Cs * p3 y₁ + Cs * p3 y₂ ≤ Cs * p3 d := by
  have h := rec1_local (Cs := Cs) (X := X) (y := y₁ + y₂) hd hX
  calc X + Cs * p3 y₁ + Cs * p3 y₂ = X + Cs * (p3 y₁ + p3 y₂) := by ring
    _ ≤ X + Cs * p3 (y₁ + y₂) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (p3_add_le _ _) zero_le)
    _ ≤ Cs * p3 d := h

end recursion4

/-! ## 5. The cost corollaries at the cubic lengths (`Prologue.costSum_pro*_le'` with `costShape_mono`) -/

section costs

theorem costSum_proAll_le'' {tbl N N' B' B Wl Wc W T s p i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∀ p) ∈ s)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (free LAct p) (setShift LAct s)) ≤ D)
    (hspD : formulaLen LAct (shift LAct p) ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + 1)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : i + 2 * ((1 + D) * (1 + D + 1)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    costSum N E Γ (proAll walkPieces Wl Wc W T s p i) ≤ (402 * p3 (D + 1)) *
      (costK N E B 9 (layQ B B' D) (layD N' B' D) + (3 * ((9 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (402 * p3 (D + 1)) +
          (fvOccS LAct Γ + (402 * p3 (D + 1)) * growK B E (layQ B B' D)))) :=
  le_trans (costSum_proAll_le htbl hP htblN hWl hWc hWp hBt hPle hs hp hr hsD hcD hspD hE hEQ hiE hΓ hLay)
    (costShape_mono (len_proAll_le_cubic htbl hP hWl hWc walkPieces W T i hs hp hr hsD hcD hspD))

theorem costSum_proExs_le'' {tbl N N' B' B Wl Wc W T s p t i D E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (htblN : NumTableOK T N' B') (hWl : Wl = layoutPieces) (hWc : Wc = certPieces) (hWp : W = proPieces)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hs : IsFormulaSet LAct s) (hp : IsSemiformula LAct 1 p) (hr : (^∃ p) ∈ s) (ht : IsSemiterm LAct 0 t)
    (hsD : setLen LAct s ≤ D) (hcD : setLen LAct (insert (substs1 LAct t p) s) ≤ D) (htD : termLen LAct t ≤ D)
    (hE : 13 * D + 18 * ‖D‖ + 12 ≤ E)
    (hEQ : 2 * ((1 + D) * (1 + D + D)) * (D + 1) + 4 * D + 11 ≤ E)
    (hiE : i + 2 * ((1 + D) * (1 + D + D)) * D + 40 * D + 20 ≤ E)
    (hΓ : IsFormulaSet LAct Γ) (hLay : Layout walkPieces Wc T Γ s i) :
    costSum N E Γ (proExs walkPieces Wl Wc W T s p t i) ≤ (256 * p3 (D + 1)) *
      (costK N E B 9 (layQ B B' D) (layD N' B' D) + (3 * ((9 : ℕ) : V) + 11) *
        (ctxBoundG (growK B E (layQ B B' D)) Γ (256 * p3 (D + 1)) +
          (fvOccS LAct Γ + (256 * p3 (D + 1)) * growK B E (layQ B B' D)))) :=
  le_trans (costSum_proExs_le htbl hP htblN hWl hWc hWp hBt hPle hs hp hr ht hsD hcD htD hE hEQ hiE hΓ hLay)
    (costShape_mono (len_proExs_le_cubic htbl hP hWl hWc walkPieces W T i hs hp hr ht hsD hcD htD))

end costs

end ArithS
