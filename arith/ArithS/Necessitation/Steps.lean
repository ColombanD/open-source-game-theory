import ArithS.Necessitation.Primitives
import ArithS.Necessitation.Lib.Sets
import ArithS.Necessitation.Lib.Formulas
import ArithS.Necessitation.Lib.Lengths

/-!
# ArithS.Necessitation.Steps — using library rows on derivation codes: the fragment protocol

The two primitives of `ArithS.Necessitation.Primitives` (`useLemmaCode`: cut a stored `∀^m B`
in at witnesses; `elimExistsCode`: eliminate `∃` with the fresh eigenvariable `&0`) are
assembled here into the three STEPS every per-tag fragment of the verification proof
(`DESIGN_inner_necessitation.md` §3.3) is written in, on library rows of the three shapes the
library has (`Lib/Sets`, `Lib/Formulas`, `Lib/Lengths`, `Lib/Nodes`):

* a HORN row `∀x̄ (A₁ → … → A_j → C)` — `useHornCode`;
* a row with a conjunctive conclusion `∀x̄ (A₁ → … → C₁ ∧ C₂)` — `useHornAndCode`;
* a TOTALITY row `∀x̄ (A₁ → … → ∃ z, R(z, x̄))` — `introFactCode`.

## The fragment protocol (the calling convention of every fragment)

1. **Context.** A fragment works at a sequent code `Γ` (a finite bit-set of `LAct`-formula codes,
   read disjunctively, `IsFormulaSet Γ`). A FACT `H` is *in context* iff its negation is a member:
   `neg H ∈ Γ`. Facts are constant-size formulas about eigenvariables (`§3.4`), never numerals.
2. **Rows and instances.** A row is `Λ = ∀^m B` with matrix `B = impChain as c` (`imp` on codes,
   `imp a b = neg a ⋎ b`; `impChain [] c = c`); `dΛ` is its stored proof code (`Lib.univ_code`
   gives one of length `≤ N_Λ` in every model). It is used at CLOSED witness codes
   `es = [e₁, …, e_m]`, OUTERMOST quantifier first (`es` lists the row's variables in REVERSE
   index order: `e₁` fills `#(m-1)`, `e_m` fills `#0`). The instantiated pieces are
   `instOuter es aᵢ`, `instOuter es c` (`instOuter_impChain`), one simultaneous substitution
   each, of length `≤ |aᵢ|·E ≤ |B|·E` (`E ≥ 1` a bound on every witness length).
3. **Antecedents** must be in context: `neg (instOuter es aᵢ) ∈ Γ` for every `i` — the fragment
   NEVER derives an antecedent inline; it is a fact established earlier (by a previous step) or a
   hypothesis of the subtree.
4. **Conclusions** are delivered to a CONTINUATION `d`, a derivation code of `Γ` extended by the
   new fact: `useHornCode` — `d : insert (neg (instOuter es c)) Γ₀`; `useHornAndCode` —
   `d : insert (neg c₁') (insert (neg c₂') Γ₀)`; `introFactCode` (conclusion `^∃ R`) —
   `d : insert (neg (free R')) (setShift Γ)` where `R' = instOuterAt 1 es R` is the body under
   the witnesses and `free R'` is it at the fresh eigenvariable `&0` (so every free variable of
   `Γ` is shifted by one — the SHIFT BOOKKEEPING: facts about eigenvariables `&i` of `Γ` reappear
   as facts about `&(i+1)`, and the cost of a `setShift` is the doubling `|setShift Γ| ≤ 2|Γ|`).
   The continuation may have dropped facts (`Γ₀ ⊆ Γ`, one `wkToCode` inside the step).
5. **Polarity.** Δ₁ predicates appear in rows as `.pi` in antecedent position and `.sigma` in
   conclusion position (the `cutSentence` convention of `Lib/Sets`). A fragment therefore HOLDS a
   Δ₁ fact in the `.pi` reading (what rows consume) and, when a row DELIVERS it in the `.sigma`
   reading, converts once with the bridge row (`lib_isSemiformulaSigmaPi`, …) by one more
   `useHornCode` — as `describeAndCode` does below.
6. **Length bookkeeping.** Every step's `dlen` is `dlen dΛ + dlen d + (linear in |Γ|) +
   (a polynomial in `m`, `j`, `|B|·E`)`; the stored-proof length `dlen dΛ ≤ N_Λ` is a constant of
   the row (threaded as a hypothesis `hN`), and `E` is a constant of the fragment (witnesses are
   eigenvariables — one symbol each, so `E = 1` — or the small symbol-code numerals). Hence a
   fragment costs `O(|Γ|)` per row use plus a constant, the `O(w_ν · L_ν)` of the design note.
7. **Leaves.** `axLFactCode Γ φ` derives `insert φ Γ` from `neg φ ∈ Γ` (one `axL`);
   `wkToCode Γ d` weakens a derivation of `Γ' ⊆ Γ` to `Γ` (one `wkRule`).

The smoke test `describeAndCode` (bottom of the file) runs the protocol end to end: from
`IsFormula a`, `IsFormula b` in context (`.pi` reading), get `z = a ⋏ b` (`lib_qqAndTotal`,
`introFactCode`), then `IsFormula z` in the `.sigma` reading (`lib_isSemiformulaAnd`,
`useHornCode`), then in the `.pi` reading (`lib_isSemiformulaSigmaPi`, `useHornCode`), and hand
the continuation the context with all three new facts; its `dlen` is
`dlen d + c·(|Γ| + |a| + |b|) + C` with `C` the three rows' lengths.

V-generic (every model of `𝗜𝚺₁`); `L`, `T` generic in the steps, `LAct`/`TAct` in the smoke test.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### Horn matrices on codes: `impChain` -/

variable (L) in
/-- The Horn matrix `A₁ → (A₂ → … → C)` on codes: `impChain [] c = c`,
`impChain (a :: as) c = imp a (impChain as c)`. -/
noncomputable def impChain : List V → V → V
  | [], c => c
  | a :: as, c => imp L a (impChain as c)

@[simp] lemma impChain_nil (c : V) : impChain L [] c = c := rfl
@[simp] lemma impChain_cons (a : V) (as : List V) (c : V) :
    impChain L (a :: as) c = imp L a (impChain L as c) := rfl

lemma isSemiformula_impChain {n : V} : ∀ {as : List V} {c : V}, (∀ a ∈ as, IsSemiformula L n a) →
    IsSemiformula L n c → IsSemiformula L n (impChain L as c)
  | [], _, _, hc => hc
  | a :: as, c, has, hc => by
    rw [impChain_cons, IsSemiformula.imp]
    exact ⟨has a (by simp), isSemiformula_impChain (fun a' h ↦ has a' (by simp [h])) hc⟩

-- `neg_imp_code` (`∼(a → b) = a ⋏ ∼b`) and `formulaLen_imp` (`|a → b| = |a| + |b| + 1`) are in `ArithS.CutV`.

/-- The first antecedent and the rest of the chain are shorter than the chain. -/
lemma formulaLen_le_impChain_cons {n : V} {a : V} {as : List V} {c : V}
    (ha : IsSemiformula L n a) (has : ∀ a' ∈ as, IsSemiformula L n a') (hc : IsSemiformula L n c) :
    formulaLen L a ≤ formulaLen L (impChain L (a :: as) c) ∧
    formulaLen L (impChain L as c) ≤ formulaLen L (impChain L (a :: as) c) := by
  rw [impChain_cons, formulaLen_imp ha.isUFormula (isSemiformula_impChain has hc).isUFormula]
  exact ⟨le_trans le_self_add le_self_add, le_trans le_add_self le_self_add⟩

/-- The conclusion is shorter than the chain. -/
lemma formulaLen_concl_le_impChain {n : V} : ∀ {as : List V} {c : V},
    (∀ a ∈ as, IsSemiformula L n a) → IsSemiformula L n c →
    formulaLen L c ≤ formulaLen L (impChain L as c)
  | [], _, _, _ => le_refl _
  | a :: as, c, has, hc =>
    le_trans (formulaLen_concl_le_impChain (fun a' h ↦ has a' (by simp [h])) hc)
      (formulaLen_le_impChain_cons (has a (by simp)) (fun a' h ↦ has a' (by simp [h])) hc).2

/-! ### `instOuter` distributes over the connectives; `instOuterAt` under an `∃` -/

lemma subOuter_imp {n : ℕ} {e a b : V} (ha : IsSemiformula L ((n : V) + 1) a)
    (hb : IsSemiformula L ((n : V) + 1) b) (he : IsTerm L e) :
    subOuter L n e (imp L a b) = imp L (subOuter L n e a) (subOuter L n e b) := by
  unfold subOuter Bootstrapping.imp
  rw [substs_or ha.isUFormula.neg hb.isUFormula, substs_neg ha (isSemitermVec_qVecIter_single he)]

lemma subOuter_and {n : ℕ} {e a b : V} (ha : IsUFormula L a) (hb : IsUFormula L b) :
    subOuter L n e (a ^⋏ b) = subOuter L n e a ^⋏ subOuter L n e b := by
  unfold subOuter
  rw [substs_and ha hb]

lemma instOuter_imp : ∀ (es : List V) {a b : V}, IsSemiformula L (es.length : V) a →
    IsSemiformula L (es.length : V) b → (∀ e ∈ es, IsTerm L e) →
    instOuter L es (imp L a b) = imp L (instOuter L es a) (instOuter L es b)
  | [], _, _, _, _, _ => rfl
  | e :: es, a, b, ha, hb, hes => by
    have ha' : IsSemiformula L ((es.length : V) + 1) a := by simpa [Nat.cast_succ] using ha
    have hb' : IsSemiformula L ((es.length : V) + 1) b := by simpa [Nat.cast_succ] using hb
    have he : IsTerm L e := hes e (by simp)
    rw [instOuter_cons, instOuter_cons, instOuter_cons, subOuter_imp ha' hb' he]
    exact instOuter_imp es (isSemiformula_subOuter ha' he) (isSemiformula_subOuter hb' he)
      (fun e' he' ↦ hes e' (by simp [he']))

lemma instOuter_and : ∀ (es : List V) {a b : V}, IsSemiformula L (es.length : V) a →
    IsSemiformula L (es.length : V) b → (∀ e ∈ es, IsTerm L e) →
    instOuter L es (a ^⋏ b) = instOuter L es a ^⋏ instOuter L es b
  | [], _, _, _, _, _ => rfl
  | e :: es, a, b, ha, hb, hes => by
    have ha' : IsSemiformula L ((es.length : V) + 1) a := by simpa [Nat.cast_succ] using ha
    have hb' : IsSemiformula L ((es.length : V) + 1) b := by simpa [Nat.cast_succ] using hb
    have he : IsTerm L e := hes e (by simp)
    rw [instOuter_cons, instOuter_cons, instOuter_cons, subOuter_and ha.isUFormula hb.isUFormula]
    exact instOuter_and es (isSemiformula_subOuter ha' he) (isSemiformula_subOuter hb' he)
      (fun e' he' ↦ hes e' (by simp [he']))

/-- `instOuter es (A₁ → … → C) = A₁[ē] → … → C[ē]`. -/
lemma instOuter_impChain (es : List V) (hes : ∀ e ∈ es, IsTerm L e) : ∀ {as : List V} {c : V},
    (∀ a ∈ as, IsSemiformula L (es.length : V) a) → IsSemiformula L (es.length : V) c →
    instOuter L es (impChain L as c) = impChain L (as.map (instOuter L es)) (instOuter L es c)
  | [], _, _, _ => rfl
  | a :: as, c, has, hc => by
    rw [impChain_cons, List.map_cons, impChain_cons,
      instOuter_imp es (has a (by simp))
        (isSemiformula_impChain (fun a' h ↦ has a' (by simp [h])) hc) hes,
      instOuter_impChain es hes (fun a' h ↦ has a' (by simp [h])) hc]

lemma qVecIter_qVec (n : ℕ) (w : V) : qVecIter L n (qVec L w) = qVec L (qVecIter L n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [qVecIter_succ, qVecIter_succ, ih]

/-- `subOuter n e (∃ q) = ∃ (subOuter (n + 1) e q)` — the substitution pushed under the quantifier. -/
lemma subOuter_exs {n : ℕ} {e q : V} (hq : IsUFormula L q) :
    subOuter L n e (^∃ q) = ^∃ (subOuter L (n + 1) e q) := by
  unfold subOuter
  rw [substs_ex hq, qVecIter_succ, qVecIter_qVec]

variable (L) in
/-- `instOuter` under `k` quantifiers: instantiate the `(es.length + k)`-semiformula `q` at `es`
(outermost first) leaving the `k` innermost bound variables in place. `instOuterAt 0 = instOuter`;
`instOuterAt k es (∃ q) = ∃ (instOuterAt (k + 1) es q)`. -/
noncomputable def instOuterAt (k : ℕ) : List V → V → V
  | [], q => q
  | e :: es, q => instOuterAt k es (subOuter L (es.length + k) e q)

@[simp] lemma instOuterAt_nil (k : ℕ) (q : V) : instOuterAt L k [] q = q := rfl
@[simp] lemma instOuterAt_cons (k : ℕ) (e : V) (es : List V) (q : V) :
    instOuterAt L k (e :: es) q = instOuterAt L k es (subOuter L (es.length + k) e q) := rfl

lemma instOuterAt_zero : ∀ (es : List V) (q : V), instOuterAt L 0 es q = instOuter L es q
  | [], _ => rfl
  | e :: es, q => by rw [instOuterAt_cons, instOuter_cons, Nat.add_zero, instOuterAt_zero]

lemma isSemiformula_instOuterAt (k : ℕ) : ∀ (es : List V) {q : V},
    IsSemiformula L ((es.length + k : ℕ) : V) q → (∀ e ∈ es, IsTerm L e) →
    IsSemiformula L (k : V) (instOuterAt L k es q)
  | [], _, hq, _ => by simpa using hq
  | e :: es, q, hq, hes => by
    have hq' : IsSemiformula L (((es.length + k : ℕ) : V) + 1) q := by
      rw [show ((es.length + k : ℕ) : V) + 1 = (((e :: es).length + k : ℕ) : V) by
        simp only [List.length_cons]; push_cast; ring]
      exact hq
    rw [instOuterAt_cons]
    exact isSemiformula_instOuterAt k es (isSemiformula_subOuter hq' (hes e (by simp)))
      (fun e' he' ↦ hes e' (by simp [he']))

lemma instOuterAt_exs (k : ℕ) : ∀ (es : List V) {q : V},
    IsSemiformula L ((es.length + k + 1 : ℕ) : V) q → (∀ e ∈ es, IsTerm L e) →
    instOuterAt L k es (^∃ q) = ^∃ (instOuterAt L (k + 1) es q)
  | [], _, _, _ => rfl
  | e :: es, q, hq, hes => by
    have hq' : IsSemiformula L (((es.length + (k + 1) : ℕ) : V) + 1) q := by
      rw [show ((es.length + (k + 1) : ℕ) : V) + 1 = (((e :: es).length + k + 1 : ℕ) : V) by
        simp only [List.length_cons]; push_cast; ring]
      exact hq
    rw [instOuterAt_cons, instOuterAt_cons, subOuter_exs hq.isUFormula]
    exact instOuterAt_exs k es (isSemiformula_subOuter hq' (hes e (by simp)))
      (fun e' he' ↦ hes e' (by simp [he']))

/-- The instance of an `∃`-conclusion: `instOuter es (∃ R) = ∃ (instOuterAt 1 es R)`. -/
lemma instOuter_exs (es : List V) {R : V} (hR : IsSemiformula L ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsTerm L e) :
    instOuter L es (^∃ R) = ^∃ (instOuterAt L 1 es R) := by
  rw [← instOuterAt_zero, instOuterAt_exs 0 es (by simpa [Nat.cast_succ] using hR) hes]

/-- The body under the witnesses is a `1`-semiformula. -/
lemma isSemiformula_one_instOuterAt (es : List V) {R : V}
    (hR : IsSemiformula L ((es.length : V) + 1) R) (hes : ∀ e ∈ es, IsTerm L e) :
    IsSemiformula L 1 (instOuterAt L 1 es R) := by
  have := isSemiformula_instOuterAt 1 es (q := R) (by simpa [Nat.cast_succ] using hR) hes
  simpa using this

/-! ### Step 1 — `useHornCode`: use a Horn row whose antecedents are in context -/

section steps

variable {T : Theory L} [T.Δ₁]

variable (L) in
/-- Close the goal `insert (neg (A₁ → … → A_j → C)) S` (the hypothesis `A₁ → … → C` in
context `S`, read `A₁ ⋏ (A₂ ⋏ … ⋏ ∼C)`) when every `neg Aᵢ ∈ S`: `j` `andIntro` nodes, each left
premise `insert Aᵢ Sᵢ` closed by `axL`, the final right premise `insert (neg C) S_j` the
continuation `d` (a derivation of `insert (neg C) Γ`, `Γ ⊆ S`) weakened once. The context grows
by one suffix per level (`Sᵢ₊₁ = insert (neg (Aᵢ₊₁ → … → C)) Sᵢ`). -/
noncomputable def hornClose : List V → V → V → V → V
  | [], c, S, d => wkRule (insert (neg L c) S) d
  | a :: as, c, S, d =>
    andIntro (insert (neg L (impChain L (a :: as) c)) S) a (neg L (impChain L as c))
      (axL (insert a (insert (neg L (impChain L (a :: as) c)) S)) a)
      (hornClose as c (insert (neg L (impChain L (a :: as) c)) S) d)

@[simp] lemma hornClose_nil (c S d : V) : hornClose L [] c S d = wkRule (insert (neg L c) S) d := rfl
@[simp] lemma hornClose_cons (a : V) (as : List V) (c S d : V) :
    hornClose L (a :: as) c S d =
      andIntro (insert (neg L (impChain L (a :: as) c)) S) a (neg L (impChain L as c))
        (axL (insert a (insert (neg L (impChain L (a :: as) c)) S)) a)
        (hornClose L as c (insert (neg L (impChain L (a :: as) c)) S) d) := rfl

theorem hornClose_proof : ∀ (as : List V) {c S Γ d : V},
    (∀ a ∈ as, IsFormula L a) → IsFormula L c → IsFormulaSet L S →
    (∀ a ∈ as, neg L a ∈ S) → Γ ⊆ S → DerivationOf T d (insert (neg L c) Γ) →
    DerivationOf T (hornClose L as c S d) (insert (neg L (impChain L as c)) S)
  | [], c, S, Γ, d, _, hc, hS, _, hΓ, hd =>
    ⟨by simp, Derivation.wkRule (by simp [hc, hS]) (insert_subset_insert_of_subset _ hΓ) hd⟩
  | a :: as, c, S, Γ, d, has, hc, hS, hneg, hΓ, hd => by
    have ha : IsFormula L a := has a (by simp)
    have has' : ∀ a' ∈ as, IsFormula L a' := fun a' h ↦ has a' (by simp [h])
    have hch : IsFormula L (impChain L as c) := isSemiformula_impChain has' hc
    have hfull : IsFormula L (impChain L (a :: as) c) := isSemiformula_impChain has hc
    have hS₁ : IsFormulaSet L (insert (neg L (impChain L (a :: as) c)) S) := by simp [hS, ha, hch]
    have e₁ : DerivationOf T (axL (insert a (insert (neg L (impChain L (a :: as) c)) S)) a)
        (insert a (insert (neg L (impChain L (a :: as) c)) S)) :=
      ⟨by simp, Derivation.axL (by simp [ha, hS, hch]) (by simp) (by simp [hneg a (by simp)])⟩
    have e₂ := hornClose_proof as has' hc hS₁ (fun a' h ↦ by simp [hneg a' (by simp [h])])
      (subset_insert_of_subset _ hΓ) hd
    refine ⟨by simp, Derivation.andIntro ?_ e₁ e₂⟩
    rw [impChain_cons, neg_imp_code ha.isUFormula hch.isUFormula]
    simp

/-- **The length of the closing chain** (`j = as.length`, `F ≥ |A₁ → … → C|`, `G ≥ |S|`):
`dlen ≤ dlen d + (2j + 1)·(G + (j + 1)·F + 1)` — `2j + 1` sequents, each of size
`≤ G + (j + 1)·F` (the accumulated suffixes plus the principal formula). -/
theorem dlen_hornClose_le {F : V} : ∀ (as : List V) {c S Γ d G : V},
    (∀ a ∈ as, IsFormula L a) → IsFormula L c → IsFormulaSet L S →
    (∀ a ∈ as, neg L a ∈ S) → Γ ⊆ S → DerivationOf T d (insert (neg L c) Γ) →
    formulaLen L (impChain L as c) ≤ F → setLen L S ≤ G →
    dlen T (hornClose L as c S d) ≤
      dlen T d + (2 * (as.length : V) + 1) * (G + ((as.length : V) + 1) * F + 1)
  | [], c, S, Γ, d, G, _, hc, hS, _, hΓ, hd, hF, hG => by
    have hpf := hornClose_proof (T := T) [] (by simp) hc hS (by simp) hΓ hd
    have hlen : dlen T (hornClose L [] c S d) = setLen L (insert (neg L c) S) + dlen T d + 1 :=
      dlen_eq_of_graph hpf.2 (DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩)
    have h1 : setLen L (insert (neg L c) S) ≤ G + F := by
      refine le_trans (setLen_insert_le _ _) (add_le_add hG ?_)
      rw [formulaLen_neg hc.isUFormula]; simpa using hF
    rw [hlen]
    calc setLen L (insert (neg L c) S) + dlen T d + 1 ≤ (G + F) + dlen T d + 1 := by gcongr
      _ = dlen T d + (2 * (([] : List V).length : V) + 1) * (G + ((([] : List V).length : V) + 1) * F + 1) := by
        simp only [List.length_nil, Nat.cast_zero]; ring
  | a :: as, c, S, Γ, d, G, has, hc, hS, hneg, hΓ, hd, hF, hG => by
    have ha : IsFormula L a := has a (by simp)
    have has' : ∀ a' ∈ as, IsFormula L a' := fun a' h ↦ has a' (by simp [h])
    have hch : IsFormula L (impChain L as c) := isSemiformula_impChain has' hc
    have hfull : IsFormula L (impChain L (a :: as) c) := isSemiformula_impChain has hc
    have hS₁ : IsFormulaSet L (insert (neg L (impChain L (a :: as) c)) S) := by simp [hS, ha, hch]
    have hneg₁ : ∀ a' ∈ as, neg L a' ∈ insert (neg L (impChain L (a :: as) c)) S :=
      fun a' h ↦ by simp [hneg a' (by simp [h])]
    have hΓ₁ : Γ ⊆ insert (neg L (impChain L (a :: as) c)) S := subset_insert_of_subset _ hΓ
    have e₂ := hornClose_proof (T := T) as has' hc hS₁ hneg₁ hΓ₁ hd
    have hpf := hornClose_proof (T := T) (a :: as) has hc hS hneg hΓ hd
    have hlen : dlen T (hornClose L (a :: as) c S d) =
        setLen L (insert (neg L (impChain L (a :: as) c)) S)
          + (setLen L (insert a (insert (neg L (impChain L (a :: as) c)) S)) + 1)
          + dlen T (hornClose L as c (insert (neg L (impChain L (a :: as) c)) S) d) + 1 :=
      dlen_eq_of_graph hpf.2
        (DlenGraph.andIntro_iff.mpr ⟨_, _, DlenGraph.axL_iff.mpr rfl, dlen_graph e₂.2, rfl⟩)
    have hlenF : formulaLen L (impChain L as c) ≤ F :=
      le_trans (formulaLen_le_impChain_cons ha has' hc).2 hF
    have haF : formulaLen L a ≤ F := le_trans (formulaLen_le_impChain_cons ha has' hc).1 hF
    have hS₁G : setLen L (insert (neg L (impChain L (a :: as) c)) S) ≤ G + F := by
      refine le_trans (setLen_insert_le _ _) (add_le_add hG ?_)
      rw [formulaLen_neg hfull.isUFormula]; exact hF
    have hS₁a : setLen L (insert a (insert (neg L (impChain L (a :: as) c)) S)) ≤ G + F + F :=
      le_trans (setLen_insert_le _ _) (add_le_add hS₁G haF)
    have hIH := dlen_hornClose_le (F := F) as has' hc hS₁ hneg₁ hΓ₁ hd hlenF hS₁G
    rw [hlen]
    calc setLen L (insert (neg L (impChain L (a :: as) c)) S)
          + (setLen L (insert a (insert (neg L (impChain L (a :: as) c)) S)) + 1)
          + dlen T (hornClose L as c (insert (neg L (impChain L (a :: as) c)) S) d) + 1
        ≤ (G + F) + ((G + F + F) + 1)
          + (dlen T d + (2 * (as.length : V) + 1) * ((G + F) + ((as.length : V) + 1) * F + 1)) + 1 := by
          gcongr
      _ = (dlen T d + (2 * (as.length : V) + 1) * (G + ((as.length : V) + 1 + 1) * F + 1))
          + (2 * G + 3 * F + 2) := by ring
      _ ≤ (dlen T d + (2 * (as.length : V) + 1) * (G + ((as.length : V) + 1 + 1) * F + 1))
          + (2 * G + 3 * F + 2) + (2 * (as.length : V) + 1) * F := le_self_add
      _ = dlen T d + (2 * ((a :: as).length : V) + 1) * (G + (((a :: as).length : V) + 1) * F + 1) := by
          simp only [List.length_cons, Nat.cast_succ]; ring

variable (L) in
/-- **Use a Horn row** `Λ = ∀^m (A₁ → … → A_j → C)` (matrix `impChain as c`, stored proof `dΛ`)
at the witnesses `es` when every instantiated antecedent is in context
(`neg (instOuter es Aᵢ) ∈ Γ`), delivering `C[ē]` to the continuation
`d : insert (neg (instOuter es c)) Γ₀` (`Γ₀ ⊆ Γ`). -/
noncomputable def useHornCode (Γ : V) (es as : List V) (c dΛ d : V) : V :=
  useLemmaCode L Γ es (impChain L as c) dΛ
    (hornClose L (as.map (instOuter L es)) (instOuter L es c) Γ d)

/-- The instantiated pieces are formulas and the instantiated antecedents are in context. -/
lemma hornClose_instances {Γ : V} {es as : List V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a) (hes : ∀ e ∈ es, IsTerm L e)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ) :
    (∀ a' ∈ as.map (instOuter L es), IsFormula L a') ∧
    (∀ a' ∈ as.map (instOuter L es), neg L a' ∈ Γ) := by
  refine ⟨fun a' ha' ↦ ?_, fun a' ha' ↦ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    exact isFormula_instOuter es (has a ha) hes
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    exact hneg a ha

theorem useHornCode_proof {Γ Γ₀ : V} {es as : List V} {c dΛ d : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a) (hc : IsSemiformula L (es.length : V) c)
    (hes : ∀ e ∈ es, IsTerm L e) (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as c)))
    (hd : DerivationOf T d (insert (neg L (instOuter L es c)) Γ₀)) :
    DerivationOf T (useHornCode L Γ es as c dΛ d) Γ := by
  have hB : IsSemiformula L (es.length : V) (impChain L as c) := isSemiformula_impChain has hc
  refine useLemmaCode_proof hB hes hΓ (subset_refl Γ) hΛ ?_
  rw [instOuter_impChain es hes has hc]
  exact hornClose_proof _ (hornClose_instances has hes hneg).1 (isFormula_instOuter es hc hes) hΓ
    (hornClose_instances has hes hneg).2 hsub hd

/-- **The bound for `useHornCode`** (`m = es.length`, `j = as.length`, `E ≥ 1` bounds the witness
lengths, `F ≥ |A₁ → … → C|·E` bounds every instantiated piece):
`dlen ≤ dlen dΛ + dlen d + (m + 3)·|Γ| + (m + 1)²·(F + m) + |B| + m·E + 2m + 3
  + (2j + 1)·(|Γ| + (j + 1)·F + 1)`. -/
theorem dlen_useHornCode_le {E F : V} (hE : 1 ≤ E) {Γ Γ₀ : V} {es as : List V} {c dΛ d : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a) (hc : IsSemiformula L (es.length : V) c)
    (hes : ∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E) (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as c)))
    (hd : DerivationOf T d (insert (neg L (instOuter L es c)) Γ₀))
    (hF : formulaLen L (impChain L as c) * E ≤ F) :
    dlen T (useHornCode L Γ es as c dΛ d) ≤
      dlen T dΛ + dlen T d + ((es.length : V) + 3) * setLen L Γ
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + formulaLen L (impChain L as c) + (es.length : V) * E + 2 * (es.length : V) + 3
        + (2 * (as.length : V) + 1) * (setLen L Γ + ((as.length : V) + 1) * F + 1) := by
  have hB : IsSemiformula L (es.length : V) (impChain L as c) := isSemiformula_impChain has hc
  have hes₁ : ∀ e ∈ es, IsTerm L e := fun e he ↦ (hes e he).1
  have hinst := hornClose_instances has hes₁ hneg
  have hc' : IsFormula L (instOuter L es c) := isFormula_instOuter es hc hes₁
  have hlen : formulaLen L (impChain L (as.map (instOuter L es)) (instOuter L es c)) ≤ F := by
    rw [← instOuter_impChain es hes₁ has hc]
    exact le_trans (formulaLen_instOuter_le hE es hB hes) hF
  have hcont : DerivationOf T (hornClose L (as.map (instOuter L es)) (instOuter L es c) Γ d)
      (insert (neg L (instOuter L es (impChain L as c))) Γ) := by
    rw [instOuter_impChain es hes₁ has hc]
    exact hornClose_proof _ hinst.1 hc' hΓ hinst.2 hsub hd
  have h₁ := dlen_useLemmaCode_le (T := T) hE hB hes hΓ (subset_refl Γ) hΛ hcont
    (F := F + (es.length : V)) (add_le_add hF (le_refl _))
  have h₂ := dlen_hornClose_le (T := T) (F := F) (as.map (instOuter L es)) hinst.1 hc' hΓ hinst.2
    hsub hd hlen (le_refl (setLen L Γ))
  rw [formulaLen_allsIter hB.isUFormula] at h₁
  simp only [List.length_map] at h₂
  unfold useHornCode
  refine le_trans h₁ ?_
  calc dlen T dΛ + dlen T (hornClose L (as.map (instOuter L es)) (instOuter L es c) Γ d)
        + ((es.length : V) + 3) * setLen L Γ + (formulaLen L (impChain L as c) + (es.length : V))
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + (es.length : V) * E + (es.length : V) + 3
      ≤ dlen T dΛ + (dlen T d + (2 * (as.length : V) + 1) * (setLen L Γ + ((as.length : V) + 1) * F + 1))
        + ((es.length : V) + 3) * setLen L Γ + (formulaLen L (impChain L as c) + (es.length : V))
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + (es.length : V) * E + (es.length : V) + 3 := by gcongr
    _ = _ := by ring

/-! ### Step 2 — `useHornAndCode`: a conjunctive conclusion, both conjuncts delivered -/

variable (L) in
/-- Close `insert (neg (p ⋏ q)) Γ` (`= insert (∼p ⋎ ∼q) Γ`) from a continuation deriving
`insert (neg p) (insert (neg q) Γ)`: one `orIntro`, the continuation weakened once. -/
noncomputable def splitAndCode (Γ p q d : V) : V :=
  orIntro (insert (neg L p ^⋎ neg L q) Γ) (neg L p) (neg L q)
    (wkRule (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ))) d)

theorem splitAndCode_proof {Γ Γ₀ p q d : V} (hp : IsFormula L p) (hq : IsFormula L q)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hd : DerivationOf T d (insert (neg L p) (insert (neg L q) Γ₀))) :
    DerivationOf T (splitAndCode L Γ p q d) (insert (neg L (p ^⋏ q)) Γ) := by
  rw [neg_and hp.isUFormula hq.isUFormula]
  have e : DerivationOf T (wkRule (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ))) d)
      (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ))) :=
    ⟨by simp, Derivation.wkRule (by simp [hp, hq, hΓ])
      (insert_subset_insert_of_subset _ (insert_subset_insert_of_subset _
        (subset_insert_of_subset _ hsub))) hd⟩
  exact ⟨by simp [splitAndCode], Derivation.orIntro (by simp) e⟩

theorem dlen_splitAndCode {Γ Γ₀ p q d : V} (hp : IsFormula L p) (hq : IsFormula L q)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hd : DerivationOf T d (insert (neg L p) (insert (neg L q) Γ₀))) :
    dlen T (splitAndCode L Γ p q d) =
      setLen L (insert (neg L p ^⋎ neg L q) Γ)
        + (setLen L (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ))) + dlen T d + 1)
        + 1 := by
  apply dlen_eq_of_graph (splitAndCode_proof hp hq hΓ hsub hd).2
  unfold splitAndCode
  exact DlenGraph.orIntro_iff.mpr ⟨_, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩, rfl⟩

/-- `dlen (splitAndCode) ≤ dlen d + 2|Γ| + 3|p| + 3|q| + 4`. -/
theorem dlen_splitAndCode_le {Γ Γ₀ p q d : V} (hp : IsFormula L p) (hq : IsFormula L q)
    (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hd : DerivationOf T d (insert (neg L p) (insert (neg L q) Γ₀))) :
    dlen T (splitAndCode L Γ p q d) ≤
      dlen T d + 2 * setLen L Γ + 3 * formulaLen L p + 3 * formulaLen L q + 4 := by
  have hp' := hp.isUFormula
  have hq' := hq.isUFormula
  have h₁ : setLen L (insert (neg L p ^⋎ neg L q) Γ) ≤ setLen L Γ + (formulaLen L p + formulaLen L q + 1) := by
    have := setLen_insert_le (L := L) (neg L p ^⋎ neg L q) Γ
    rwa [formulaLen_or hp'.neg hq'.neg, formulaLen_neg hp', formulaLen_neg hq'] at this
  have h₂ : setLen L (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ))) ≤
      setLen L Γ + (formulaLen L p + formulaLen L q + 1) + formulaLen L q + formulaLen L p := by
    calc setLen L (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ)))
        ≤ setLen L (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ)) + formulaLen L (neg L p) :=
          setLen_insert_le _ _
      _ ≤ (setLen L (insert (neg L p ^⋎ neg L q) Γ) + formulaLen L (neg L q)) + formulaLen L (neg L p) :=
          add_le_add (setLen_insert_le _ _) (le_refl _)
      _ ≤ setLen L Γ + (formulaLen L p + formulaLen L q + 1) + formulaLen L q + formulaLen L p := by
          rw [formulaLen_neg hp', formulaLen_neg hq']; gcongr
  rw [dlen_splitAndCode hp hq hΓ hsub hd]
  calc setLen L (insert (neg L p ^⋎ neg L q) Γ)
        + (setLen L (insert (neg L p) (insert (neg L q) (insert (neg L p ^⋎ neg L q) Γ))) + dlen T d + 1)
        + 1
      ≤ (setLen L Γ + (formulaLen L p + formulaLen L q + 1))
        + ((setLen L Γ + (formulaLen L p + formulaLen L q + 1) + formulaLen L q + formulaLen L p) + dlen T d + 1)
        + 1 := by gcongr
    _ = dlen T d + 2 * setLen L Γ + 3 * formulaLen L p + 3 * formulaLen L q + 4 := by ring

variable (L) in
/-- **Use a Horn row with a conjunctive conclusion** `∀^m (A₁ → … → C₁ ⋏ C₂)`, delivering BOTH
`C₁[ē]` and `C₂[ē]` to the continuation `d : insert (neg C₁[ē]) (insert (neg C₂[ē]) Γ₀)`. -/
noncomputable def useHornAndCode (Γ : V) (es as : List V) (c₁ c₂ dΛ d : V) : V :=
  useHornCode L Γ es as (c₁ ^⋏ c₂) dΛ (splitAndCode L Γ (instOuter L es c₁) (instOuter L es c₂) d)

theorem useHornAndCode_proof {Γ Γ₀ : V} {es as : List V} {c₁ c₂ dΛ d : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a)
    (hc₁ : IsSemiformula L (es.length : V) c₁) (hc₂ : IsSemiformula L (es.length : V) c₂)
    (hes : ∀ e ∈ es, IsTerm L e) (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as (c₁ ^⋏ c₂))))
    (hd : DerivationOf T d (insert (neg L (instOuter L es c₁)) (insert (neg L (instOuter L es c₂)) Γ₀))) :
    DerivationOf T (useHornAndCode L Γ es as c₁ c₂ dΛ d) Γ := by
  refine useHornCode_proof has (by simp [hc₁, hc₂]) hes hΓ (subset_refl Γ) hneg hΛ ?_
  rw [instOuter_and es hc₁ hc₂ hes]
  exact splitAndCode_proof (isFormula_instOuter es hc₁ hes) (isFormula_instOuter es hc₂ hes) hΓ hsub hd

/-- **The bound for `useHornAndCode`**: the `useHornCode` bound with the continuation's
`dlen d` replaced by `dlen d + 2|Γ| + 6F + 4` (`F ≥ |B|·E` bounds both instantiated conjuncts). -/
theorem dlen_useHornAndCode_le {E F : V} (hE : 1 ≤ E) {Γ Γ₀ : V} {es as : List V} {c₁ c₂ dΛ d : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a)
    (hc₁ : IsSemiformula L (es.length : V) c₁) (hc₂ : IsSemiformula L (es.length : V) c₂)
    (hes : ∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E) (hΓ : IsFormulaSet L Γ) (hsub : Γ₀ ⊆ Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as (c₁ ^⋏ c₂))))
    (hd : DerivationOf T d (insert (neg L (instOuter L es c₁)) (insert (neg L (instOuter L es c₂)) Γ₀)))
    (hF : formulaLen L (impChain L as (c₁ ^⋏ c₂)) * E ≤ F) :
    dlen T (useHornAndCode L Γ es as c₁ c₂ dΛ d) ≤
      dlen T dΛ + (dlen T d + 2 * setLen L Γ + 6 * F + 4) + ((es.length : V) + 3) * setLen L Γ
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + formulaLen L (impChain L as (c₁ ^⋏ c₂)) + (es.length : V) * E + 2 * (es.length : V) + 3
        + (2 * (as.length : V) + 1) * (setLen L Γ + ((as.length : V) + 1) * F + 1) := by
  have hes₁ : ∀ e ∈ es, IsTerm L e := fun e he ↦ (hes e he).1
  have hc : IsSemiformula L (es.length : V) (c₁ ^⋏ c₂) := by simp [hc₁, hc₂]
  have hB : IsSemiformula L (es.length : V) (impChain L as (c₁ ^⋏ c₂)) := isSemiformula_impChain has hc
  have hc₁' := isFormula_instOuter es hc₁ hes₁
  have hc₂' := isFormula_instOuter es hc₂ hes₁
  have hcF : formulaLen L (c₁ ^⋏ c₂) * E ≤ F :=
    le_trans (mul_le_mul_of_nonneg_right (formulaLen_concl_le_impChain has hc) zero_le) hF
  have h₁ : formulaLen L (instOuter L es c₁) ≤ F := by
    refine le_trans (formulaLen_instOuter_le hE es hc₁ hes) (le_trans ?_ hcF)
    rw [formulaLen_and hc₁.isUFormula hc₂.isUFormula]
    exact mul_le_mul_of_nonneg_right (le_trans le_self_add le_self_add) zero_le
  have h₂ : formulaLen L (instOuter L es c₂) ≤ F := by
    refine le_trans (formulaLen_instOuter_le hE es hc₂ hes) (le_trans ?_ hcF)
    rw [formulaLen_and hc₁.isUFormula hc₂.isUFormula]
    exact mul_le_mul_of_nonneg_right (le_trans le_add_self le_self_add) zero_le
  have hsplit : DerivationOf T (splitAndCode L Γ (instOuter L es c₁) (instOuter L es c₂) d)
      (insert (neg L (instOuter L es (c₁ ^⋏ c₂))) Γ) := by
    rw [instOuter_and es hc₁ hc₂ hes₁]
    exact splitAndCode_proof hc₁' hc₂' hΓ hsub hd
  have hsl := dlen_splitAndCode_le (T := T) hc₁' hc₂' hΓ hsub hd
  have hsl' : dlen T (splitAndCode L Γ (instOuter L es c₁) (instOuter L es c₂) d) ≤
      dlen T d + 2 * setLen L Γ + 6 * F + 4 := by
    refine le_trans hsl ?_
    calc dlen T d + 2 * setLen L Γ + 3 * formulaLen L (instOuter L es c₁) + 3 * formulaLen L (instOuter L es c₂) + 4
        ≤ dlen T d + 2 * setLen L Γ + 3 * F + 3 * F + 4 := by gcongr
      _ = dlen T d + 2 * setLen L Γ + 6 * F + 4 := by ring
  unfold useHornAndCode
  refine le_trans (dlen_useHornCode_le hE has hc hes hΓ (subset_refl Γ) hneg hΛ hsplit hF) ?_
  gcongr

/-! ### Step 3 — `introFactCode`: a totality row, the witness as a fresh eigenvariable -/

variable (L) in
/-- **Introduce a fact by a totality row** `∀^m (A₁ → … → A_j → ∃ z, R)`: use the row in the
context extended by `∃ R[ē]` (its continuation is the one-node `axL` on `∃ R[ē]`), then
eliminate the existential (`elimExistsCode`) — the continuation `d` sees `R[ē](&0)` as
`insert (neg (free (instOuterAt 1 es R))) (setShift Γ)`. -/
noncomputable def introFactCode (Γ : V) (es as : List V) (R dΛ d : V) : V :=
  elimExistsCode L Γ (instOuterAt L 1 es R)
    (useHornCode L (insert (^∃ (instOuterAt L 1 es R)) Γ) es as (^∃ R) dΛ
      (axL (insert (neg L (^∃ (instOuterAt L 1 es R))) (insert (^∃ (instOuterAt L 1 es R)) Γ))
        (^∃ (instOuterAt L 1 es R))))
    d

/-- The Horn part of `introFactCode` derives `insert (∃ R[ē]) Γ`. -/
theorem introFactCode_horn_proof {Γ : V} {es as : List V} {R dΛ : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a)
    (hR : IsSemiformula L ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsTerm L e) (hΓ : IsFormulaSet L Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as (^∃ R)))) :
    DerivationOf T
      (useHornCode L (insert (^∃ (instOuterAt L 1 es R)) Γ) es as (^∃ R) dΛ
        (axL (insert (neg L (^∃ (instOuterAt L 1 es R))) (insert (^∃ (instOuterAt L 1 es R)) Γ))
          (^∃ (instOuterAt L 1 es R))))
      (insert (^∃ (instOuterAt L 1 es R)) Γ) := by
  have hP : IsSemiformula L 1 (instOuterAt L 1 es R) := isSemiformula_one_instOuterAt es hR hes
  have hE : IsFormula L (^∃ (instOuterAt L 1 es R)) := by simp [hP]
  have hΓ₁ : IsFormulaSet L (insert (^∃ (instOuterAt L 1 es R)) Γ) := by simp [hE, hΓ]
  refine useHornCode_proof has (by simp [hR]) hes hΓ₁ (subset_refl _)
    (fun a ha ↦ by simp [hneg a ha]) hΛ ?_
  rw [instOuter_exs es hR hes]
  exact ⟨by simp, Derivation.axL (by simp [hE, hΓ₁]) (by simp) (by simp)⟩

theorem introFactCode_proof {Γ : V} {es as : List V} {R dΛ d : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a)
    (hR : IsSemiformula L ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsTerm L e) (hΓ : IsFormulaSet L Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as (^∃ R))))
    (hd : DerivationOf T d (insert (neg L (free L (instOuterAt L 1 es R))) (setShift L Γ))) :
    DerivationOf T (introFactCode L Γ es as R dΛ d) Γ :=
  elimExistsCode_proof (isSemiformula_one_instOuterAt es hR hes) hΓ (subset_refl Γ)
    (introFactCode_horn_proof has hR hes hΓ hneg hΛ) hd

/-- **The bound for `introFactCode`** (`m = es.length`, `j = as.length`, `E ≥ 1`,
`F ≥ |A₁ → … → ∃ R|·E`, so `|∃ R[ē]| ≤ F`):
`dlen ≤ dlen dΛ + dlen d + (m + 2j + 10)·|Γ| + (m + 11)·F + (m + 1)²·(F + m) + |B| + m·E + 2m
  + (2j + 1)·((j + 2)·F + 1) + 12`. -/
theorem dlen_introFactCode_le {E F : V} (hE : 1 ≤ E) {Γ : V} {es as : List V} {R dΛ d : V}
    (has : ∀ a ∈ as, IsSemiformula L (es.length : V) a)
    (hR : IsSemiformula L ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsTerm L e ∧ termLen L e ≤ E) (hΓ : IsFormulaSet L Γ)
    (hneg : ∀ a ∈ as, neg L (instOuter L es a) ∈ Γ)
    (hΛ : Proof T dΛ (allsIter es.length (impChain L as (^∃ R))))
    (hd : DerivationOf T d (insert (neg L (free L (instOuterAt L 1 es R))) (setShift L Γ)))
    (hF : formulaLen L (impChain L as (^∃ R)) * E ≤ F) :
    dlen T (introFactCode L Γ es as R dΛ d) ≤
      dlen T dΛ + dlen T d + ((es.length : V) + 2 * (as.length : V) + 10) * setLen L Γ
        + ((es.length : V) + 11) * F
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + formulaLen L (impChain L as (^∃ R)) + (es.length : V) * E + 2 * (es.length : V)
        + (2 * (as.length : V) + 1) * (((as.length : V) + 2) * F + 1) + 12 := by
  have hes₁ : ∀ e ∈ es, IsTerm L e := fun e he ↦ (hes e he).1
  have hP : IsSemiformula L 1 (instOuterAt L 1 es R) := isSemiformula_one_instOuterAt es hR hes₁
  have hEx : IsFormula L (^∃ (instOuterAt L 1 es R)) := by simp [hP]
  have hΓ₁ : IsFormulaSet L (insert (^∃ (instOuterAt L 1 es R)) Γ) := by simp [hEx, hΓ]
  have hc : IsSemiformula L (es.length : V) (^∃ R) := by simp [hR]
  have hB : IsSemiformula L (es.length : V) (impChain L as (^∃ R)) := isSemiformula_impChain has hc
  -- `|∃ R[ē]| ≤ F`, hence `|R[ē]| ≤ F`
  have hExF : formulaLen L (^∃ (instOuterAt L 1 es R)) ≤ F := by
    rw [← instOuter_exs es hR hes₁]
    refine le_trans (formulaLen_instOuter_le hE es hc hes) (le_trans ?_ hF)
    exact mul_le_mul_of_nonneg_right (formulaLen_concl_le_impChain has hc) zero_le
  have hRF : formulaLen L (instOuterAt L 1 es R) ≤ F := by
    rw [formulaLen_exs hP.isUFormula] at hExF
    exact le_trans le_self_add hExF
  have hΓ₁F : setLen L (insert (^∃ (instOuterAt L 1 es R)) Γ) ≤ setLen L Γ + F :=
    le_trans (setLen_insert_le _ _) (add_le_add (le_refl _) hExF)
  -- the one-node continuation
  have hax : DerivationOf T
      (axL (insert (neg L (^∃ (instOuterAt L 1 es R))) (insert (^∃ (instOuterAt L 1 es R)) Γ))
        (^∃ (instOuterAt L 1 es R)))
      (insert (neg L (instOuter L es (^∃ R))) (insert (^∃ (instOuterAt L 1 es R)) Γ)) := by
    rw [instOuter_exs es hR hes₁]
    exact ⟨by simp, Derivation.axL (by simp [hEx, hΓ₁]) (by simp) (by simp)⟩
  have haxlen : dlen T (axL (insert (neg L (^∃ (instOuterAt L 1 es R))) (insert (^∃ (instOuterAt L 1 es R)) Γ))
        (^∃ (instOuterAt L 1 es R))) ≤ setLen L Γ + 2 * F + 1 := by
    rw [dlen_eq_of_graph hax.2 (DlenGraph.axL_iff.mpr rfl)]
    have : setLen L (insert (neg L (^∃ (instOuterAt L 1 es R))) (insert (^∃ (instOuterAt L 1 es R)) Γ))
        ≤ setLen L Γ + F + F := by
      refine le_trans (setLen_insert_le _ _) (add_le_add hΓ₁F ?_)
      rw [formulaLen_neg hEx.isUFormula]; exact hExF
    calc _ ≤ setLen L Γ + F + F + 1 := by gcongr
      _ = setLen L Γ + 2 * F + 1 := by ring
  have hhorn := dlen_useHornCode_le (T := T) hE has hc hes hΓ₁ (subset_refl _)
    (fun a ha ↦ by simp [hneg a ha]) hΛ hax hF
  have hD := introFactCode_horn_proof (T := T) has hR hes₁ hΓ hneg hΛ
  have hhorn' : dlen T (useHornCode L (insert (^∃ (instOuterAt L 1 es R)) Γ) es as (^∃ R) dΛ
        (axL (insert (neg L (^∃ (instOuterAt L 1 es R))) (insert (^∃ (instOuterAt L 1 es R)) Γ))
          (^∃ (instOuterAt L 1 es R)))) ≤
      dlen T dΛ + (setLen L Γ + 2 * F + 1) + ((es.length : V) + 3) * (setLen L Γ + F)
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + formulaLen L (impChain L as (^∃ R)) + (es.length : V) * E + 2 * (es.length : V) + 3
        + (2 * (as.length : V) + 1) * ((setLen L Γ + F) + ((as.length : V) + 1) * F + 1) := by
    refine le_trans hhorn ?_
    gcongr
  unfold introFactCode
  refine le_trans (dlen_elimExistsCode_le' hP hΓ (subset_refl Γ) hD hd) ?_
  calc _ ≤ (dlen T dΛ + (setLen L Γ + 2 * F + 1) + ((es.length : V) + 3) * (setLen L Γ + F)
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (F + (es.length : V))
        + formulaLen L (impChain L as (^∃ R)) + (es.length : V) * E + 2 * (es.length : V) + 3
        + (2 * (as.length : V) + 1) * ((setLen L Γ + F) + ((as.length : V) + 1) * F + 1))
        + dlen T d + 5 * setLen L Γ + 6 * F + 8 := by gcongr
    _ = _ := by ring

/-! ### Leaves — `axLFactCode`, `wkToCode` -/

/-- Derive `insert φ Γ` from `neg φ ∈ Γ`: one `axL`. -/
noncomputable def axLFactCode (Γ φ : V) : V := axL (insert φ Γ) φ

theorem axLFactCode_proof {Γ φ : V} (hφ : IsFormula L φ) (hΓ : IsFormulaSet L Γ) (h : neg L φ ∈ Γ) :
    DerivationOf T (axLFactCode Γ φ) (insert φ Γ) :=
  ⟨by simp [axLFactCode], Derivation.axL (by simp [hφ, hΓ]) (by simp) (by simp [h])⟩

theorem dlen_axLFactCode {Γ φ : V} (hφ : IsFormula L φ) (hΓ : IsFormulaSet L Γ) (h : neg L φ ∈ Γ) :
    dlen T (axLFactCode Γ φ) = setLen L (insert φ Γ) + 1 :=
  dlen_eq_of_graph (axLFactCode_proof hφ hΓ h).2 (DlenGraph.axL_iff.mpr rfl)

theorem dlen_axLFactCode_le {Γ φ : V} (hφ : IsFormula L φ) (hΓ : IsFormulaSet L Γ) (h : neg L φ ∈ Γ) :
    dlen T (axLFactCode Γ φ) ≤ setLen L Γ + formulaLen L φ + 1 := by
  rw [dlen_axLFactCode hφ hΓ h]
  exact add_le_add (setLen_insert_le _ _) (le_refl _)

/-- Weaken a derivation of `Γ' ⊆ Γ` to `Γ`: one `wkRule`. -/
noncomputable def wkToCode (Γ d : V) : V := wkRule Γ d

theorem wkToCode_proof {Γ Γ' d : V} (hΓ : IsFormulaSet L Γ) (h : Γ' ⊆ Γ)
    (hd : DerivationOf T d Γ') : DerivationOf T (wkToCode Γ d) Γ :=
  ⟨by simp [wkToCode], Derivation.wkRule hΓ h hd⟩

theorem dlen_wkToCode {Γ Γ' d : V} (hΓ : IsFormulaSet L Γ) (h : Γ' ⊆ Γ)
    (hd : DerivationOf T d Γ') : dlen T (wkToCode Γ d) = setLen L Γ + dlen T d + 1 :=
  dlen_eq_of_graph (wkToCode_proof hΓ h hd).2 (DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩)

theorem dlen_wkToCode_le {Γ Γ' d : V} (hΓ : IsFormulaSet L Γ) (h : Γ' ⊆ Γ)
    (hd : DerivationOf T d Γ') : dlen T (wkToCode Γ d) ≤ dlen T d + setLen L Γ + 1 := by
  rw [dlen_wkToCode hΓ h hd, add_comm (setLen L Γ)]

end steps

end ArithS
