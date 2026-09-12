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
8. **Canonical fact codes and the identification theorem.** A fact about a Δ₁/Σ₀ predicate
   `P` (a quoted `ℒₒᵣ`-semisentence, e.g. `Ppi = ⌜lMap emb (isSemiformula LAct).pi⌝`) at witnesses
   `w₀ … w_{k-1}` is stored as `subst ?[w₀, …, w_{k-1}] P` (`listToVec`; the predicate's OWN
   variable order — `piFact n a`, `sigmaFact n a`, `andFact z a b`). A row's antecedent
   `P/[#i, #j]` (the DSL's `!P xᵢ xⱼ`) instantiated at the witnesses IS such a code:
   `instOuterAt_subst` — `instOuterAt k es (subst W P) = subst (W ∘ ?[#0, …, #(k-1), e_m, …, e₁]) P`
   (one simultaneous substitution; entries of `qVecIter n (e ∷ 0)` are `?[#0, …, #(n-1), e]`,
   `qVecIter_single`) — so `instOuter_subst_bv2`/`_bv3` reduce every row piece to
   `subst ?[es.reverse[i], es.reverse[j]] P` and the fragment matches facts SYNTACTICALLY, never by
   evaluating a code. Row bodies are read off the DSL by `rfl` (`quote_isSemiformulaAndB`, …:
   `⌜lMap emb (φ ⇜ v)⌝ = subst ⌜v⌝ ⌜lMap emb φ⌝`, `quote_lMap_emb_subst`) and `shift` fixes a
   quoted sentence (`shift_quote_sentence`), so a fact `subst ?[w] P` shifts to
   `subst ?[shift w] P` (`shift_subst_listToVec`) and the freed existential body
   `subst ?[#0, w] P` becomes `subst ?[&0, shift w] P` (`free_subst_listToVec`).

The smoke test `describeAndCode` (bottom of the file) runs the protocol end to end: from
`IsFormula a`, `IsFormula b` in context (`.pi` reading, `neg (piFact nc a) ∈ Γ`), get `z = a ⋏ b`
at the fresh `z = &0` (`lib_qqAndTotal`, `introFactCode`, context shifted: `ctx1`), then
`IsFormula z` in the `.sigma` reading (`lib_isSemiformulaAnd`, `useHornCode`, `ctx2`), then in
the `.pi` reading (`lib_isSemiformulaSigmaPi`, `useHornCode`, `ctx3`), and hand the continuation
`ctx3`; `describeAndCode_proof`, and `dlen_describeAndCode_le`:
`dlen ≤ dlen d + N₁ + N₂ + N₃ + 56|Γ| + (68|B₁| + 61|B₂| + 15|B₃| + 8)·E + |B₁| + |B₂| + |B₃| + 181`
with `E ≥ 1, 2|a|, 2|b|, 2|nc|` (the witness bound — `nc` is the arity witness, `E` absorbs the
shift's doubling), `Nᵢ ≥ dlen dΛᵢ` the stored-proof lengths and `|Bᵢ|` the row bodies' lengths;
`describeAndCode_exists` packages the rows through `Lib.univ_code` (one standard `N`, every model).

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

/-! ### The entries of `qVecIter n (e ∷ 0)`: `?[#0, …, #(n-1), e]` -/

/-- `bvarChain j n e = ?[#j, #(j+1), …, #(j+n-1), e]`. -/
noncomputable def bvarChain : ℕ → ℕ → V → V
  | _, 0, e => e ∷ 0
  | j, n + 1, e => ^#((j : ℕ) : V) ∷ bvarChain (j + 1) n e

@[simp] lemma bvarChain_zero (j : ℕ) (e : V) : bvarChain j 0 e = e ∷ 0 := rfl
@[simp] lemma bvarChain_succ (j n : ℕ) (e : V) :
    bvarChain j (n + 1) e = ^#((j : ℕ) : V) ∷ bvarChain (j + 1) n e := rfl

lemma len_bvarChain (e : V) : ∀ (j n : ℕ), len (bvarChain j n e) = ((n + 1 : ℕ) : V)
  | _, 0 => by simp
  | j, n + 1 => by rw [bvarChain_succ, len_adjoin, len_bvarChain e (j + 1) n]; push_cast; ring

lemma isUTermVec_bvarChain {e : V} (he : IsUTerm L e) : ∀ (j n : ℕ),
    IsUTermVec L ((n + 1 : ℕ) : V) (bvarChain j n e)
  | _, 0 => by simp [he]
  | j, n + 1 => by
    rw [bvarChain_succ, Nat.cast_succ]
    exact IsUTermVec.adjoin (isUTermVec_bvarChain he (j + 1) n) (by simp)

lemma termBShiftVec_bvarChain {e : V} (he : IsSemiterm L 0 e) : ∀ (j n : ℕ),
    termBShiftVec L ((n + 1 : ℕ) : V) (bvarChain j n e) = bvarChain (j + 1) n e
  | _, 0 => by
    simp only [bvarChain_zero, Nat.zero_add, Nat.cast_one]
    rw [termBShiftVec_cons₁ he.isUTerm, termBShift_eq_self_of_closed he]
  | j, n + 1 => by
    rw [bvarChain_succ, bvarChain_succ, Nat.cast_succ,
      termBShiftVec_cons (by simp) (isUTermVec_bvarChain he.isUTerm (j + 1) n), termBShift_bvar,
      termBShiftVec_bvarChain he (j + 1) n, Nat.cast_succ]

lemma qVec_bvarChain {e : V} (he : IsSemiterm L 0 e) (n : ℕ) :
    qVec L (bvarChain 0 n e) = bvarChain 0 (n + 1) e := by
  rw [qVec, len_bvarChain, termBShiftVec_bvarChain he 0 n, bvarChain_succ, Nat.cast_zero]

/-- `qVecIter n (e ∷ 0) = ?[#0, …, #(n-1), e]`. -/
lemma qVecIter_single {e : V} (he : IsSemiterm L 0 e) : ∀ n : ℕ,
    qVecIter L n (e ∷ (0 : V)) = bvarChain 0 n e
  | 0 => rfl
  | n + 1 => by rw [qVecIter_succ, qVecIter_qVec, qVecIter_single he n, qVec_bvarChain he n]

lemma nth_bvarChain_lt (e : V) : ∀ (j n i : ℕ), i < n →
    (bvarChain j n e).[((i : ℕ) : V)] = ^#((j + i : ℕ) : V)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | j, n + 1, 0, _ => by simp
  | j, n + 1, i + 1, h => by
    rw [bvarChain_succ, Nat.cast_succ, nth_adjoin_succ, nth_bvarChain_lt e (j + 1) n i (by omega),
      show j + 1 + i = j + (i + 1) by omega]

lemma nth_bvarChain_last (e : V) : ∀ (j n : ℕ), (bvarChain j n e).[((n : ℕ) : V)] = e
  | _, 0 => by simp
  | j, n + 1 => by rw [bvarChain_succ, Nat.cast_succ, nth_adjoin_succ, nth_bvarChain_last e (j + 1) n]

/-- The substitution `subOuter n e` sends `#i` (`i < n`) to itself … -/
lemma termSubst_qVecIter_bvar_lt {e : V} (he : IsSemiterm L 0 e) {n i : ℕ} (h : i < n) :
    termSubst L (qVecIter L n (e ∷ (0 : V))) (^#((i : ℕ) : V)) = ^#((i : ℕ) : V) := by
  rw [termSubst_bvar, qVecIter_single he, nth_bvarChain_lt e 0 n i h, Nat.zero_add]

/-- … and `#n` to `e`. -/
lemma termSubst_qVecIter_bvar_eq {e : V} (he : IsSemiterm L 0 e) (n : ℕ) :
    termSubst L (qVecIter L n (e ∷ (0 : V))) (^#((n : ℕ) : V)) = e := by
  rw [termSubst_bvar, qVecIter_single he, nth_bvarChain_last]

/-- `subOuter n e (subst W P) = subst (W[#n := e]) P`. -/
lemma subOuter_subst {n : ℕ} {k P W e : V} (hP : IsSemiformula L k P)
    (hW : IsSemitermVec L k ((n : V) + 1) W) (he : IsTerm L e) :
    subOuter L n e (subst L W P) = subst L (termSubstVec L k (qVecIter L n (e ∷ (0 : V))) W) P := by
  unfold subOuter
  exact substs_substs hP (isSemitermVec_qVecIter_single he) hW

lemma isSemitermVec_natCast_cons_iff {k : ℕ} {n t w : V} :
    IsSemitermVec L ((k + 1 : ℕ) : V) n (t ∷ w) ↔ IsSemiterm L n t ∧ IsSemitermVec L (k : V) n w := by
  rw [Nat.cast_succ, IsSemitermVec.cons_iff]

lemma termSubstVec_natCast_cons {k : ℕ} {w t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L (k : V) ts) :
    termSubstVec L ((k + 1 : ℕ) : V) w (t ∷ ts) = termSubst L w t ∷ termSubstVec L (k : V) w ts := by
  rw [Nat.cast_succ, termSubstVec_cons ht hts]


/-! ### Level monotonicity, standard indices, `listToVec` -/

lemma isSemiterm_of_le {n m t : V} (h : IsSemiterm L n t) (hnm : n ≤ m) : IsSemiterm L m t :=
  IsSemiterm.def.mpr ⟨(IsSemiterm.def.mp h).1, le_trans (IsSemiterm.def.mp h).2 hnm⟩

lemma isSemitermVec_of_le {k n m v : V} (h : IsSemitermVec L k n v) (hnm : n ≤ m) :
    IsSemitermVec L k m v :=
  IsSemitermVec.iff.mpr ⟨h.lh, fun _ hi ↦ isSemiterm_of_le (h.nth hi) hnm⟩

/-- Elements below a standard numeral are standard. -/
lemma exists_natCast_of_lt_natCast : ∀ (n : ℕ) (i : V), i < (n : V) → ∃ i' : ℕ, i = (i' : V) ∧ i' < n
  | 0, i, hi => absurd hi (by simp)
  | n + 1, i, hi => by
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · exact ⟨0, by simp, Nat.succ_pos n⟩
    · rw [Nat.cast_succ] at hi
      obtain ⟨i', rfl, h⟩ := exists_natCast_of_lt_natCast n i (lt_of_add_lt_add_right hi)
      exact ⟨i' + 1, by rw [Nat.cast_succ], by omega⟩

/-- An HFS vector from a list. -/
noncomputable def listToVec : List V → V
  | [] => 0
  | x :: xs => x ∷ listToVec xs

@[simp] lemma listToVec_nil : listToVec ([] : List V) = 0 := rfl
@[simp] lemma listToVec_cons (x : V) (xs : List V) : listToVec (x :: xs) = x ∷ listToVec xs := rfl

lemma len_listToVec : ∀ l : List V, len (listToVec l) = (l.length : V)
  | [] => by simp
  | x :: xs => by rw [listToVec_cons, len_adjoin, len_listToVec xs, List.length_cons, Nat.cast_succ]

lemma isSemitermVec_listToVec {n : V} : ∀ (l : List V), (∀ x ∈ l, IsSemiterm L n x) →
    IsSemitermVec L (l.length : V) n (listToVec l)
  | [], _ => by simp
  | x :: xs, h => by
    rw [listToVec_cons, List.length_cons, Nat.cast_succ, IsSemitermVec.cons_iff]
    exact ⟨h x (by simp), isSemitermVec_listToVec xs (fun y hy ↦ h y (by simp [hy]))⟩

lemma nth_listToVec : ∀ (l : List V) (i : ℕ), (listToVec l).[(i : V)] = l.getD i 0
  | [], i => by simp
  | x :: xs, 0 => by simp
  | x :: xs, i + 1 => by rw [listToVec_cons, Nat.cast_succ, nth_adjoin_succ, nth_listToVec xs i]; rfl

/-- The list `[#0, …, #(k-1)]` of bound-variable codes. -/
noncomputable def bvarList (k : ℕ) : List V := (List.range k).map fun i ↦ ^#((i : ℕ) : V)

@[simp] lemma length_bvarList (k : ℕ) : (bvarList (V := V) k).length = k := by simp [bvarList]

lemma getD_bvarList {k i : ℕ} (h : i < k) : (bvarList (V := V) k).getD i 0 = ^#((i : ℕ) : V) := by
  simp [bvarList, List.getD_eq_getElem?_getD, h]

/-! ### The instantiation theorem: `instOuterAt k es (subst W P) = subst (W ∘ [#0…#(k-1), e_m … e₁]) P` -/

/-- `termSubstVec` composes (the vector form of `termSubst_termSubst`). -/
lemma termSubstVec_termSubstVec {l n m w v W : V} (hv : IsSemitermVec L n m v)
    (hW : IsSemitermVec L l n W) :
    termSubstVec L l w (termSubstVec L l v W) = termSubstVec L l (termSubstVec L n w v) W := by
  apply nth_ext' l (len_termSubstVec (hv.termSubstVec hW).isUTerm) (len_termSubstVec hW.isUTerm)
  intro i hi
  rw [nth_termSubstVec (hv.termSubstVec hW).isUTerm hi, nth_termSubstVec hW.isUTerm hi,
    nth_termSubstVec hW.isUTerm hi, termSubst_termSubst hv (hW.nth hi)]

/-- Substituting `?[l₀, …, l_{n-1}]` into `?[#0, …, #(n-1), e]` gives `?[l₀, …, l_{n-1}, e]`. -/
lemma termSubstVec_listToVec_qVecIter {e : V} (he : IsSemiterm L 0 e) (n : ℕ) (l : List V)
    (hl : l.length = n) :
    termSubstVec L ((n : V) + 1) (listToVec l) (qVecIter L n (e ∷ (0 : V))) = listToVec (l ++ [e]) := by
  have hq : IsSemitermVec L ((n : V) + 1) (n : V) (qVecIter L n (e ∷ (0 : V))) :=
    isSemitermVec_qVecIter_single he
  apply nth_ext' ((n : V) + 1) (len_termSubstVec hq.isUTerm)
    (by rw [len_listToVec, List.length_append, List.length_singleton, hl, Nat.cast_succ])
  intro i hi
  rw [nth_termSubstVec hq.isUTerm hi, qVecIter_single he]
  rw [← Nat.cast_succ] at hi
  obtain ⟨i', rfl, hi'⟩ := exists_natCast_of_lt_natCast (n + 1) i hi
  rw [nth_listToVec]
  rcases Nat.lt_or_ge i' n with h | h
  · rw [nth_bvarChain_lt e 0 n i' h, Nat.zero_add, termSubst_bvar, nth_listToVec,
      List.getD_append _ _ _ _ (by omega)]
  · have : i' = n := by omega
    subst this
    rw [nth_bvarChain_last, termSubst_eq_self_of_closed he,
      List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
    rfl

/-- The identity substitution `?[#0, …, #(k-1)]` fixes a `k`-level vector. -/
lemma termSubstVec_bvarList {k : ℕ} {l W : V} (hW : IsSemitermVec L l (k : V) W) :
    termSubstVec L l (listToVec (bvarList k)) W = W := by
  apply nth_ext' l (len_termSubstVec hW.isUTerm) hW.lh
  intro i hi
  rw [nth_termSubstVec hW.isUTerm hi]
  apply termSubst_eq_self (hW.nth hi)
  intro j hj
  obtain ⟨j', rfl, hj'⟩ := exists_natCast_of_lt_natCast k j hj
  rw [nth_listToVec, getD_bvarList hj']

/-- **The instantiation theorem.** `instOuterAt k es` acting on `subst W P` is the single
substitution by the vector `?[#0, …, #(k-1), e_m, …, e₁]` composed with `W`. -/
theorem instOuterAt_subst (k : ℕ) : ∀ (es : List V) {l P W : V}, IsSemiformula L l P →
    IsSemitermVec L l ((es.length + k : ℕ) : V) W → (∀ e ∈ es, IsSemiterm L 0 e) →
    instOuterAt L k es (subst L W P) =
      subst L (termSubstVec L l (listToVec (bvarList k ++ es.reverse)) W) P
  | [], l, P, W, hP, hW, _ => by
    rw [instOuterAt_nil, List.reverse_nil, List.append_nil, termSubstVec_bvarList (by simpa using hW)]
  | e :: es, l, P, W, hP, hW, hes => by
    have he : IsSemiterm L 0 e := hes e (by simp)
    have hW' : IsSemitermVec L l (((es.length + k : ℕ) : V) + 1) W := by
      rw [show ((es.length + k : ℕ) : V) + 1 = (((e :: es).length + k : ℕ) : V) by
        simp only [List.length_cons]; push_cast; ring]
      exact hW
    have hq : IsSemitermVec L (((es.length + k : ℕ) : V) + 1) ((es.length + k : ℕ) : V)
        (qVecIter L (es.length + k) (e ∷ (0 : V))) := isSemitermVec_qVecIter_single he
    rw [instOuterAt_cons, subOuter_subst hP hW' he,
      instOuterAt_subst k es hP (hq.termSubstVec hW') (fun e' he' ↦ hes e' (by simp [he'])),
      termSubstVec_termSubstVec hq hW', List.reverse_cons, ← List.append_assoc,
      termSubstVec_listToVec_qVecIter he (es.length + k) _ (by simp; omega)]

theorem instOuter_subst (es : List V) {l P W : V} (hP : IsSemiformula L l P)
    (hW : IsSemitermVec L l (es.length : V) W) (hes : ∀ e ∈ es, IsSemiterm L 0 e) :
    instOuter L es (subst L W P) = subst L (termSubstVec L l (listToVec es.reverse) W) P := by
  rw [← instOuterAt_zero, instOuterAt_subst 0 es hP (by simpa using hW) hes]
  rfl

/-! ### `termSubstVec`/`termShiftVec` on `listToVec`; `shift` and `free` of substituted closed codes -/

lemma isUTermVec_listToVec : ∀ (l : List V), (∀ x ∈ l, IsUTerm L x) →
    IsUTermVec L (l.length : V) (listToVec l)
  | [], _ => by simp
  | x :: xs, h => by
    rw [listToVec_cons, List.length_cons, Nat.cast_succ]
    exact IsUTermVec.adjoin (isUTermVec_listToVec xs (fun y hy ↦ h y (by simp [hy]))) (h x (by simp))

lemma termSubstVec_listToVec (w : V) : ∀ (l : List V), (∀ x ∈ l, IsUTerm L x) →
    termSubstVec L (l.length : V) w (listToVec l) = listToVec (l.map (termSubst L w))
  | [], _ => by simp
  | x :: xs, h => by
    rw [listToVec_cons, List.length_cons, termSubstVec_natCast_cons (h x (by simp))
      (isUTermVec_listToVec xs (fun y hy ↦ h y (by simp [hy]))),
      termSubstVec_listToVec w xs (fun y hy ↦ h y (by simp [hy])), List.map_cons, listToVec_cons]

lemma termShiftVec_natCast_cons {k : ℕ} {t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L (k : V) ts) :
    termShiftVec L ((k + 1 : ℕ) : V) (t ∷ ts) = termShift L t ∷ termShiftVec L (k : V) ts := by
  rw [Nat.cast_succ, termShiftVec_cons ht hts]

lemma termShiftVec_listToVec : ∀ (l : List V), (∀ x ∈ l, IsUTerm L x) →
    termShiftVec L (l.length : V) (listToVec l) = listToVec (l.map (termShift L))
  | [], _ => by simp
  | x :: xs, h => by
    rw [listToVec_cons, List.length_cons, termShiftVec_natCast_cons (h x (by simp))
      (isUTermVec_listToVec xs (fun y hy ↦ h y (by simp [hy]))),
      termShiftVec_listToVec xs (fun y hy ↦ h y (by simp [hy])), List.map_cons, listToVec_cons]

/-- `shift (subst ?[l] P) = subst ?[shift l] P` when `shift P = P` (a quoted sentence code). -/
lemma shift_subst_listToVec {P : V} (l : List V) (hP : IsSemiformula L (l.length : V) P)
    (hP0 : shift L P = P) {n : V} (hl : ∀ x ∈ l, IsSemiterm L n x) :
    shift L (subst L (listToVec l) P) = subst L (listToVec (l.map (termShift L))) P := by
  rw [shift_substs hP (isSemitermVec_listToVec l hl), hP0,
    termShiftVec_listToVec l (fun x hx ↦ (hl x hx).isUTerm)]

/-- `free (subst ?[#0, l] P) = subst ?[&0, shift l] P` for closed `l` and `shift P = P`. -/
lemma free_subst_listToVec {P : V} (l : List V) (hP : IsSemiformula L ((l.length + 1 : ℕ) : V) P)
    (hP0 : shift L P = P) (hl : ∀ x ∈ l, IsSemiterm L 0 x) :
    free L (subst L (listToVec (^#0 :: l)) P) =
      subst L (listToVec (^&0 :: l.map (termShift L))) P := by
  have hl1 : ∀ x ∈ (^#0 :: l), IsSemiterm L 1 x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact isSemiterm_of_le (hl x hx) (by simp)
  have hl1' : ∀ x ∈ (^#0 :: l.map (termShift L)), IsSemiterm L 1 x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact isSemiterm_of_le (hl y hy).termShift (by simp)
  have hP' : IsSemiformula L (((^#0 :: l).length : ℕ) : V) P := by simpa using hP
  unfold free substs1
  rw [shift_subst_listToVec (^#0 :: l) hP' hP0 hl1, List.map_cons, termShift_bvar]
  have hW : IsSemitermVec L (((^#0 :: l.map (termShift L)).length : ℕ) : V) 1
      (listToVec (^#0 :: l.map (termShift L))) := isSemitermVec_listToVec _ hl1'
  have hP'' : IsSemiformula L (((^#0 :: l.map (termShift L)).length : ℕ) : V) P := by simpa using hP
  rw [substs_substs hP'' (by simp : IsSemitermVec (V := V) L 1 0 (^&0 ∷ 0)) hW,
    termSubstVec_listToVec _ _ (fun x hx ↦ (hl1' x hx).isUTerm), List.map_cons, termSubst_bvar,
    nth_adjoin_zero, List.map_map]
  congr 3
  apply List.map_congr_left
  intro x hx
  exact termSubst_eq_self_of_closed (hl x hx).termShift

/-! ### Quote bridges for `ℒₒᵣ`-semisentences embedded into `LAct` -/

section quotes
open LAct

/-- The code of an embedded substitution instance `φ ⇜ v` is the code of `φ` under the codes
of the terms. -/
lemma quote_lMap_emb_subst {k m : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → ClosedSemiterm ℒₒᵣ m) :
    (⌜Semiformula.lMap emb (φ ⇜ v)⌝ : V) =
      subst LAct (SemitermVec.val fun i ↦
          (⌜(↑(Semiterm.lMap emb (v i)) : SyntacticSemiterm LAct m)⌝ : Bootstrapping.Semiterm V LAct m))
        ⌜Semiformula.lMap emb φ⌝ := by
  rw [Semiformula.lMap_subst, Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  rfl

lemma shift_emb_semisentence {L : Language} {n : ℕ} (σ : Semisentence L n) :
    Rewriting.shift (Rewriting.emb σ : Semiproposition L n) = Rewriting.emb σ := by
  show Rew.shift ▹ (Rew.emb ▹ σ) = Rew.emb ▹ σ
  rw [← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

/-- `shift` fixes the code of a sentence (no free variables). -/
lemma shift_quote_sentence {n : ℕ} (σ : Semisentence LAct n) : shift LAct (⌜σ⌝ : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, ← Semiformula.quote_shift, shift_emb_semisentence]

lemma quote_lMap_emb_imp {n : ℕ} (φ ψ : ArithmeticSemisentence n) :
    (⌜Semiformula.lMap emb (φ 🡒 ψ)⌝ : V) =
      Bootstrapping.imp LAct ⌜Semiformula.lMap emb φ⌝ ⌜Semiformula.lMap emb ψ⌝ := by
  rw [LogicalConnective.HomClass.map_imply, quote_imp_sentence_V]

lemma quote_lMap_emb_ex {n : ℕ} (φ : ArithmeticSemisentence (n + 1)) :
    (⌜Semiformula.lMap emb (∃¹ φ)⌝ : V) = ^∃ ⌜Semiformula.lMap emb φ⌝ := by
  rw [Semiformula.lMap_exs]
  simp [Sentence.quote_def]

end quotes

/-! ### The smoke test: `describeAndCode` -/

section smoke
open LAct

/-- The bound-variable code `#i`, `i` standard. -/
noncomputable abbrev bv (i : ℕ) : V := ^#((i : ℕ) : V)

/-- The codes of the three predicates the smoke test speaks about. -/
noncomputable def Ppi : V :=
  ⌜Semiformula.lMap emb (↑(isSemiformula LAct).pi : ArithmeticSemisentence 2)⌝
noncomputable def Psigma : V :=
  ⌜Semiformula.lMap emb (↑(isSemiformula LAct).sigma : ArithmeticSemisentence 2)⌝
noncomputable def Pand : V := ⌜Semiformula.lMap emb (↑qqAndDef : ArithmeticSemisentence 3)⌝

lemma isSemiformula_Ppi : IsSemiformula LAct ((2 : ℕ) : V) Ppi := Sentence.quote_isSemiformula _
lemma isSemiformula_Psigma : IsSemiformula LAct ((2 : ℕ) : V) Psigma := Sentence.quote_isSemiformula _
lemma isSemiformula_Pand : IsSemiformula LAct ((3 : ℕ) : V) Pand := Sentence.quote_isSemiformula _
lemma shift_Ppi : shift LAct (Ppi : V) = Ppi := shift_quote_sentence _
lemma shift_Psigma : shift LAct (Psigma : V) = Psigma := shift_quote_sentence _
lemma shift_Pand : shift LAct (Pand : V) = Pand := shift_quote_sentence _

/-- **Canonical fact codes**: the predicate's code substituted at the witnesses in ITS variable
order (`!(isSemiformula LAct).pi n p`, `!qqAndDef r p q`). -/
noncomputable def piFact (n a : V) : V := subst LAct (listToVec [n, a]) Ppi
noncomputable def sigmaFact (n a : V) : V := subst LAct (listToVec [n, a]) Psigma
noncomputable def andFact (z a b : V) : V := subst LAct (listToVec [z, a, b]) Pand

/-- The three rows in `impChain` form (`quote_qqAndTotalB`, `quote_isSemiformulaAndB`,
`quote_isSemiformulaSigmaPiB`). -/
noncomputable def rowAndTotalR : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand
noncomputable def rowIsAndAs : List V :=
  [subst LAct (listToVec [bv 3, bv 2]) Ppi, subst LAct (listToVec [bv 3, bv 1]) Ppi,
    subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand]
noncomputable def rowIsAndC : V := subst LAct (listToVec [bv 3, bv 0]) Psigma
noncomputable def rowSigmaPiA : V := subst LAct (listToVec [bv 1, bv 0]) Psigma
noncomputable def rowSigmaPiC : V := subst LAct (listToVec [bv 1, bv 0]) Ppi

theorem quote_qqAndTotalB :
    (⌜Semiformula.lMap emb qqAndTotalB⌝ : V) = impChain LAct [] (^∃ rowAndTotalR) := by
  rw [show qqAndTotalB = ∃¹ ((↑qqAndDef : ArithmeticSemisentence 3) ⇜ ![#0, #2, #1]) from rfl,
    quote_lMap_emb_ex, quote_lMap_emb_subst, impChain_nil]
  unfold rowAndTotalR Pand
  congr 2

theorem quote_isSemiformulaAndB :
    (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V) = impChain LAct rowIsAndAs rowIsAndC := by
  rw [show isSemiformulaAndB =
      ((↑(isSemiformula LAct).pi : ArithmeticSemisentence 2) ⇜ ![#3, #2]) 🡒
        (((↑(isSemiformula LAct).pi : ArithmeticSemisentence 2) ⇜ ![#3, #1]) 🡒
          (((↑qqAndDef : ArithmeticSemisentence 3) ⇜ ![#0, #2, #1]) 🡒
            ((↑(isSemiformula LAct).sigma : ArithmeticSemisentence 2) ⇜ ![#3, #0]))) from rfl,
    quote_lMap_emb_imp, quote_lMap_emb_imp, quote_lMap_emb_imp, quote_lMap_emb_subst,
    quote_lMap_emb_subst, quote_lMap_emb_subst, quote_lMap_emb_subst]
  unfold rowIsAndAs rowIsAndC Ppi Psigma Pand
  simp only [impChain_cons, impChain_nil]
  congr 2

theorem quote_isSemiformulaSigmaPiB :
    (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) = impChain LAct [rowSigmaPiA] rowSigmaPiC := by
  rw [show isSemiformulaSigmaPiB =
      ((↑(isSemiformula LAct).sigma : ArithmeticSemisentence 2) ⇜ ![#1, #0]) 🡒
        ((↑(isSemiformula LAct).pi : ArithmeticSemisentence 2) ⇜ ![#1, #0]) from rfl,
    quote_lMap_emb_imp, quote_lMap_emb_subst, quote_lMap_emb_subst]
  unfold rowSigmaPiA rowSigmaPiC Ppi Psigma
  simp only [impChain_cons, impChain_nil]
  congr 2

/-! #### Instances of the row pieces at closed witnesses -/

lemma isSemiterm_bv {i n : ℕ} (h : i < n) : IsSemiterm LAct (n : V) (bv i) :=
  IsSemiterm.bvar.mpr (Nat.cast_lt.mpr h)

lemma instOuter_subst_bv2 {P : V} (hP : IsSemiformula LAct ((2 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i j : ℕ} (hi : i < es.length) (hj : j < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i, bv j]) P) =
      subst LAct (listToVec [es.reverse.getD i 0, es.reverse.getD j 0]) P := by
  have hW : IsSemitermVec LAct ((2 : ℕ) : V) (es.length : V) (listToVec [bv i, bv j]) :=
    isSemitermVec_listToVec [bv i, bv j] (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact isSemiterm_bv hi
      · exact isSemiterm_bv hj)
  rw [instOuter_subst es hP hW hes]
  have h := termSubstVec_listToVec (L := LAct) (listToVec es.reverse) [bv i, bv j] (by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> simp)
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.map_cons,
    List.map_nil] at h
  rw [h, termSubst_bvar, termSubst_bvar, nth_listToVec, nth_listToVec]

lemma instOuterAt_subst_bv3 (k : ℕ) {P : V} (hP : IsSemiformula LAct ((3 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i j l : ℕ} (hi : i < es.length + k) (hj : j < es.length + k)
    (hl : l < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec [bv i, bv j, bv l]) P) =
      subst LAct (listToVec [(bvarList k ++ es.reverse).getD i 0, (bvarList k ++ es.reverse).getD j 0,
        (bvarList k ++ es.reverse).getD l 0]) P := by
  have hW : IsSemitermVec LAct ((3 : ℕ) : V) ((es.length + k : ℕ) : V) (listToVec [bv i, bv j, bv l]) :=
    isSemitermVec_listToVec [bv i, bv j, bv l] (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact isSemiterm_bv hi
      · exact isSemiterm_bv hj
      · exact isSemiterm_bv hl)
  rw [instOuterAt_subst k es hP hW hes]
  have h := termSubstVec_listToVec (L := LAct) (listToVec (bvarList k ++ es.reverse)) [bv i, bv j, bv l] (by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp)
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.map_cons,
    List.map_nil] at h
  rw [h, termSubst_bvar, termSubst_bvar, termSubst_bvar, nth_listToVec, nth_listToVec, nth_listToVec]

lemma instOuter_subst_bv3 {P : V} (hP : IsSemiformula LAct ((3 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i j l : ℕ} (hi : i < es.length) (hj : j < es.length)
    (hl : l < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i, bv j, bv l]) P) =
      subst LAct (listToVec [es.reverse.getD i 0, es.reverse.getD j 0, es.reverse.getD l 0]) P := by
  rw [← instOuterAt_zero, instOuterAt_subst_bv3 0 hP es hes (by simpa using hi) (by simpa using hj)
    (by simpa using hl)]
  simp [bvarList]

/-- Row 1 (`qqAndTotal`) at `[a, b]`: the existential body under the witnesses. -/
lemma inst_rowAndTotalR {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    instOuterAt LAct 1 [a, b] rowAndTotalR = subst LAct (listToVec [^#0, a, b]) Pand := by
  unfold rowAndTotalR
  rw [instOuterAt_subst_bv3 1 isSemiformula_Pand [a, b] (by simp [ha, hb]) (by simp) (by simp) (by simp)]
  simp [bvarList]

lemma free_inst_rowAndTotalR {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    free LAct (instOuterAt LAct 1 [a, b] rowAndTotalR) =
      andFact (^&0) (termShift LAct a) (termShift LAct b) := by
  rw [inst_rowAndTotalR ha hb, free_subst_listToVec [a, b] isSemiformula_Pand shift_Pand (by simp [ha, hb])]
  rfl

/-- Row 2 (`isSemiformulaAnd`) at `[n, a, b, z]`. -/
lemma inst_rowIsAnd {n a b z : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) (hz : IsSemiterm LAct 0 z) :
    rowIsAndAs.map (instOuter LAct [n, a, b, z]) = [piFact n a, piFact n b, andFact z a b] ∧
    instOuter LAct [n, a, b, z] rowIsAndC = sigmaFact n z := by
  have hes : ∀ e ∈ [n, a, b, z], IsSemiterm LAct 0 e := by simp [hn, ha, hb, hz]
  unfold rowIsAndAs rowIsAndC
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_bv2 isSemiformula_Ppi _ hes (by simp) (by simp),
    instOuter_subst_bv2 isSemiformula_Ppi _ hes (by simp) (by simp),
    instOuter_subst_bv3 isSemiformula_Pand _ hes (by simp) (by simp) (by simp),
    instOuter_subst_bv2 isSemiformula_Psigma _ hes (by simp) (by simp)]
  simp [piFact, andFact, sigmaFact]

/-- Row 3 (`isSemiformulaSigmaPi`) at `[n, z]`. -/
lemma inst_rowSigmaPi {n z : V} (hn : IsSemiterm LAct 0 n) (hz : IsSemiterm LAct 0 z) :
    instOuter LAct [n, z] rowSigmaPiA = sigmaFact n z ∧ instOuter LAct [n, z] rowSigmaPiC = piFact n z := by
  have hes : ∀ e ∈ [n, z], IsSemiterm LAct 0 e := by simp [hn, hz]
  unfold rowSigmaPiA rowSigmaPiC
  rw [instOuter_subst_bv2 isSemiformula_Psigma _ hes (by simp) (by simp),
    instOuter_subst_bv2 isSemiformula_Ppi _ hes (by simp) (by simp)]
  simp [piFact, sigmaFact]

/-- A fact about closed witnesses is shifted entrywise. -/
lemma shift_piFact {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) :
    shift LAct (piFact n a) = piFact (termShift LAct n) (termShift LAct a) := by
  unfold piFact
  rw [shift_subst_listToVec [n, a] isSemiformula_Ppi shift_Ppi (n := 0) (by simp [hn, ha])]
  rfl

/-! #### Formula-ness of the fact codes and of the row pieces -/

lemma isFormula_piFact {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) :
    IsFormula LAct (piFact n a) :=
  IsSemiformula.subst isSemiformula_Ppi (isSemitermVec_listToVec (n := 0) [n, a] (by simp [hn, ha]))

lemma isFormula_sigmaFact {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) :
    IsFormula LAct (sigmaFact n a) :=
  IsSemiformula.subst isSemiformula_Psigma (isSemitermVec_listToVec (n := 0) [n, a] (by simp [hn, ha]))

lemma isFormula_andFact {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) : IsFormula LAct (andFact z a b) :=
  IsSemiformula.subst isSemiformula_Pand (isSemitermVec_listToVec (n := 0) [z, a, b] (by simp [hz, ha, hb]))

lemma isSemiformula_rowAndTotalR : IsSemiformula LAct ((3 : ℕ) : V) rowAndTotalR :=
  IsSemiformula.subst isSemiformula_Pand (isSemitermVec_listToVec [bv 0, bv 2, bv 1] (by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact isSemiterm_bv (by norm_num)))

lemma isSemiformula_rowIsAnd :
    (∀ A ∈ rowIsAndAs, IsSemiformula LAct ((4 : ℕ) : V) (A : V)) ∧
    IsSemiformula LAct ((4 : ℕ) : V) (rowIsAndC : V) := by
  refine ⟨fun A hA ↦ ?_, ?_⟩
  · simp only [rowIsAndAs, List.mem_cons, List.mem_nil_iff, or_false] at hA
    rcases hA with rfl | rfl | rfl
    · exact IsSemiformula.subst isSemiformula_Ppi (isSemitermVec_listToVec [bv 3, bv 2] (by
        intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> exact isSemiterm_bv (by norm_num)))
    · exact IsSemiformula.subst isSemiformula_Ppi (isSemitermVec_listToVec [bv 3, bv 1] (by
        intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> exact isSemiterm_bv (by norm_num)))
    · exact IsSemiformula.subst isSemiformula_Pand (isSemitermVec_listToVec [bv 0, bv 2, bv 1] (by
        intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> exact isSemiterm_bv (by norm_num)))
  · exact IsSemiformula.subst isSemiformula_Psigma (isSemitermVec_listToVec [bv 3, bv 0] (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> exact isSemiterm_bv (by norm_num)))

lemma isSemiformula_rowSigmaPi :
    IsSemiformula LAct ((2 : ℕ) : V) (rowSigmaPiA : V) ∧ IsSemiformula LAct ((2 : ℕ) : V) (rowSigmaPiC : V) :=
  ⟨IsSemiformula.subst isSemiformula_Psigma (isSemitermVec_listToVec [bv 1, bv 0] (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> exact isSemiterm_bv (by norm_num))),
   IsSemiformula.subst isSemiformula_Ppi (isSemitermVec_listToVec [bv 1, bv 0] (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> exact isSemiterm_bv (by norm_num)))⟩

/-! #### The contexts and the code -/

/-- After row 1: `z = a ⋏ b` at the fresh `z = &0`, everything shifted. -/
noncomputable def ctx1 (Γ a b : V) : V :=
  insert (neg LAct (andFact (^&0) (termShift LAct a) (termShift LAct b))) (setShift LAct Γ)
/-- After row 2: `IsFormula z` in the `.sigma` reading. -/
noncomputable def ctx2 (Γ nc a b : V) : V :=
  insert (neg LAct (sigmaFact (termShift LAct nc) (^&0))) (ctx1 Γ a b)
/-- After row 3: `IsFormula z` in the `.pi` reading — what the continuation sees. -/
noncomputable def ctx3 (Γ nc a b : V) : V :=
  insert (neg LAct (piFact (termShift LAct nc) (^&0))) (ctx2 Γ nc a b)

lemma isFormulaSet_ctx1 {Γ a b : V} (hΓ : IsFormulaSet LAct Γ) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) : IsFormulaSet LAct (ctx1 Γ a b) := by
  have hz : IsSemiterm LAct 0 (^&0 : V) := by simp
  unfold ctx1
  simp [hΓ.setShift, isFormula_andFact hz ha.termShift hb.termShift]

lemma isFormulaSet_ctx2 {Γ nc a b : V} (hΓ : IsFormulaSet LAct Γ) (hnc : IsSemiterm LAct 0 nc)
    (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) : IsFormulaSet LAct (ctx2 Γ nc a b) := by
  have hz : IsSemiterm LAct 0 (^&0 : V) := by simp
  unfold ctx2
  simp [isFormulaSet_ctx1 hΓ ha hb, isFormula_sigmaFact hnc.termShift hz]

/-- **The smoke test.** From `IsFormula a`, `IsFormula b` (`.pi`) in `Γ`: row 1 (`qqAndTotal`) at
`[a, b]` introduces `z = &0` with `z = a ⋏ b`; row 2 (`isSemiformulaAnd`) at `[n, a, b, z]` (shifted)
gives `IsFormula z` (`.sigma`); row 3 (`isSemiformulaSigmaPi`) at `[n, z]` converts it to `.pi`. -/
noncomputable def describeAndCode (Γ nc a b dΛ₁ dΛ₂ dΛ₃ d : V) : V :=
  introFactCode LAct Γ [a, b] [] rowAndTotalR dΛ₁
    (useHornCode LAct (ctx1 Γ a b) [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0]
      rowIsAndAs rowIsAndC dΛ₂
      (useHornCode LAct (ctx2 Γ nc a b) [termShift LAct nc, ^&0] [rowSigmaPiA] rowSigmaPiC dΛ₃ d))

theorem describeAnd_row3_proof {Γ nc a b dΛ₃ d : V} (hΓ : IsFormulaSet LAct Γ)
    (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hΛ₃ : Proof TAct dΛ₃ (qqAlls (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) ((2 : ℕ) : V)))
    (hd : DerivationOf TAct d (ctx3 Γ nc a b)) :
    DerivationOf TAct
      (useHornCode LAct (ctx2 Γ nc a b) [termShift LAct nc, ^&0] [rowSigmaPiA] rowSigmaPiC dΛ₃ d)
      (ctx2 Γ nc a b) := by
  rw [qqAlls_natCast, quote_isSemiformulaSigmaPiB] at hΛ₃
  have hz : IsSemiterm LAct 0 (^&0 : V) := by simp
  obtain ⟨hA3, hC3⟩ := inst_rowSigmaPi hnc.termShift hz
  refine useHornCode_proof (fun A hA ↦ ?_) isSemiformula_rowSigmaPi.2 (by simp [hnc.termShift])
    (isFormulaSet_ctx2 hΓ hnc ha hb) (subset_refl _) (fun A hA ↦ ?_) hΛ₃ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
    rw [hA]; exact isSemiformula_rowSigmaPi.1
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
    rw [hA, hA3]
    unfold ctx2; simp
  · rw [hC3]; exact hd

theorem describeAnd_row2_proof {Γ nc a b dΛ₂ d₃ : V} (hΓ : IsFormulaSet LAct Γ)
    (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hfa : neg LAct (piFact nc a) ∈ Γ) (hfb : neg LAct (piFact nc b) ∈ Γ)
    (hΛ₂ : Proof TAct dΛ₂ (qqAlls (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V) ((4 : ℕ) : V)))
    (hd₃ : DerivationOf TAct d₃ (ctx2 Γ nc a b)) :
    DerivationOf TAct
      (useHornCode LAct (ctx1 Γ a b) [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0]
        rowIsAndAs rowIsAndC dΛ₂ d₃)
      (ctx1 Γ a b) := by
  rw [qqAlls_natCast, quote_isSemiformulaAndB] at hΛ₂
  have hz : IsSemiterm LAct 0 (^&0 : V) := by simp
  obtain ⟨hAs, hC⟩ := inst_rowIsAnd hnc.termShift ha.termShift hb.termShift hz
  refine useHornCode_proof isSemiformula_rowIsAnd.1 isSemiformula_rowIsAnd.2
    (by simp [hnc.termShift, ha.termShift, hb.termShift]) (isFormulaSet_ctx1 hΓ ha hb) (subset_refl _)
    (fun A hA ↦ ?_) hΛ₂ ?_
  · have hmem : instOuter LAct [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0] A ∈
        rowIsAndAs.map (instOuter LAct [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0]) :=
      List.mem_map_of_mem hA
    rw [hAs] at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h | h | h <;> rw [h] <;> unfold ctx1
    · apply mem_bitInsert_iff.mpr; right
      rw [← shift_piFact hnc ha, ← shift_neg (isFormula_piFact hnc ha)]
      exact shift_mem_setShift hfa
    · apply mem_bitInsert_iff.mpr; right
      rw [← shift_piFact hnc hb, ← shift_neg (isFormula_piFact hnc hb)]
      exact shift_mem_setShift hfb
    · simp
  · rw [hC]; exact hd₃

theorem describeAndCode_proof {Γ nc a b dΛ₁ dΛ₂ dΛ₃ d : V} (hΓ : IsFormulaSet LAct Γ)
    (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hfa : neg LAct (piFact nc a) ∈ Γ) (hfb : neg LAct (piFact nc b) ∈ Γ)
    (hΛ₁ : Proof TAct dΛ₁ (qqAlls (⌜Semiformula.lMap emb qqAndTotalB⌝ : V) ((2 : ℕ) : V)))
    (hΛ₂ : Proof TAct dΛ₂ (qqAlls (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V) ((4 : ℕ) : V)))
    (hΛ₃ : Proof TAct dΛ₃ (qqAlls (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) ((2 : ℕ) : V)))
    (hd : DerivationOf TAct d (ctx3 Γ nc a b)) :
    DerivationOf TAct (describeAndCode Γ nc a b dΛ₁ dΛ₂ dΛ₃ d) Γ := by
  rw [qqAlls_natCast, quote_qqAndTotalB] at hΛ₁
  have hR : IsSemiformula LAct ((([a, b] : List V).length : V) + 1) rowAndTotalR := by
    rw [show ((([a, b] : List V).length : ℕ) : V) + 1 = ((3 : ℕ) : V) by
      simp only [List.length_cons, List.length_nil]; push_cast; ring]
    exact isSemiformula_rowAndTotalR
  refine introFactCode_proof (by simp) hR (by simp [ha, hb]) hΓ (by simp) hΛ₁ ?_
  rw [free_inst_rowAndTotalR ha hb]
  exact describeAnd_row2_proof hΓ hnc ha hb hfa hfb hΛ₂ (describeAnd_row3_proof hΓ hnc ha hb hΛ₃ hd)

/-! #### Lengths: the witnesses, the contexts, the three rows, the whole -/

lemma termLen_le_of_two_mul_le {t E : V} (h : 2 * termLen LAct t ≤ E) : termLen LAct t ≤ E :=
  le_trans (le_mul_of_one_le_left zero_le one_le_two') h

lemma termLen_termShift_le_of {t E : V} (ht : IsSemiterm LAct 0 t) (h : 2 * termLen LAct t ≤ E) :
    termLen LAct (termShift LAct t) ≤ E :=
  le_trans (termLen_termShift_le ht) h

lemma termLen_fvar0_le {E : V} (hE : 1 ≤ E) : termLen LAct (^&0 : V) ≤ E := by
  rw [termLen_fvar, zero_add]; exact hE

/-- The row-1 witnesses, with lengths. -/
lemma row1_witnesses {E a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hEa : 2 * termLen LAct a ≤ E) (hEb : 2 * termLen LAct b ≤ E) :
    ∀ e ∈ [a, b], IsTerm LAct e ∧ termLen LAct e ≤ E := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  rintro e (rfl | rfl)
  · exact ⟨ha, termLen_le_of_two_mul_le hEa⟩
  · exact ⟨hb, termLen_le_of_two_mul_le hEb⟩

lemma row2_witnesses {E nc a b : V} (hE : 1 ≤ E) (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) (hEn : 2 * termLen LAct nc ≤ E) (hEa : 2 * termLen LAct a ≤ E)
    (hEb : 2 * termLen LAct b ≤ E) :
    ∀ e ∈ [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0], IsTerm LAct e ∧ termLen LAct e ≤ E := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  rintro e (rfl | rfl | rfl | rfl)
  · exact ⟨hnc.termShift, termLen_termShift_le_of hnc hEn⟩
  · exact ⟨ha.termShift, termLen_termShift_le_of ha hEa⟩
  · exact ⟨hb.termShift, termLen_termShift_le_of hb hEb⟩
  · exact ⟨by simp, termLen_fvar0_le hE⟩

lemma row3_witnesses {E nc : V} (hE : 1 ≤ E) (hnc : IsSemiterm LAct 0 nc) (hEn : 2 * termLen LAct nc ≤ E) :
    ∀ e ∈ [termShift LAct nc, ^&0], IsTerm LAct e ∧ termLen LAct e ≤ E := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  rintro e (rfl | rfl)
  · exact ⟨hnc.termShift, termLen_termShift_le_of hnc hEn⟩
  · exact ⟨by simp, termLen_fvar0_le hE⟩

/-- `|ctx1| ≤ 2|Γ| + 2·|B₁|·E` (the shift doubles, the new fact is the row's body under the
witnesses, freed). -/
lemma setLen_ctx1_le {E Γ a b : V} (hE : 1 ≤ E) (hΓ : IsFormulaSet LAct Γ) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) (hEa : 2 * termLen LAct a ≤ E) (hEb : 2 * termLen LAct b ≤ E) :
    setLen LAct (ctx1 Γ a b) ≤
      2 * setLen LAct Γ + 2 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E) := by
  have hes := row1_witnesses ha hb hEa hEb
  have hR3 : IsSemiformula LAct ((([a, b] : List V).length : V) + 1) rowAndTotalR := by
    rw [show ((([a, b] : List V).length : ℕ) : V) + 1 = ((3 : ℕ) : V) by
      simp only [List.length_cons, List.length_nil]; push_cast; ring]
    exact isSemiformula_rowAndTotalR
  have hR' : IsSemiformula LAct 1 (instOuterAt LAct 1 [a, b] rowAndTotalR) :=
    isSemiformula_one_instOuterAt [a, b] hR3 (fun e he ↦ (hes e he).1)
  have hEx : IsSemiformula LAct ((([a, b] : List V).length : V)) (^∃ rowAndTotalR) :=
    IsSemiformula.exs.mpr hR3
  have h1 : formulaLen LAct (instOuterAt LAct 1 [a, b] rowAndTotalR) ≤
      formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E := by
    rw [impChain_nil]
    refine le_trans ?_ (formulaLen_instOuter_le hE [a, b] hEx hes)
    rw [instOuter_exs [a, b] hR3 (fun e he ↦ (hes e he).1), formulaLen_exs hR'.isUFormula]
    exact le_self_add
  unfold ctx1
  refine le_trans (setLen_insert_le _ _) ?_
  rw [← free_inst_rowAndTotalR ha hb, formulaLen_neg hR'.free.isUFormula]
  calc setLen LAct (setShift LAct Γ) + formulaLen LAct (free LAct (instOuterAt LAct 1 [a, b] rowAndTotalR))
      ≤ 2 * setLen LAct Γ + 2 * formulaLen LAct (instOuterAt LAct 1 [a, b] rowAndTotalR) :=
        add_le_add (setLen_setShift_le hΓ) (formulaLen_free_le hR')
    _ ≤ 2 * setLen LAct Γ + 2 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E) := by gcongr

/-- `|ctx2| ≤ |ctx1| + |B₂|·E`. -/
lemma setLen_ctx2_le {E Γ nc a b : V} (hE : 1 ≤ E) (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) (hEn : 2 * termLen LAct nc ≤ E) (hEa : 2 * termLen LAct a ≤ E)
    (hEb : 2 * termLen LAct b ≤ E) :
    setLen LAct (ctx2 Γ nc a b) ≤
      setLen LAct (ctx1 Γ a b) + formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) * E := by
  have hes := row2_witnesses hE hnc ha hb hEn hEa hEb
  have hz : IsSemiterm LAct 0 (^&0 : V) := by simp
  obtain ⟨_, hC⟩ := inst_rowIsAnd hnc.termShift ha.termShift hb.termShift hz
  unfold ctx2
  refine le_trans (setLen_insert_le _ _) (add_le_add (le_refl _) ?_)
  rw [formulaLen_neg (isFormula_sigmaFact hnc.termShift hz).isUFormula, ← hC]
  refine le_trans (formulaLen_instOuter_le hE _ isSemiformula_rowIsAnd.2 hes) ?_
  exact mul_le_mul_of_nonneg_right
    (formulaLen_concl_le_impChain isSemiformula_rowIsAnd.1 isSemiformula_rowIsAnd.2) zero_le

/-- The continuation of row 3 in the form `useHornCode_proof` wants. -/
lemma row3_cont {Γ nc a b d : V} (hnc : IsSemiterm LAct 0 nc) (hd : DerivationOf TAct d (ctx3 Γ nc a b)) :
    DerivationOf TAct d (insert (neg LAct (instOuter LAct [termShift LAct nc, ^&0] rowSigmaPiC)) (ctx2 Γ nc a b)) := by
  rw [(inst_rowSigmaPi hnc.termShift (by simp)).2]; exact hd

lemma row3_hneg {Γ nc a b : V} (hnc : IsSemiterm LAct 0 nc) :
    ∀ A ∈ [rowSigmaPiA], neg LAct (instOuter LAct [termShift LAct nc, ^&0] A) ∈ ctx2 Γ nc a b := by
  intro A hA
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
  rw [hA, (inst_rowSigmaPi hnc.termShift (by simp)).1]
  unfold ctx2; simp

lemma row3_has : ∀ A ∈ [rowSigmaPiA], IsSemiformula LAct ((([termShift LAct nc, ^&0] : List V).length : V)) (A : V) := by
  intro A hA
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
  rw [hA]; exact isSemiformula_rowSigmaPi.1

/-- The continuation of row 2 in the form `useHornCode_proof` wants. -/
lemma row2_cont {Γ nc a b d₃ : V} (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) (hd₃ : DerivationOf TAct d₃ (ctx2 Γ nc a b)) :
    DerivationOf TAct d₃ (insert (neg LAct
      (instOuter LAct [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0] rowIsAndC)) (ctx1 Γ a b)) := by
  rw [(inst_rowIsAnd hnc.termShift ha.termShift hb.termShift (by simp)).2]; exact hd₃

lemma row2_hneg {Γ nc a b : V} (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a)
    (hb : IsSemiterm LAct 0 b) (hfa : neg LAct (piFact nc a) ∈ Γ) (hfb : neg LAct (piFact nc b) ∈ Γ) :
    ∀ A ∈ rowIsAndAs, neg LAct
      (instOuter LAct [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0] A) ∈ ctx1 Γ a b := by
  intro A hA
  have hmem : instOuter LAct [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0] A ∈
      rowIsAndAs.map (instOuter LAct [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0]) :=
    List.mem_map_of_mem hA
  rw [(inst_rowIsAnd hnc.termShift ha.termShift hb.termShift (by simp)).1] at hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h | h | h <;> rw [h] <;> unfold ctx1
  · apply mem_bitInsert_iff.mpr; right
    rw [← shift_piFact hnc ha, ← shift_neg (isFormula_piFact hnc ha)]
    exact shift_mem_setShift hfa
  · apply mem_bitInsert_iff.mpr; right
    rw [← shift_piFact hnc hb, ← shift_neg (isFormula_piFact hnc hb)]
    exact shift_mem_setShift hfb
  · simp

/-- The continuation of row 1 (`introFactCode`) in the form `introFactCode_proof` wants. -/
lemma row1_cont {Γ a b d₂ : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hd₂ : DerivationOf TAct d₂ (ctx1 Γ a b)) :
    DerivationOf TAct d₂ (insert (neg LAct (free LAct (instOuterAt LAct 1 [a, b] rowAndTotalR))) (setShift LAct Γ)) := by
  rw [free_inst_rowAndTotalR ha hb]; exact hd₂

lemma row1_hR {a b : V} : IsSemiformula LAct ((([a, b] : List V).length : V) + 1) rowAndTotalR := by
  rw [show ((([a, b] : List V).length : ℕ) : V) + 1 = ((3 : ℕ) : V) by
    simp only [List.length_cons, List.length_nil]; push_cast; ring]
  exact isSemiformula_rowAndTotalR

/-- Row 3: `dlen ≤ dlen dΛ₃ + dlen d + 8|ctx2| + 15|B₃|E + |B₃| + 2E + 28`. -/
theorem dlen_describeAnd_row3_le {E Γ nc a b dΛ₃ d : V} (hE : 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hEn : 2 * termLen LAct nc ≤ E)
    (hΛ₃ : Proof TAct dΛ₃ (qqAlls (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) ((2 : ℕ) : V)))
    (hd : DerivationOf TAct d (ctx3 Γ nc a b)) :
    dlen TAct (useHornCode LAct (ctx2 Γ nc a b) [termShift LAct nc, ^&0] [rowSigmaPiA] rowSigmaPiC dΛ₃ d) ≤
      dlen TAct dΛ₃ + dlen TAct d + 8 * setLen LAct (ctx2 Γ nc a b)
        + 15 * (formulaLen LAct (impChain LAct [rowSigmaPiA] rowSigmaPiC) * E)
        + formulaLen LAct (impChain LAct [rowSigmaPiA] rowSigmaPiC) + 2 * E + 28 := by
  rw [qqAlls_natCast, quote_isSemiformulaSigmaPiB] at hΛ₃
  have h := dlen_useHornCode_le (T := TAct) hE row3_has isSemiformula_rowSigmaPi.2
    (row3_witnesses hE hnc hEn) (isFormulaSet_ctx2 hΓ hnc ha hb) (subset_refl _) (row3_hneg hnc) hΛ₃
    (row3_cont hnc hd) (le_refl _)
  refine le_trans h (le_of_eq ?_)
  simp only [List.length_cons, List.length_nil, Nat.cast_ofNat, Nat.cast_one, Nat.zero_add, Nat.reduceAdd]
  ring

/-- Row 2: `dlen ≤ dlen dΛ₂ + dlen d₃ + 14|ctx1| + 53|B₂|E + |B₂| + 4E + 118`. -/
theorem dlen_describeAnd_row2_le {E Γ nc a b dΛ₂ d₃ : V} (hE : 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hEn : 2 * termLen LAct nc ≤ E) (hEa : 2 * termLen LAct a ≤ E) (hEb : 2 * termLen LAct b ≤ E)
    (hfa : neg LAct (piFact nc a) ∈ Γ) (hfb : neg LAct (piFact nc b) ∈ Γ)
    (hΛ₂ : Proof TAct dΛ₂ (qqAlls (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V) ((4 : ℕ) : V)))
    (hd₃ : DerivationOf TAct d₃ (ctx2 Γ nc a b)) :
    dlen TAct (useHornCode LAct (ctx1 Γ a b) [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0]
        rowIsAndAs rowIsAndC dΛ₂ d₃) ≤
      dlen TAct dΛ₂ + dlen TAct d₃ + 14 * setLen LAct (ctx1 Γ a b)
        + 53 * (formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) * E)
        + formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) + 4 * E + 118 := by
  rw [qqAlls_natCast, quote_isSemiformulaAndB] at hΛ₂
  have h := dlen_useHornCode_le (T := TAct) hE
    (es := [termShift LAct nc, termShift LAct a, termShift LAct b, ^&0])
    isSemiformula_rowIsAnd.1 isSemiformula_rowIsAnd.2 (row2_witnesses hE hnc ha hb hEn hEa hEb) (isFormulaSet_ctx1 hΓ ha hb) (subset_refl _)
    (row2_hneg hnc ha hb hfa hfb) hΛ₂ (row2_cont hnc ha hb hd₃) (le_refl _)
  refine le_trans h (le_of_eq ?_)
  simp only [rowIsAndAs, List.length_cons, List.length_nil, Nat.cast_ofNat, Nat.zero_add, Nat.reduceAdd]
  ring

/-- Row 1: `dlen ≤ dlen dΛ₁ + dlen d₂ + 12|Γ| + 24|B₁|E + |B₁| + 2E + 35`. -/
theorem dlen_describeAnd_row1_le {E Γ a b dΛ₁ d₂ : V} (hE : 1 ≤ E) (hΓ : IsFormulaSet LAct Γ)
    (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hEa : 2 * termLen LAct a ≤ E) (hEb : 2 * termLen LAct b ≤ E)
    (hΛ₁ : Proof TAct dΛ₁ (qqAlls (⌜Semiformula.lMap emb qqAndTotalB⌝ : V) ((2 : ℕ) : V)))
    (hd₂ : DerivationOf TAct d₂ (ctx1 Γ a b)) :
    dlen TAct (introFactCode LAct Γ [a, b] [] rowAndTotalR dΛ₁ d₂) ≤
      dlen TAct dΛ₁ + dlen TAct d₂ + 12 * setLen LAct Γ
        + 24 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E)
        + formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) + 2 * E + 35 := by
  rw [qqAlls_natCast, quote_qqAndTotalB] at hΛ₁
  have h := dlen_introFactCode_le (T := TAct) hE (by simp) row1_hR (row1_witnesses ha hb hEa hEb) hΓ
    (by simp) hΛ₁ (row1_cont ha hb hd₂) (le_refl _)
  refine le_trans h (le_of_eq ?_)
  simp only [List.length_cons, List.length_nil, Nat.cast_ofNat, Nat.cast_zero, Nat.zero_add, Nat.reduceAdd]
  ring

/-- **The smoke test's length**: with `E` a bound on the witness lengths (`1 ≤ E`,
`2|a|, 2|b|, 2|nc| ≤ E` — the shift may double a witness), `N_i` the three rows' stored-proof
lengths and `|B_i|` their bodies' lengths (constants of the rows),
`dlen ≤ dlen d + N₁ + N₂ + N₃ + 56·|Γ| + (68|B₁| + 61|B₂| + 15|B₃| + 8)·E + |B₁| + |B₂| + |B₃| + 181`. -/
theorem dlen_describeAndCode_le {E N₁ N₂ N₃ Γ nc a b dΛ₁ dΛ₂ dΛ₃ d : V} (hE : 1 ≤ E)
    (hΓ : IsFormulaSet LAct Γ)
    (hnc : IsSemiterm LAct 0 nc) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hEn : 2 * termLen LAct nc ≤ E) (hEa : 2 * termLen LAct a ≤ E) (hEb : 2 * termLen LAct b ≤ E)
    (hfa : neg LAct (piFact nc a) ∈ Γ) (hfb : neg LAct (piFact nc b) ∈ Γ)
    (hΛ₁ : Proof TAct dΛ₁ (qqAlls (⌜Semiformula.lMap emb qqAndTotalB⌝ : V) ((2 : ℕ) : V)))
    (hΛ₂ : Proof TAct dΛ₂ (qqAlls (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V) ((4 : ℕ) : V)))
    (hΛ₃ : Proof TAct dΛ₃ (qqAlls (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) ((2 : ℕ) : V)))
    (hN₁ : dlen TAct dΛ₁ ≤ N₁) (hN₂ : dlen TAct dΛ₂ ≤ N₂) (hN₃ : dlen TAct dΛ₃ ≤ N₃)
    (hd : DerivationOf TAct d (ctx3 Γ nc a b)) :
    dlen TAct (describeAndCode Γ nc a b dΛ₁ dΛ₂ dΛ₃ d) ≤
      dlen TAct d + N₁ + N₂ + N₃ + 56 * setLen LAct Γ
        + (68 * formulaLen LAct (⌜Semiformula.lMap emb qqAndTotalB⌝ : V)
            + 61 * formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V)
            + 15 * formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) + 8) * E
        + formulaLen LAct (⌜Semiformula.lMap emb qqAndTotalB⌝ : V)
        + formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V)
        + formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) + 181 := by
  rw [quote_qqAndTotalB, quote_isSemiformulaAndB, quote_isSemiformulaSigmaPiB]
  have hd₃ := describeAnd_row3_proof hΓ hnc ha hb hΛ₃ hd
  have hd₂ := describeAnd_row2_proof hΓ hnc ha hb hfa hfb hΛ₂ hd₃
  have h₁ := dlen_describeAnd_row1_le hE hΓ ha hb hEa hEb hΛ₁ hd₂
  have h₂ := dlen_describeAnd_row2_le hE hΓ hnc ha hb hEn hEa hEb hfa hfb hΛ₂ hd₃
  have h₃ := dlen_describeAnd_row3_le hE hΓ hnc ha hb hEn hΛ₃ hd
  have hc1 := setLen_ctx1_le hE hΓ ha hb hEa hEb
  have hc2 := setLen_ctx2_le (Γ := Γ) hE hnc ha hb hEn hEa hEb
  unfold describeAndCode
  calc _ ≤ _ := h₁
    _ ≤ N₁ + (dlen TAct dΛ₂ + dlen TAct (useHornCode LAct (ctx2 Γ nc a b) [termShift LAct nc, ^&0]
            [rowSigmaPiA] rowSigmaPiC dΛ₃ d) + 14 * setLen LAct (ctx1 Γ a b)
          + 53 * (formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) * E)
          + formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) + 4 * E + 118)
        + 12 * setLen LAct Γ + 24 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E)
        + formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) + 2 * E + 35 := by gcongr
    _ ≤ N₁ + (N₂ + (dlen TAct dΛ₃ + dlen TAct d + 8 * setLen LAct (ctx2 Γ nc a b)
            + 15 * (formulaLen LAct (impChain LAct [rowSigmaPiA] rowSigmaPiC) * E)
            + formulaLen LAct (impChain LAct [rowSigmaPiA] rowSigmaPiC) + 2 * E + 28)
          + 14 * setLen LAct (ctx1 Γ a b)
          + 53 * (formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) * E)
          + formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) + 4 * E + 118)
        + 12 * setLen LAct Γ + 24 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E)
        + formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) + 2 * E + 35 := by gcongr
    _ ≤ N₁ + (N₂ + (N₃ + dlen TAct d
            + 8 * ((2 * setLen LAct Γ + 2 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E))
                + formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) * E)
            + 15 * (formulaLen LAct (impChain LAct [rowSigmaPiA] rowSigmaPiC) * E)
            + formulaLen LAct (impChain LAct [rowSigmaPiA] rowSigmaPiC) + 2 * E + 28)
          + 14 * (2 * setLen LAct Γ + 2 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E))
          + 53 * (formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) * E)
          + formulaLen LAct (impChain LAct rowIsAndAs rowIsAndC) + 4 * E + 118)
        + 12 * setLen LAct Γ + 24 * (formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) * E)
        + formulaLen LAct (impChain LAct [] (^∃ rowAndTotalR)) + 2 * E + 35 := by
        gcongr
        exact le_trans hc2 (add_le_add hc1 (le_refl _))
    _ = _ := by ring

/-- **The smoke test, packaged along `Lib.univ_code`**: the three rows are library sentences, so
for ONE standard `N` and in EVERY model of `𝗜𝚺₁` there are stored proofs `dΛ₁ dΛ₂ dΛ₃` with which
`describeAndCode` derives `Γ` at length
`≤ dlen d + 56·|Γ| + (68|B₁| + 61|B₂| + 15|B₃| + 8)·E + |B₁| + |B₂| + |B₃| + N`
(`|Bᵢ|` the rows' body lengths, constants of the rows; `E` the witness bound). -/
theorem describeAndCode_exists : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ dΛ₁ dΛ₂ dΛ₃ : V, ∀ {E Γ nc a b d : V}, 1 ≤ E → IsFormulaSet LAct Γ →
      IsSemiterm LAct 0 nc → IsSemiterm LAct 0 a → IsSemiterm LAct 0 b →
      2 * termLen LAct nc ≤ E → 2 * termLen LAct a ≤ E → 2 * termLen LAct b ≤ E →
      neg LAct (piFact nc a) ∈ Γ → neg LAct (piFact nc b) ∈ Γ →
      DerivationOf TAct d (ctx3 Γ nc a b) →
      DerivationOf TAct (describeAndCode Γ nc a b dΛ₁ dΛ₂ dΛ₃ d) Γ ∧
      dlen TAct (describeAndCode Γ nc a b dΛ₁ dΛ₂ dΛ₃ d) ≤
        dlen TAct d + 56 * setLen LAct Γ
          + (68 * formulaLen LAct (⌜Semiformula.lMap emb qqAndTotalB⌝ : V)
              + 61 * formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V)
              + 15 * formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) + 8) * E
          + formulaLen LAct (⌜Semiformula.lMap emb qqAndTotalB⌝ : V)
          + formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V)
          + formulaLen LAct (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) + (N : V) := by
  obtain ⟨N₁, h₁⟩ := Lib.univ_code (B := qqAndTotalB) lib_qqAndTotal
  obtain ⟨N₂, h₂⟩ := Lib.univ_code (B := isSemiformulaAndB) lib_isSemiformulaAnd
  obtain ⟨N₃, h₃⟩ := Lib.univ_code (B := isSemiformulaSigmaPiB) lib_isSemiformulaSigmaPi
  refine ⟨N₁ + N₂ + N₃ + 181, fun V _ _ ↦ ?_⟩
  obtain ⟨dΛ₁, hΛ₁, hN₁⟩ := h₁ V
  obtain ⟨dΛ₂, hΛ₂, hN₂⟩ := h₂ V
  obtain ⟨dΛ₃, hΛ₃, hN₃⟩ := h₃ V
  refine ⟨dΛ₁, dΛ₂, dΛ₃, fun {E Γ nc a b d} hE hΓ hnc ha hb hEn hEa hEb hfa hfb hd ↦ ?_⟩
  refine ⟨describeAndCode_proof hΓ hnc ha hb hfa hfb hΛ₁ hΛ₂ hΛ₃ hd, ?_⟩
  refine le_trans (dlen_describeAndCode_le hE hΓ hnc ha hb hEn hEa hEb hfa hfb hΛ₁ hΛ₂ hΛ₃
    hN₁ hN₂ hN₃ hd) (le_of_eq ?_)
  push_cast
  ring

end smoke

end ArithS
