import ArithS.Necessitation.WalkLemmas

/-!
# ArithS.Necessitation.RowInst — every row of the formula walk, read off the DSL and instantiated

`M4_BOUNDED_HBL/DESIGN_describe.md` §4.2, §5, §9, §10 ("per-row `inst_row_ρ`"): for EVERY library
row the walk `describeSteps` and its top-down companions `negSteps`/`shiftSteps`/`substSteps`/
`freeSteps` use — the totality rows, the formation rows, the polarity bridges, the `<` rows, the
closed symbol rows, the vector rows, and the commutation rows — three things, all V-generic
(every model of `𝗜𝚺₁`, three standard axioms):

1. **The row-shape lemma** `quote_<row>B : ⌜lMap emb <row>B⌝ = impChain LAct row_<row>_as row_<row>_c`
   with every piece an explicit code `subst (listToVec [#i, …]) P` (`P` the code of the row's
   predicate, `#i` written `bv i`, the DSL's `n + 1` as `bv i ^+ 𝟏`, its literals `0`/`1` as
   `𝟎`/`𝟏`, the chain literals of the closed symbol rows as `cT k`) and an existential conclusion
   `row_<row>_c = ^∃ row_<row>_R`, `row_<row>_R = ^∃ … row_<row>_body` — read off the DSL by
   `rfl` after `quote_lMap_emb_imp/_ex/_and` and the vector form `quote_lMap_emb_subst'` of
   `Steps.lean`'s `quote_lMap_emb_subst` (§1 below: the typed `LAct`-quote of an embedded closed
   `ℒₒᵣ`-term is its `ℒₒᵣ` code, `entry_val`, so `‘#2 + 1’` reads `bv 2 ^+ 𝟏`, `quote_closed_add_m`).
   The `<` rows are `Operator.operator` applications: `Plt` is the code of the operator's
   sentence, and `zeroLtSuccB = Plt-sentence ⇜ ![‘0’, ‘#0 + 1’]` definitionally.
2. **The instantiation lemma** `inst_<row>` at ARBITRARY closed witnesses (one hypothesis
   `IsSemiterm LAct 0 w` per DSL variable; the witness list is the DSL variable list read
   RIGHT-TO-LEFT, `[w_{m-1}, …, w_0]`): every antecedent instance `instOuter es aᵢ` IS a canonical
   fact code (`piFact n p`, `andFact z a b`, …, `ltFact a b`, `negFact y p`, …), the Horn
   conclusion likewise, and an existential conclusion after its `a` eliminations —
   `freeIter a (instOuterAt a es body)` — is the conjunction of canonical facts about the
   eigenvariables `&(a-1) … &0` (the LAST-listed existential is `&0`) with every witness shifted
   `a` times (`termShift^[a] w`); the four rows with a NESTED existential (`freeRel/NRel/All/Exs`)
   get a third clause for the inner eliminations (`freeIterAt`, §1.4 below). So the hypotheses
   `neg (instOuter es aᵢ) ∈ Γ` of `useHornCode_proof`/`introFactCode_proof` are memberships of
   EXACTLY the codes of DESIGN §5. Chain numerals are the special case `w := cT k`
   (`cT_semiterm_LAct`; the row's `n + 1` at `cT k` is `cT k ^+ 𝟏 = cT (k + 1)`, `cT_succ`).
3. **The canonical fact codes** (§2 below; DESIGN §1.2's names in parentheses):
   `piFact/sigmaFact` (`piF/sigmaF`), `tPiFact/tSigmaFact`, `tvPiFact/tvSigmaFact`,
   `utvPiFact/utvSigmaFact`, the shape facts `relFact/nrelFact/verumFact/falsumFact/andFact/orFact/
   allFact/exsFact` (`relF …`, DESIGN's `shapeRel …`), `funcFact/bvarFact/fvarFact/adjFact`,
   `isRelFact/isFuncFact`, `ltFact`, the graph facts `negFact/shiftFact/substFact/substs1Fact/
   freeFact/qVecFact/tsvFact/tshvFact` — each `subst (listToVec [witnesses]) P` in the predicate's
   own variable order, with `IsFormula`-ness, the shift law `shift (xFact w…) = xFact (termShift w)…`,
   the length bound `formulaLen (xFact w…) ≤ formulaLen P · B` for any `B ≥ 1, termLen wᵢ`
   (`formulaLen P` an opaque row constant; the bound is MULTIPLICATIVE because a variable may
   occur several times in `P` — an additive `c + Σ termLen wᵢ` is false in general), and the
   occurrence bound `fvOccF (xFact w…) ≤ bvOccF P · M` for `M ≥ fvOcc wᵢ` (a quoted sentence has
   no free variables, `fvOccF_quote_sentence`), so a fact about eigenvariables has
   `fvOccF ≤ bvOccF P`, a constant.

§1 also supplies the walk's general instantiation laws: `instOuter_subst_listToVec` (any term
entries, `termSubst` entrywise), `instOuterAt_and` (distribution under `k` binders),
`freeIterAt m j` (`j` eigenvariable introductions under `m` extra binders; `freeIter = freeIterAt 0`),
`freeIter_exsIter` (introductions pass under an `exsIter`), `freeIterAt_and`, and the entrywise law
`freeIterAt_subst_listToVec : freeIterAt m j (subst ?[ws] P) = subst ?[ws.map (freeIterT m j)] P`
with `freeIterT m j` computed on `#i` (`i < m`: fixed; `m ≤ i < m + j`: `&(i - m)`) and on closed
terms (`termShift^[j]`).

Two DSL literals to know about: `isSemiformulaSubsts1B`/`isFormulaFreeB` write the arity of a
`1`-semiformula as the numeral `1`, whose code is `𝟏` (Foundation's `numeral 1`), NOT the chain
numeral `cT 1 = 𝟎 ^+ 𝟏` the walk writes for arities — an instance at `cT 1` does not match these
two rows syntactically (an equality row `0 + 1 = 1` or a rewrite of the two rows is needed if the
walk ever consumes them at a chain arity); `0` is `𝟎 = cT 0` (`cT_zero`) and matches.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- the row lemmas share one simp set and one finishing tactic; not every call uses every entry
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## 1. Infrastructure -/

/-! ### 1.1 Term-entry codes: the typed `LAct`-quote of an embedded closed `ℒₒᵣ`-term -/

/-- The entry of `quote_lMap_emb_subst`'s vector is the `ℒₒᵣ` code of the closed term. -/
lemma entry_val {m : ℕ} (t : ClosedSemiterm ℒₒᵣ m) :
    ((⌜(↑(Semiterm.lMap emb t) : SyntacticSemiterm LAct m)⌝ : Bootstrapping.Semiterm V LAct m)).val =
      (⌜t⌝ : V) := by
  rw [← Semiterm.quote_def]
  show (⌜(Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct m)⌝ : V) = _
  rw [Diag.term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def]

/-- `quote_lMap_emb_subst` with the entries as `ℒₒᵣ` closed codes. -/
lemma quote_lMap_emb_subst' {k m : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → ClosedSemiterm ℒₒᵣ m) :
    (⌜Semiformula.lMap emb (φ ⇜ v)⌝ : V) =
      subst LAct (matrixToVec fun i ↦ (⌜v i⌝ : V)) ⌜Semiformula.lMap emb φ⌝ := by
  rw [quote_lMap_emb_subst]
  congr 1
  unfold SemitermVec.val
  exact matrixToVec_congr (fun i ↦ entry_val (v i))

lemma quote_lMap_emb_and {n : ℕ} (φ ψ : ArithmeticSemisentence n) :
    (⌜Semiformula.lMap emb (φ ⋏ ψ)⌝ : V) = ⌜Semiformula.lMap emb φ⌝ ^⋏ ⌜Semiformula.lMap emb ψ⌝ := by
  rw [LogicalConnective.HomClass.map_and]; simp [Sentence.quote_def]

lemma matrixToVec_fin0 (f : Fin 0 → V) : matrixToVec f = listToVec [] := rfl
lemma matrixToVec_fin1 (f : Fin 1 → V) : matrixToVec f = listToVec [f 0] := rfl
lemma matrixToVec_fin2 (f : Fin 2 → V) : matrixToVec f = listToVec [f 0, f 1] := rfl
lemma matrixToVec_fin3 (f : Fin 3 → V) : matrixToVec f = listToVec [f 0, f 1, f 2] := rfl
lemma matrixToVec_fin4 (f : Fin 4 → V) : matrixToVec f = listToVec [f 0, f 1, f 2, f 3] := rfl
lemma matrixToVec_fin5 (f : Fin 5 → V) : matrixToVec f = listToVec [f 0, f 1, f 2, f 3, f 4] := rfl
lemma matrixToVec_fin6 (f : Fin 6 → V) : matrixToVec f = listToVec [f 0, f 1, f 2, f 3, f 4, f 5] := rfl
lemma matrixToVec_fin7 (f : Fin 7 → V) : matrixToVec f = listToVec [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := rfl

/-- The closed-term codes at any bound-variable count (`Bnum.lean` has the `m = 0` forms). -/
lemma quote_closed_add_m {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (⌜(‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ m)⌝ : V) = (⌜t⌝ : V) ^+ (⌜u⌝ : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_add]; rfl
lemma quote_closed_zero_m {m : ℕ} : (⌜(‘0’ : ClosedSemiterm ℒₒᵣ m)⌝ : V) = (𝟎 : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_numeral_eq_numeral]; simp
lemma quote_closed_one_m {m : ℕ} : (⌜(‘1’ : ClosedSemiterm ℒₒᵣ m)⌝ : V) = (𝟏 : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_numeral_eq_numeral]; simp
lemma quote_closed_bvar_m {m : ℕ} (i : Fin m) : (⌜(#i : ClosedSemiterm ℒₒᵣ m)⌝ : V) = bv (i : ℕ) := rfl

/-! ### 1.2 Entrywise `termSubst`; numerals and bound variables as row entries -/

lemma isSemiterm_qqOne_LAct (n : V) : IsSemiterm LAct n (𝟏 : V) := IsSemiterm.LAct_of_LOR one_semiterm
lemma isSemiterm_qqZero_LAct (n : V) : IsSemiterm LAct n (𝟎 : V) := IsSemiterm.LAct_of_LOR zero_semiterm

lemma termSubst_bv (l : List V) (i : ℕ) : termSubst LAct (listToVec l) (bv i) = l.getD i 0 := by
  rw [bv, termSubst_bvar, nth_listToVec]

lemma termSubst_qqAdd' {w x y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y) :
    termSubst LAct w (x ^+ y) = termSubst LAct w x ^+ termSubst LAct w y := by
  unfold qqAdd
  rw [termSubst_func isFunc_LAct_addIndex (by simp [hx, hy]), termSubstVec_cons₂ hx hy]

lemma termSubst_qqOne' (w : V) : termSubst LAct w (𝟏 : V) = 𝟏 :=
  termSubst_eq_self_of_closed (isSemiterm_qqOne_LAct 0)
lemma termSubst_qqZero' (w : V) : termSubst LAct w (𝟎 : V) = 𝟎 :=
  termSubst_eq_self_of_closed (isSemiterm_qqZero_LAct 0)

/-- The DSL's `n + 1` at a witness. -/
lemma termSubst_bv_add_one (l : List V) (i : ℕ) :
    termSubst LAct (listToVec l) (bv i ^+ (𝟏 : V)) = l.getD i 0 ^+ 𝟏 := by
  rw [termSubst_qqAdd' (by simp) (isSemiterm_qqOne_LAct 0).isUTerm, termSubst_bv, termSubst_qqOne']

lemma isSemiterm_bv_add_one {i n : ℕ} (h : i < n) : IsSemiterm LAct (n : V) (bv i ^+ (𝟏 : V)) := by
  unfold qqAdd
  exact IsSemiterm.func.mpr ⟨isFunc_LAct_addIndex, by simp [isSemiterm_bv h, isSemiterm_qqOne_LAct]⟩

lemma isSemiterm_iterate_termShift {t : V} (ht : IsSemiterm LAct 0 t) :
    ∀ j : ℕ, IsSemiterm LAct 0 ((termShift LAct)^[j] t)
  | 0 => ht
  | j + 1 => by rw [Function.iterate_succ_apply]; exact isSemiterm_iterate_termShift ht.termShift j

lemma iterate_termShift_qqZero : ∀ j : ℕ, (termShift LAct)^[j] (𝟎 : V) = 𝟎
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply, termShift_qqZero isFunc_LAct_zeroIndex, iterate_termShift_qqZero j]

lemma bvarList_zero : bvarList (V := V) 0 = [] := rfl
lemma bvarList_one : bvarList (V := V) 1 = [bv 0] := rfl
lemma bvarList_two : bvarList (V := V) 2 = [bv 0, bv 1] := rfl
lemma bvarList_three : bvarList (V := V) 3 = [bv 0, bv 1, bv 2] := rfl
lemma bvarList_four : bvarList (V := V) 4 = [bv 0, bv 1, bv 2, bv 3] := rfl
lemma bvarList_five : bvarList (V := V) 5 = [bv 0, bv 1, bv 2, bv 3, bv 4] := rfl

/-! ### 1.3 General instantiation: any term entries -/

/-- `instOuterAt k es` on `subst ?[t₁, …, t_N] P` substitutes `?[#0, …, #(k-1), e_m, …, e₁]` into
every entry (`instOuterAt_subst` + `termSubstVec_listToVec`). -/
theorem instOuterAt_subst_listToVec (k : ℕ) {P : V} (ts : List V) {n : ℕ}
    (hP : IsSemiformula LAct (n : V) P) (hn : ts.length = n) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (hts : ∀ t ∈ ts, IsSemiterm LAct ((es.length + k : ℕ) : V) t) :
    instOuterAt LAct k es (subst LAct (listToVec ts) P) =
      subst LAct (listToVec (ts.map (termSubst LAct (listToVec (bvarList k ++ es.reverse))))) P := by
  subst hn
  have hW : IsSemitermVec LAct ((ts.length : ℕ) : V) ((es.length + k : ℕ) : V) (listToVec ts) :=
    isSemitermVec_listToVec ts hts
  rw [instOuterAt_subst k es hP hW hes, termSubstVec_listToVec _ _ (fun x hx ↦ (hts x hx).isUTerm)]

theorem instOuter_subst_listToVec {P : V} (ts : List V) {n : ℕ}
    (hP : IsSemiformula LAct (n : V) P) (hn : ts.length = n) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (hts : ∀ t ∈ ts, IsSemiterm LAct ((es.length : ℕ) : V) t) :
    instOuter LAct es (subst LAct (listToVec ts) P) =
      subst LAct (listToVec (ts.map (termSubst LAct (listToVec es.reverse)))) P := by
  rw [← instOuterAt_zero, instOuterAt_subst_listToVec 0 ts hP hn es hes (by simpa using hts)]
  simp [bvarList]

/-- `instOuterAt` distributes over `⋏`. -/
lemma instOuterAt_and (k : ℕ) : ∀ (es : List V) {a b : V},
    IsSemiformula LAct ((es.length + k : ℕ) : V) a → IsSemiformula LAct ((es.length + k : ℕ) : V) b →
    (∀ e ∈ es, IsTerm LAct e) →
    instOuterAt LAct k es (a ^⋏ b) = instOuterAt LAct k es a ^⋏ instOuterAt LAct k es b
  | [], _, _, _, _, _ => rfl
  | e :: es, a, b, ha, hb, hes => by
    have cast : (((es.length + k : ℕ) : V) + 1) = (((e :: es).length + k : ℕ) : V) := by
      simp only [List.length_cons]; push_cast; ring
    have ha' : IsSemiformula LAct (((es.length + k : ℕ) : V) + 1) a := by rw [cast]; exact ha
    have hb' : IsSemiformula LAct (((es.length + k : ℕ) : V) + 1) b := by rw [cast]; exact hb
    rw [instOuterAt_cons, instOuterAt_cons, instOuterAt_cons, subOuter_and ha.isUFormula hb.isUFormula]
    exact instOuterAt_and k es (isSemiformula_subOuter ha' (hes e (by simp)))
      (isSemiformula_subOuter hb' (hes e (by simp))) (fun e' he' ↦ hes e' (by simp [he']))

/-- Formula-ness of a row piece / a fact code at any level. -/
lemma isSemiformula_substRow {n k : ℕ} {P : V} (hP : IsSemiformula LAct (k : V) P) (ts : List V)
    (hk : ts.length = k) (hts : ∀ t ∈ ts, IsSemiterm LAct (n : V) t) :
    IsSemiformula LAct (n : V) (subst LAct (listToVec ts) P) := by
  subst hk
  exact IsSemiformula.subst hP (isSemitermVec_listToVec ts hts)

lemma isSemiformula_exs_cast {m : ℕ} {p : V} (h : IsSemiformula LAct ((m + 1 : ℕ) : V) p) :
    IsSemiformula LAct ((m : ℕ) : V) (^∃ p) := by
  rw [Nat.cast_succ] at h
  exact IsSemiformula.exs.mpr h

/-! ### 1.4 `freeIterAt`: eigenvariable introductions under extra binders, entrywise -/

/-- `freeIterAt m j q`: `j` eigenvariable introductions on a `(j + m)`-semiformula `q`, from the
outermost quantifier inwards, leaving the `m` innermost bound variables in place
(`freeIter j = freeIterAt 0 j`; the introductions of the `j` outer existentials of `∃^m … ∃^j q`,
`freeIter_exsIter`). -/
noncomputable def freeIterAt (m : ℕ) : ℕ → V → V
  | 0, q => q
  | j + 1, q => freeIterAt m j (subOuter LAct (j + m) (^&0) (shift LAct q))

@[simp] lemma freeIterAt_zero (m : ℕ) (q : V) : freeIterAt m 0 q = q := rfl
@[simp] lemma freeIterAt_succ (m j : ℕ) (q : V) :
    freeIterAt m (j + 1) q = freeIterAt m j (subOuter LAct (j + m) (^&0) (shift LAct q)) := rfl

lemma freeIterAt_zero_eq (j : ℕ) (q : V) : freeIterAt 0 j q = freeIter LAct j q := by
  induction j generalizing q with
  | zero => rfl
  | succ j ih => rw [freeIterAt_succ, freeIter_succ, Nat.add_zero, ih]

lemma cast_succ_add (j m : ℕ) : ((j + 1 + m : ℕ) : V) = ((j + m : ℕ) : V) + 1 := by push_cast; ring

/-- Introductions pass under `m` existentials: `freeIter j (∃^m q) = ∃^m (freeIterAt m j q)`. -/
lemma freeIter_exsIter (m : ℕ) : ∀ (j : ℕ) {q : V}, IsSemiformula LAct ((j + m : ℕ) : V) q →
    freeIter LAct j (exsIter m q) = exsIter m (freeIterAt m j q)
  | 0, _, _ => rfl
  | j + 1, q, hq => by
    have hq' : IsSemiformula LAct (((j + m : ℕ) : V) + 1) (shift LAct q) := by
      rw [← cast_succ_add]; exact hq.shift
    rw [freeIter_succ, shift_exsIter hq.isUFormula, subOuter_exsIter hq.isUFormula.shift,
      freeIter_exsIter m j (isSemiformula_subOuter hq' (by simp)), freeIterAt_succ]

lemma freeIter_exs2 (j : ℕ) {q : V} (hq : IsSemiformula LAct ((j + 2 : ℕ) : V) q) :
    freeIter LAct j (^∃ (^∃ q)) = ^∃ (^∃ (freeIterAt 2 j q)) := freeIter_exsIter 2 j hq

lemma freeIter_exs3 (j : ℕ) {q : V} (hq : IsSemiformula LAct ((j + 3 : ℕ) : V) q) :
    freeIter LAct j (^∃ (^∃ (^∃ q))) = ^∃ (^∃ (^∃ (freeIterAt 3 j q))) := freeIter_exsIter 3 j hq

/-- The inner-first reading: `freeIterAt m (j + 1) q = subOuter m (&0) (shift (freeIterAt (m + 1) j q))`
— what `sElimExs` on the outermost remaining existential does to a body already freed `j` times. -/
lemma freeIterAt_succ' (m : ℕ) : ∀ (j : ℕ) (q : V),
    freeIterAt m (j + 1) q = subOuter LAct m (^&0) (shift LAct (freeIterAt (m + 1) j q))
  | 0, q => by rw [freeIterAt_succ, freeIterAt_zero, freeIterAt_zero, Nat.zero_add]
  | j + 1, q => by
    rw [freeIterAt_succ, freeIterAt_succ' m j, freeIterAt_succ,
      show j + 1 + m = j + (m + 1) by omega]

/-- The entrywise action of `freeIterAt m j`. -/
noncomputable def freeIterT (m : ℕ) : ℕ → V → V
  | 0, t => t
  | j + 1, t => freeIterT m j (termSubst LAct (qVecIter LAct (j + m) (^&0 ∷ (0 : V))) (termShift LAct t))

@[simp] lemma freeIterT_zero (m : ℕ) (t : V) : freeIterT m 0 t = t := rfl
@[simp] lemma freeIterT_succ (m j : ℕ) (t : V) :
    freeIterT m (j + 1) t =
      freeIterT m j (termSubst LAct (qVecIter LAct (j + m) (^&0 ∷ (0 : V))) (termShift LAct t)) := rfl

lemma freeIterAt_and (m : ℕ) : ∀ (j : ℕ) {a b : V},
    IsSemiformula LAct ((j + m : ℕ) : V) a → IsSemiformula LAct ((j + m : ℕ) : V) b →
    freeIterAt m j (a ^⋏ b) = freeIterAt m j a ^⋏ freeIterAt m j b
  | 0, _, _, _, _ => rfl
  | j + 1, a, b, ha, hb => by
    have ha' : IsSemiformula LAct (((j + m : ℕ) : V) + 1) (shift LAct a) := by
      rw [← cast_succ_add]; exact ha.shift
    have hb' : IsSemiformula LAct (((j + m : ℕ) : V) + 1) (shift LAct b) := by
      rw [← cast_succ_add]; exact hb.shift
    rw [freeIterAt_succ, shift_and ha.isUFormula hb.isUFormula, subOuter_and ha'.isUFormula hb'.isUFormula]
    exact freeIterAt_and m j (isSemiformula_subOuter ha' (by simp)) (isSemiformula_subOuter hb' (by simp))

lemma freeIter_and (j : ℕ) {a b : V} (ha : IsSemiformula LAct (j : V) a) (hb : IsSemiformula LAct (j : V) b) :
    freeIter LAct j (a ^⋏ b) = freeIter LAct j a ^⋏ freeIter LAct j b := by
  rw [← freeIterAt_zero_eq, ← freeIterAt_zero_eq, ← freeIterAt_zero_eq]
  exact freeIterAt_and 0 j (by simpa using ha) (by simpa using hb)

/-- **The entrywise law**: `freeIterAt m j (subst ?[ws] P) = subst ?[ws.map (freeIterT m j)] P` for a
quoted sentence code `P` (`shift P = P`) and entries of level `j + m`. -/
theorem freeIterAt_subst_listToVec (m j : ℕ) (ws : List V) {P : V} {n : ℕ}
    (hP : IsSemiformula LAct (n : V) P) (hP0 : shift LAct P = P) (hn : ws.length = n)
    (hws : ∀ w ∈ ws, IsSemiterm LAct ((j + m : ℕ) : V) w) :
    freeIterAt m j (subst LAct (listToVec ws) P) = subst LAct (listToVec (ws.map (freeIterT m j))) P := by
  induction j generalizing ws with
  | zero =>
    rw [freeIterAt_zero, List.map_congr_left (fun t _ ↦ freeIterT_zero m t), List.map_id']
  | succ j ih =>
    subst hn
    have hsh : ∀ x ∈ ws, IsSemiterm LAct (((j + m : ℕ) : V) + 1) (termShift LAct x) := by
      intro x hx
      rw [← cast_succ_add]; exact (hws x hx).termShift
    have hws' : ∀ w ∈ ws.map (termShift LAct), IsSemiterm LAct (((j + m : ℕ) : V) + 1) w := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact hsh x hx
    have hW : IsSemitermVec LAct (((ws.map (termShift LAct)).length : ℕ) : V) (((j + m : ℕ) : V) + 1)
        (listToVec (ws.map (termShift LAct))) := isSemitermVec_listToVec _ hws'
    have hP' : IsSemiformula LAct (((ws.map (termShift LAct)).length : ℕ) : V) P := by simpa using hP
    have hq : IsSemitermVec LAct (((j + m : ℕ) : V) + 1) ((j + m : ℕ) : V)
        (qVecIter LAct (j + m) (^&0 ∷ (0 : V))) := isSemitermVec_qVecIter_single (by simp)
    rw [freeIterAt_succ, shift_subst_listToVec ws hP hP0 hws, subOuter_subst hP' hW (by simp),
      termSubstVec_listToVec _ _ (fun x hx ↦ (hws' x hx).isUTerm),
      ih _ (by simp) (by
        intro w hw
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
        exact hq.termSubst (hws' x hx)),
      List.map_map, List.map_map]
    exact congrArg (fun l ↦ subst LAct (listToVec l) P)
      (List.map_congr_left (fun t _ ↦ (freeIterT_succ m j t).symm))

theorem freeIter_subst_listToVec' (j : ℕ) (ws : List V) {P : V} {n : ℕ}
    (hP : IsSemiformula LAct (n : V) P) (hP0 : shift LAct P = P) (hn : ws.length = n)
    (hws : ∀ w ∈ ws, IsSemiterm LAct (j : V) w) :
    freeIter LAct j (subst LAct (listToVec ws) P) = subst LAct (listToVec (ws.map (freeIterT 0 j))) P := by
  rw [← freeIterAt_zero_eq]
  exact freeIterAt_subst_listToVec 0 j ws hP hP0 hn (by simpa using hws)

/-- Closed entries are shifted `j` times. -/
lemma freeIterT_closed (m : ℕ) {t : V} (ht : IsSemiterm LAct 0 t) :
    ∀ j : ℕ, freeIterT m j t = (termShift LAct)^[j] t
  | 0 => rfl
  | j + 1 => by
    rw [freeIterT_succ, termSubst_eq_self_of_closed ht.termShift, freeIterT_closed m ht.termShift j,
      Function.iterate_succ_apply]

/-- The `m` innermost bound variables stay. -/
lemma freeIterT_bv_lt (m : ℕ) : ∀ (j i : ℕ), i < m → freeIterT m j (bv i : V) = bv i
  | 0, _, _ => rfl
  | j + 1, i, hi => by
    rw [freeIterT_succ, bv, termShift_bvar, termSubst_qVecIter_bvar_lt (by simp) (by omega)]
    exact freeIterT_bv_lt m j i hi

/-- The `j` outer bound variables become `&(i - m)`: the innermost of them is `&0`. -/
lemma freeIterT_bv_ge (m : ℕ) : ∀ (j i : ℕ), m ≤ i → i < m + j →
    freeIterT m j (bv i : V) = ^&(((i - m : ℕ) : ℕ) : V)
  | 0, i, h1, h2 => by omega
  | j + 1, i, h1, h2 => by
    rw [freeIterT_succ, bv, termShift_bvar]
    rcases Nat.lt_or_ge i (j + m) with h | h
    · rw [termSubst_qVecIter_bvar_lt (by simp) h]
      exact freeIterT_bv_ge m j i h1 (by omega)
    · have : i = j + m := by omega
      subst this
      rw [termSubst_qVecIter_bvar_eq (by simp), freeIterT_closed m (by simp) j,
        termShift_iterate_fvar (V := V) (L := LAct)]
      simp

lemma freeIterT_bv0 (j i : ℕ) (hi : i < j) : freeIterT 0 j (bv i : V) = ^&((i : ℕ) : V) := by
  rw [freeIterT_bv_ge 0 j i (Nat.zero_le _) (by omega), Nat.sub_zero]

/-! ### 1.5 Generic fact-code lemmas -/

lemma forall_nth_listToVec {Q : V → Prop} (ws : List V) (h : ∀ w ∈ ws, Q w) :
    ∀ i < ((ws.length : ℕ) : V), Q (listToVec ws).[i] := by
  intro i hi
  obtain ⟨i', rfl, hi'⟩ := exists_natCast_of_lt_natCast _ i hi
  rw [nth_listToVec, List.getD_eq_getElem _ _ hi']
  exact h _ (List.getElem_mem hi')

lemma substInv_listToVec {B : V} (ws : List V) (h : ∀ w ∈ ws, IsSemiterm LAct 0 w ∧ termLen LAct w ≤ B) :
    SubstInv LAct B (listToVec ws) := by
  intro i hi
  rw [len_listToVec] at hi
  exact Or.inr (forall_nth_listToVec ws h i hi)

/-- A quoted sentence has no free-variable occurrence (`shift` fixes it, `formulaLen_shift_eq`). -/
lemma fvOccF_quote_sentence {n : ℕ} (σ : Semisentence LAct n) : fvOccF LAct (⌜σ⌝ : V) = 0 := by
  have h := formulaLen_shift_eq (L := LAct) (Sentence.quote_isSemiformula (V := V) σ).isUFormula
  rw [shift_quote_sentence] at h
  have : formulaLen LAct (⌜σ⌝ : V) + 0 = formulaLen LAct (⌜σ⌝ : V) + fvOccF LAct ⌜σ⌝ := by
    rw [add_zero]; exact h
  exact (add_left_cancel this).symm

section fact
variable {P : V} {n : ℕ}

lemma isFormula_fact (hP : IsSemiformula LAct (n : V) P) (ws : List V) (hn : ws.length = n)
    (hws : ∀ w ∈ ws, IsSemiterm LAct 0 w) : IsFormula LAct (subst LAct (listToVec ws) P) := by
  subst hn
  exact IsSemiformula.subst hP (isSemitermVec_listToVec ws hws)

/-- `|subst ?[ws] P| ≤ |P| · B` for `B ≥ 1` bounding every witness (`formulaLen_subst_le`). -/
lemma formulaLen_fact_le {B : V} (hB : 1 ≤ B) (hP : IsSemiformula LAct (n : V) P) (ws : List V)
    (hn : ws.length = n) (hws : ∀ w ∈ ws, IsSemiterm LAct 0 w ∧ termLen LAct w ≤ B) :
    formulaLen LAct (subst LAct (listToVec ws) P) ≤ formulaLen LAct P * B := by
  subst hn
  exact formulaLen_subst_le hB hP _ _ (isSemitermVec_listToVec ws (fun w hw ↦ (hws w hw).1))
    (substInv_listToVec ws hws)

/-- `fvOccF (subst ?[ws] P) ≤ bvOccF P · M` for `M` bounding every witness's occurrences. -/
lemma fvOccF_fact_le {M : V} (hP : IsSemiformula LAct (n : V) P) (hP0 : fvOccF LAct P = 0) (ws : List V)
    (hn : ws.length = n) (hws : ∀ w ∈ ws, IsSemiterm LAct 0 w ∧ fvOcc LAct w ≤ M) :
    fvOccF LAct (subst LAct (listToVec ws) P) ≤ bvOccF LAct P * M := by
  subst hn
  have := fvOccF_subst_le hP (isSemitermVec_listToVec ws (fun w hw ↦ (hws w hw).1))
    (forall_nth_listToVec ws (fun w hw ↦ (hws w hw).2))
  rwa [hP0, zero_add] at this

end fact

/-! ### 1.6 The three uniform tactics of the row lemmas -/

/-- Level-`n` term-ness of every entry of a row piece (`#i`, `#i + 1`, `𝟎`, `𝟏`, `cT k`, a closed
witness in context, its iterated shift, an eigenvariable `&i`). -/
macro "row_entries" : tactic => `(tactic| (
  repeat' refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
  all_goals first
    | exact List.forall_mem_nil _
    | exact isSemiterm_bv (by norm_num)
    | exact isSemiterm_bv_add_one (by norm_num)
    | exact isSemiterm_qqZero_LAct _
    | exact isSemiterm_qqOne_LAct _
    | exact cT_semiterm_LAct _ _
    | exact isSemiterm_of_le (by assumption) zero_le
    | exact isSemiterm_of_le (isSemiterm_iterate_termShift (by assumption) _) zero_le
    | simp))

/-- Evaluate the entrywise substitution of an instantiated piece. -/
macro "row_entries_simp" : tactic => `(tactic| simp only [List.map_cons, List.map_nil, termSubst_bv,
  termSubst_bv_add_one, termSubst_qqZero', termSubst_qqOne', termSubst_cT, bvarList_zero, bvarList_one,
  bvarList_two, bvarList_three, bvarList_four, bvarList_five, List.reverse_cons, List.reverse_nil,
  List.nil_append, List.append_nil, List.cons_append, List.singleton_append, List.getD_cons_zero,
  List.getD_cons_succ])

/-- Close `[..] = [..] ∧ code = fact` (or what is left of it) by unfolding the fact codes. -/
macro "row_finish" : tactic => `(tactic| all_goals first
  | rfl
  | (refine ⟨?_, ?_⟩ <;> first | rfl | trivial)
  | trivial)

/-- Read a row body off the DSL. -/
macro "row_shape" : tactic => `(tactic| (
  simp only [Semiformula.Operator.operator, quote_lMap_emb_imp, quote_lMap_emb_ex, quote_lMap_emb_and,
    quote_lMap_emb_subst', impChain_cons, impChain_nil, matrixToVec_fin0, matrixToVec_fin1, matrixToVec_fin2,
    matrixToVec_fin3, matrixToVec_fin4, matrixToVec_fin5, matrixToVec_fin6, matrixToVec_fin7,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    quote_closed_add_m, quote_closed_one_m, quote_closed_zero_m, quote_closed_bvar_m, quote_cTT]
  all_goals rfl))

/-! ## 2. The predicate codes and the canonical fact codes -/

section facts

lemma fvOccF_Ppi : fvOccF LAct (Ppi : V) = 0 := fvOccF_quote_sentence _

lemma fvOccF_Psigma : fvOccF LAct (Psigma : V) = 0 := fvOccF_quote_sentence _

lemma fvOccF_Pand : fvOccF LAct (Pand : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqOr` (arity 3). -/
noncomputable def Por : V := ⌜Semiformula.lMap emb (↑qqOrDef : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Por : IsSemiformula LAct ((3 : ℕ) : V) Por := Sentence.quote_isSemiformula _
lemma shift_Por : shift LAct (Por : V) = Por := shift_quote_sentence _
lemma fvOccF_Por : fvOccF LAct (Por : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqAll` (arity 2). -/
noncomputable def Pall : V := ⌜Semiformula.lMap emb (↑qqAllDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pall : IsSemiformula LAct ((2 : ℕ) : V) Pall := Sentence.quote_isSemiformula _
lemma shift_Pall : shift LAct (Pall : V) = Pall := shift_quote_sentence _
lemma fvOccF_Pall : fvOccF LAct (Pall : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqExs` (arity 2). -/
noncomputable def Pexs : V := ⌜Semiformula.lMap emb (↑qqExsDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pexs : IsSemiformula LAct ((2 : ℕ) : V) Pexs := Sentence.quote_isSemiformula _
lemma shift_Pexs : shift LAct (Pexs : V) = Pexs := shift_quote_sentence _
lemma fvOccF_Pexs : fvOccF LAct (Pexs : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqRel` (arity 4). -/
noncomputable def Prel : V := ⌜Semiformula.lMap emb (↑qqRelDef : ArithmeticSemisentence 4)⌝
lemma isSemiformula_Prel : IsSemiformula LAct ((4 : ℕ) : V) Prel := Sentence.quote_isSemiformula _
lemma shift_Prel : shift LAct (Prel : V) = Prel := shift_quote_sentence _
lemma fvOccF_Prel : fvOccF LAct (Prel : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqNRel` (arity 4). -/
noncomputable def Pnrel : V := ⌜Semiformula.lMap emb (↑qqNRelDef : ArithmeticSemisentence 4)⌝
lemma isSemiformula_Pnrel : IsSemiformula LAct ((4 : ℕ) : V) Pnrel := Sentence.quote_isSemiformula _
lemma shift_Pnrel : shift LAct (Pnrel : V) = Pnrel := shift_quote_sentence _
lemma fvOccF_Pnrel : fvOccF LAct (Pnrel : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqVerum` (arity 1). -/
noncomputable def Pverum : V := ⌜Semiformula.lMap emb (↑qqVerumDef : ArithmeticSemisentence 1)⌝
lemma isSemiformula_Pverum : IsSemiformula LAct ((1 : ℕ) : V) Pverum := Sentence.quote_isSemiformula _
lemma shift_Pverum : shift LAct (Pverum : V) = Pverum := shift_quote_sentence _
lemma fvOccF_Pverum : fvOccF LAct (Pverum : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqFalsum` (arity 1). -/
noncomputable def Pfalsum : V := ⌜Semiformula.lMap emb (↑qqFalsumDef : ArithmeticSemisentence 1)⌝
lemma isSemiformula_Pfalsum : IsSemiformula LAct ((1 : ℕ) : V) Pfalsum := Sentence.quote_isSemiformula _
lemma shift_Pfalsum : shift LAct (Pfalsum : V) = Pfalsum := shift_quote_sentence _
lemma fvOccF_Pfalsum : fvOccF LAct (Pfalsum : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqFunc` (arity 4). -/
noncomputable def Pfunc : V := ⌜Semiformula.lMap emb (↑qqFuncDef : ArithmeticSemisentence 4)⌝
lemma isSemiformula_Pfunc : IsSemiformula LAct ((4 : ℕ) : V) Pfunc := Sentence.quote_isSemiformula _
lemma shift_Pfunc : shift LAct (Pfunc : V) = Pfunc := shift_quote_sentence _
lemma fvOccF_Pfunc : fvOccF LAct (Pfunc : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqBvar` (arity 2). -/
noncomputable def Pbvar : V := ⌜Semiformula.lMap emb (↑qqBvarDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pbvar : IsSemiformula LAct ((2 : ℕ) : V) Pbvar := Sentence.quote_isSemiformula _
lemma shift_Pbvar : shift LAct (Pbvar : V) = Pbvar := shift_quote_sentence _
lemma fvOccF_Pbvar : fvOccF LAct (Pbvar : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qqFvar` (arity 2). -/
noncomputable def Pfvar : V := ⌜Semiformula.lMap emb (↑qqFvarDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pfvar : IsSemiformula LAct ((2 : ℕ) : V) Pfvar := Sentence.quote_isSemiformula _
lemma shift_Pfvar : shift LAct (Pfvar : V) = Pfvar := shift_quote_sentence _
lemma fvOccF_Pfvar : fvOccF LAct (Pfvar : V) = 0 := fvOccF_quote_sentence _

/-- The code of `adjoin` (arity 3). -/
noncomputable def Padjoin : V := ⌜Semiformula.lMap emb (↑adjoinDef : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Padjoin : IsSemiformula LAct ((3 : ℕ) : V) Padjoin := Sentence.quote_isSemiformula _
lemma shift_Padjoin : shift LAct (Padjoin : V) = Padjoin := shift_quote_sentence _
lemma fvOccF_Padjoin : fvOccF LAct (Padjoin : V) = 0 := fvOccF_quote_sentence _

/-- The code of `tpi` (arity 2). -/
noncomputable def PtPi : V := ⌜Semiformula.lMap emb (↑(isSemiterm LAct).pi : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PtPi : IsSemiformula LAct ((2 : ℕ) : V) PtPi := Sentence.quote_isSemiformula _
lemma shift_PtPi : shift LAct (PtPi : V) = PtPi := shift_quote_sentence _
lemma fvOccF_PtPi : fvOccF LAct (PtPi : V) = 0 := fvOccF_quote_sentence _

/-- The code of `tsigma` (arity 2). -/
noncomputable def PtSigma : V := ⌜Semiformula.lMap emb (↑(isSemiterm LAct).sigma : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PtSigma : IsSemiformula LAct ((2 : ℕ) : V) PtSigma := Sentence.quote_isSemiformula _
lemma shift_PtSigma : shift LAct (PtSigma : V) = PtSigma := shift_quote_sentence _
lemma fvOccF_PtSigma : fvOccF LAct (PtSigma : V) = 0 := fvOccF_quote_sentence _

/-- The code of `tvpi` (arity 3). -/
noncomputable def PtvPi : V := ⌜Semiformula.lMap emb (↑(isSemitermVec LAct).pi : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PtvPi : IsSemiformula LAct ((3 : ℕ) : V) PtvPi := Sentence.quote_isSemiformula _
lemma shift_PtvPi : shift LAct (PtvPi : V) = PtvPi := shift_quote_sentence _
lemma fvOccF_PtvPi : fvOccF LAct (PtvPi : V) = 0 := fvOccF_quote_sentence _

/-- The code of `tvsigma` (arity 3). -/
noncomputable def PtvSigma : V := ⌜Semiformula.lMap emb (↑(isSemitermVec LAct).sigma : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PtvSigma : IsSemiformula LAct ((3 : ℕ) : V) PtvSigma := Sentence.quote_isSemiformula _
lemma shift_PtvSigma : shift LAct (PtvSigma : V) = PtvSigma := shift_quote_sentence _
lemma fvOccF_PtvSigma : fvOccF LAct (PtvSigma : V) = 0 := fvOccF_quote_sentence _

/-- The code of `utvpi` (arity 2). -/
noncomputable def PutvPi : V := ⌜Semiformula.lMap emb (↑(isUTermVec LAct).pi : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PutvPi : IsSemiformula LAct ((2 : ℕ) : V) PutvPi := Sentence.quote_isSemiformula _
lemma shift_PutvPi : shift LAct (PutvPi : V) = PutvPi := shift_quote_sentence _
lemma fvOccF_PutvPi : fvOccF LAct (PutvPi : V) = 0 := fvOccF_quote_sentence _

/-- The code of `utvsigma` (arity 2). -/
noncomputable def PutvSigma : V := ⌜Semiformula.lMap emb (↑(isUTermVec LAct).sigma : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PutvSigma : IsSemiformula LAct ((2 : ℕ) : V) PutvSigma := Sentence.quote_isSemiformula _
lemma shift_PutvSigma : shift LAct (PutvSigma : V) = PutvSigma := shift_quote_sentence _
lemma fvOccF_PutvSigma : fvOccF LAct (PutvSigma : V) = 0 := fvOccF_quote_sentence _

/-- The code of `isRel` (arity 2). -/
noncomputable def PisRel : V := ⌜Semiformula.lMap emb (↑LAct.isRel : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PisRel : IsSemiformula LAct ((2 : ℕ) : V) PisRel := Sentence.quote_isSemiformula _
lemma shift_PisRel : shift LAct (PisRel : V) = PisRel := shift_quote_sentence _
lemma fvOccF_PisRel : fvOccF LAct (PisRel : V) = 0 := fvOccF_quote_sentence _

/-- The code of `isFunc` (arity 2). -/
noncomputable def PisFunc : V := ⌜Semiformula.lMap emb (↑LAct.isFunc : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PisFunc : IsSemiformula LAct ((2 : ℕ) : V) PisFunc := Sentence.quote_isSemiformula _
lemma shift_PisFunc : shift LAct (PisFunc : V) = PisFunc := shift_quote_sentence _
lemma fvOccF_PisFunc : fvOccF LAct (PisFunc : V) = 0 := fvOccF_quote_sentence _

/-- The code of `lt` (arity 2). -/
noncomputable def Plt : V := ⌜Semiformula.lMap emb (Rewriting.emb (Semiformula.Operator.LT.lt : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Plt : IsSemiformula LAct ((2 : ℕ) : V) Plt := Sentence.quote_isSemiformula _
lemma shift_Plt : shift LAct (Plt : V) = Plt := shift_quote_sentence _
lemma fvOccF_Plt : fvOccF LAct (Plt : V) = 0 := fvOccF_quote_sentence _

/-- The code of `negG` (arity 2). -/
noncomputable def PnegG : V := ⌜Semiformula.lMap emb (↑(negGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PnegG : IsSemiformula LAct ((2 : ℕ) : V) PnegG := Sentence.quote_isSemiformula _
lemma shift_PnegG : shift LAct (PnegG : V) = PnegG := shift_quote_sentence _
lemma fvOccF_PnegG : fvOccF LAct (PnegG : V) = 0 := fvOccF_quote_sentence _

/-- The code of `shiftG` (arity 2). -/
noncomputable def PshiftG : V := ⌜Semiformula.lMap emb (↑(shiftGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PshiftG : IsSemiformula LAct ((2 : ℕ) : V) PshiftG := Sentence.quote_isSemiformula _
lemma shift_PshiftG : shift LAct (PshiftG : V) = PshiftG := shift_quote_sentence _
lemma fvOccF_PshiftG : fvOccF LAct (PshiftG : V) = 0 := fvOccF_quote_sentence _

/-- The code of `substsG` (arity 3). -/
noncomputable def PsubstsG : V := ⌜Semiformula.lMap emb (↑(substsGraph LAct) : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PsubstsG : IsSemiformula LAct ((3 : ℕ) : V) PsubstsG := Sentence.quote_isSemiformula _
lemma shift_PsubstsG : shift LAct (PsubstsG : V) = PsubstsG := shift_quote_sentence _
lemma fvOccF_PsubstsG : fvOccF LAct (PsubstsG : V) = 0 := fvOccF_quote_sentence _

/-- The code of `substs1G` (arity 3). -/
noncomputable def Psubsts1G : V := ⌜Semiformula.lMap emb (↑(substs1Graph LAct) : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Psubsts1G : IsSemiformula LAct ((3 : ℕ) : V) Psubsts1G := Sentence.quote_isSemiformula _
lemma shift_Psubsts1G : shift LAct (Psubsts1G : V) = Psubsts1G := shift_quote_sentence _
lemma fvOccF_Psubsts1G : fvOccF LAct (Psubsts1G : V) = 0 := fvOccF_quote_sentence _

/-- The code of `freeG` (arity 2). -/
noncomputable def PfreeG : V := ⌜Semiformula.lMap emb (↑(freeGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PfreeG : IsSemiformula LAct ((2 : ℕ) : V) PfreeG := Sentence.quote_isSemiformula _
lemma shift_PfreeG : shift LAct (PfreeG : V) = PfreeG := shift_quote_sentence _
lemma fvOccF_PfreeG : fvOccF LAct (PfreeG : V) = 0 := fvOccF_quote_sentence _

/-- The code of `qVecG` (arity 2). -/
noncomputable def PqVecG : V := ⌜Semiformula.lMap emb (↑(qVecGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PqVecG : IsSemiformula LAct ((2 : ℕ) : V) PqVecG := Sentence.quote_isSemiformula _
lemma shift_PqVecG : shift LAct (PqVecG : V) = PqVecG := shift_quote_sentence _
lemma fvOccF_PqVecG : fvOccF LAct (PqVecG : V) = 0 := fvOccF_quote_sentence _

/-- The code of `tsvG` (arity 4). -/
noncomputable def PtsvG : V := ⌜Semiformula.lMap emb (↑(termSubstVecGraph LAct) : ArithmeticSemisentence 4)⌝
lemma isSemiformula_PtsvG : IsSemiformula LAct ((4 : ℕ) : V) PtsvG := Sentence.quote_isSemiformula _
lemma shift_PtsvG : shift LAct (PtsvG : V) = PtsvG := shift_quote_sentence _
lemma fvOccF_PtsvG : fvOccF LAct (PtsvG : V) = 0 := fvOccF_quote_sentence _

/-- The code of `tshvG` (arity 3). -/
noncomputable def PtshvG : V := ⌜Semiformula.lMap emb (↑(termShiftVecGraph LAct) : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PtshvG : IsSemiformula LAct ((3 : ℕ) : V) PtshvG := Sentence.quote_isSemiformula _
lemma shift_PtshvG : shift LAct (PtshvG : V) = PtshvG := shift_quote_sentence _
lemma fvOccF_PtshvG : fvOccF LAct (PtshvG : V) = 0 := fvOccF_quote_sentence _

/-! ### The facts: `subst (listToVec [witnesses]) P` in the predicate's own variable order -/

lemma formulaLen_piFact_le {B : V} (hB : 1 ≤ B) {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) (hln : termLen LAct n ≤ B) (hla : termLen LAct a ≤ B) :
    formulaLen LAct (piFact n a) ≤ formulaLen LAct (Ppi : V) * B :=
  formulaLen_fact_le hB isSemiformula_Ppi _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hln⟩, List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_piFact_le {M : V} {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) (hon : fvOcc LAct n ≤ M) (hoa : fvOcc LAct a ≤ M) :
    fvOccF LAct (piFact n a) ≤ bvOccF LAct (Ppi : V) * M :=
  fvOccF_fact_le isSemiformula_Ppi fvOccF_Ppi _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hon⟩, List.forall_mem_cons.mpr ⟨⟨ha, hoa⟩, List.forall_mem_nil _⟩⟩)

lemma shift_sigmaFact {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) :
    shift LAct (sigmaFact n a) = sigmaFact (termShift LAct n) (termShift LAct a) := by
  unfold sigmaFact
  rw [shift_subst_listToVec [n, a] isSemiformula_Psigma shift_Psigma (n := 0) (List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨ha, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_sigmaFact_le {B : V} (hB : 1 ≤ B) {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) (hln : termLen LAct n ≤ B) (hla : termLen LAct a ≤ B) :
    formulaLen LAct (sigmaFact n a) ≤ formulaLen LAct (Psigma : V) * B :=
  formulaLen_fact_le hB isSemiformula_Psigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hln⟩, List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_sigmaFact_le {M : V} {n a : V} (hn : IsSemiterm LAct 0 n) (ha : IsSemiterm LAct 0 a) (hon : fvOcc LAct n ≤ M) (hoa : fvOcc LAct a ≤ M) :
    fvOccF LAct (sigmaFact n a) ≤ bvOccF LAct (Psigma : V) * M :=
  fvOccF_fact_le isSemiformula_Psigma fvOccF_Psigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hon⟩, List.forall_mem_cons.mpr ⟨⟨ha, hoa⟩, List.forall_mem_nil _⟩⟩)

lemma shift_andFact {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    shift LAct (andFact z a b) = andFact (termShift LAct z) (termShift LAct a) (termShift LAct b) := by
  unfold andFact
  rw [shift_subst_listToVec [z, a, b] isSemiformula_Pand shift_Pand (n := 0) (List.forall_mem_cons.mpr ⟨hz, List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_andFact_le {B : V} (hB : 1 ≤ B) {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hlz : termLen LAct z ≤ B) (hla : termLen LAct a ≤ B) (hlb : termLen LAct b ≤ B) :
    formulaLen LAct (andFact z a b) ≤ formulaLen LAct (Pand : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pand _ rfl (List.forall_mem_cons.mpr ⟨⟨hz, hlz⟩, List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_cons.mpr ⟨⟨hb, hlb⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_andFact_le {M : V} {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hoz : fvOcc LAct z ≤ M) (hoa : fvOcc LAct a ≤ M) (hob : fvOcc LAct b ≤ M) :
    fvOccF LAct (andFact z a b) ≤ bvOccF LAct (Pand : V) * M :=
  fvOccF_fact_le isSemiformula_Pand fvOccF_Pand _ rfl (List.forall_mem_cons.mpr ⟨⟨hz, hoz⟩, List.forall_mem_cons.mpr ⟨⟨ha, hoa⟩, List.forall_mem_cons.mpr ⟨⟨hb, hob⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def orFact (z a b : V) : V := subst LAct (listToVec [z, a, b]) Por
lemma isFormula_orFact {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) : IsFormula LAct (orFact z a b) :=
  isFormula_fact isSemiformula_Por _ rfl (List.forall_mem_cons.mpr ⟨hz, List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩⟩)
lemma shift_orFact {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    shift LAct (orFact z a b) = orFact (termShift LAct z) (termShift LAct a) (termShift LAct b) := by
  unfold orFact
  rw [shift_subst_listToVec [z, a, b] isSemiformula_Por shift_Por (n := 0) (List.forall_mem_cons.mpr ⟨hz, List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_orFact_le {B : V} (hB : 1 ≤ B) {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hlz : termLen LAct z ≤ B) (hla : termLen LAct a ≤ B) (hlb : termLen LAct b ≤ B) :
    formulaLen LAct (orFact z a b) ≤ formulaLen LAct (Por : V) * B :=
  formulaLen_fact_le hB isSemiformula_Por _ rfl (List.forall_mem_cons.mpr ⟨⟨hz, hlz⟩, List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_cons.mpr ⟨⟨hb, hlb⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_orFact_le {M : V} {z a b : V} (hz : IsSemiterm LAct 0 z) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hoz : fvOcc LAct z ≤ M) (hoa : fvOcc LAct a ≤ M) (hob : fvOcc LAct b ≤ M) :
    fvOccF LAct (orFact z a b) ≤ bvOccF LAct (Por : V) * M :=
  fvOccF_fact_le isSemiformula_Por fvOccF_Por _ rfl (List.forall_mem_cons.mpr ⟨⟨hz, hoz⟩, List.forall_mem_cons.mpr ⟨⟨ha, hoa⟩, List.forall_mem_cons.mpr ⟨⟨hb, hob⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def allFact (q p : V) : V := subst LAct (listToVec [q, p]) Pall
lemma isFormula_allFact {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (allFact q p) :=
  isFormula_fact isSemiformula_Pall _ rfl (List.forall_mem_cons.mpr ⟨hq, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)
lemma shift_allFact {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) :
    shift LAct (allFact q p) = allFact (termShift LAct q) (termShift LAct p) := by
  unfold allFact
  rw [shift_subst_listToVec [q, p] isSemiformula_Pall shift_Pall (n := 0) (List.forall_mem_cons.mpr ⟨hq, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_allFact_le {B : V} (hB : 1 ≤ B) {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) (hlq : termLen LAct q ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (allFact q p) ≤ formulaLen LAct (Pall : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pall _ rfl (List.forall_mem_cons.mpr ⟨⟨hq, hlq⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_allFact_le {M : V} {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) (hoq : fvOcc LAct q ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (allFact q p) ≤ bvOccF LAct (Pall : V) * M :=
  fvOccF_fact_le isSemiformula_Pall fvOccF_Pall _ rfl (List.forall_mem_cons.mpr ⟨⟨hq, hoq⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩)

noncomputable def exsFact (q p : V) : V := subst LAct (listToVec [q, p]) Pexs
lemma isFormula_exsFact {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (exsFact q p) :=
  isFormula_fact isSemiformula_Pexs _ rfl (List.forall_mem_cons.mpr ⟨hq, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)
lemma shift_exsFact {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) :
    shift LAct (exsFact q p) = exsFact (termShift LAct q) (termShift LAct p) := by
  unfold exsFact
  rw [shift_subst_listToVec [q, p] isSemiformula_Pexs shift_Pexs (n := 0) (List.forall_mem_cons.mpr ⟨hq, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_exsFact_le {B : V} (hB : 1 ≤ B) {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) (hlq : termLen LAct q ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (exsFact q p) ≤ formulaLen LAct (Pexs : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pexs _ rfl (List.forall_mem_cons.mpr ⟨⟨hq, hlq⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_exsFact_le {M : V} {q p : V} (hq : IsSemiterm LAct 0 q) (hp : IsSemiterm LAct 0 p) (hoq : fvOcc LAct q ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (exsFact q p) ≤ bvOccF LAct (Pexs : V) * M :=
  fvOccF_fact_le isSemiformula_Pexs fvOccF_Pexs _ rfl (List.forall_mem_cons.mpr ⟨⟨hq, hoq⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩)

noncomputable def relFact (p k R v : V) : V := subst LAct (listToVec [p, k, R, v]) Prel
lemma isFormula_relFact {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (relFact p k R v) :=
  isFormula_fact isSemiformula_Prel _ rfl (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hR, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)
lemma shift_relFact {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) :
    shift LAct (relFact p k R v) = relFact (termShift LAct p) (termShift LAct k) (termShift LAct R) (termShift LAct v) := by
  unfold relFact
  rw [shift_subst_listToVec [p, k, R, v] isSemiformula_Prel shift_Prel (n := 0) (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hR, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)]
  rfl
lemma formulaLen_relFact_le {B : V} (hB : 1 ≤ B) {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) (hlp : termLen LAct p ≤ B) (hlk : termLen LAct k ≤ B) (hlR : termLen LAct R ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (relFact p k R v) ≤ formulaLen LAct (Prel : V) * B :=
  formulaLen_fact_le hB isSemiformula_Prel _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hR, hlR⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩⟩)
lemma fvOccF_relFact_le {M : V} {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) (hop : fvOcc LAct p ≤ M) (hok : fvOcc LAct k ≤ M) (hoR : fvOcc LAct R ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (relFact p k R v) ≤ bvOccF LAct (Prel : V) * M :=
  fvOccF_fact_le isSemiformula_Prel fvOccF_Prel _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hR, hoR⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩⟩)

noncomputable def nrelFact (p k R v : V) : V := subst LAct (listToVec [p, k, R, v]) Pnrel
lemma isFormula_nrelFact {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (nrelFact p k R v) :=
  isFormula_fact isSemiformula_Pnrel _ rfl (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hR, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)
lemma shift_nrelFact {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) :
    shift LAct (nrelFact p k R v) = nrelFact (termShift LAct p) (termShift LAct k) (termShift LAct R) (termShift LAct v) := by
  unfold nrelFact
  rw [shift_subst_listToVec [p, k, R, v] isSemiformula_Pnrel shift_Pnrel (n := 0) (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hR, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)]
  rfl
lemma formulaLen_nrelFact_le {B : V} (hB : 1 ≤ B) {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) (hlp : termLen LAct p ≤ B) (hlk : termLen LAct k ≤ B) (hlR : termLen LAct R ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (nrelFact p k R v) ≤ formulaLen LAct (Pnrel : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pnrel _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hR, hlR⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩⟩)
lemma fvOccF_nrelFact_le {M : V} {p k R v : V} (hp : IsSemiterm LAct 0 p) (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hv : IsSemiterm LAct 0 v) (hop : fvOcc LAct p ≤ M) (hok : fvOcc LAct k ≤ M) (hoR : fvOcc LAct R ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (nrelFact p k R v) ≤ bvOccF LAct (Pnrel : V) * M :=
  fvOccF_fact_le isSemiformula_Pnrel fvOccF_Pnrel _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hR, hoR⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩⟩)

noncomputable def verumFact (p : V) : V := subst LAct (listToVec [p]) Pverum
lemma isFormula_verumFact {p : V} (hp : IsSemiterm LAct 0 p) : IsFormula LAct (verumFact p) :=
  isFormula_fact isSemiformula_Pverum _ rfl (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩)
lemma shift_verumFact {p : V} (hp : IsSemiterm LAct 0 p) :
    shift LAct (verumFact p) = verumFact (termShift LAct p) := by
  unfold verumFact
  rw [shift_subst_listToVec [p] isSemiformula_Pverum shift_Pverum (n := 0) (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩)]
  rfl
lemma formulaLen_verumFact_le {B : V} (hB : 1 ≤ B) {p : V} (hp : IsSemiterm LAct 0 p) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (verumFact p) ≤ formulaLen LAct (Pverum : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pverum _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩)
lemma fvOccF_verumFact_le {M : V} {p : V} (hp : IsSemiterm LAct 0 p) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (verumFact p) ≤ bvOccF LAct (Pverum : V) * M :=
  fvOccF_fact_le isSemiformula_Pverum fvOccF_Pverum _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩)

noncomputable def falsumFact (p : V) : V := subst LAct (listToVec [p]) Pfalsum
lemma isFormula_falsumFact {p : V} (hp : IsSemiterm LAct 0 p) : IsFormula LAct (falsumFact p) :=
  isFormula_fact isSemiformula_Pfalsum _ rfl (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩)
lemma shift_falsumFact {p : V} (hp : IsSemiterm LAct 0 p) :
    shift LAct (falsumFact p) = falsumFact (termShift LAct p) := by
  unfold falsumFact
  rw [shift_subst_listToVec [p] isSemiformula_Pfalsum shift_Pfalsum (n := 0) (List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩)]
  rfl
lemma formulaLen_falsumFact_le {B : V} (hB : 1 ≤ B) {p : V} (hp : IsSemiterm LAct 0 p) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (falsumFact p) ≤ formulaLen LAct (Pfalsum : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pfalsum _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩)
lemma fvOccF_falsumFact_le {M : V} {p : V} (hp : IsSemiterm LAct 0 p) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (falsumFact p) ≤ bvOccF LAct (Pfalsum : V) * M :=
  fvOccF_fact_le isSemiformula_Pfalsum fvOccF_Pfalsum _ rfl (List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩)

noncomputable def funcFact (t k f v : V) : V := subst LAct (listToVec [t, k, f, v]) Pfunc
lemma isFormula_funcFact {t k f v : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (funcFact t k f v) :=
  isFormula_fact isSemiformula_Pfunc _ rfl (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hf, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)
lemma shift_funcFact {t k f v : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hv : IsSemiterm LAct 0 v) :
    shift LAct (funcFact t k f v) = funcFact (termShift LAct t) (termShift LAct k) (termShift LAct f) (termShift LAct v) := by
  unfold funcFact
  rw [shift_subst_listToVec [t, k, f, v] isSemiformula_Pfunc shift_Pfunc (n := 0) (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hf, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)]
  rfl
lemma formulaLen_funcFact_le {B : V} (hB : 1 ≤ B) {t k f v : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hv : IsSemiterm LAct 0 v) (hlt : termLen LAct t ≤ B) (hlk : termLen LAct k ≤ B) (hlf : termLen LAct f ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (funcFact t k f v) ≤ formulaLen LAct (Pfunc : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pfunc _ rfl (List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hf, hlf⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩⟩)
lemma fvOccF_funcFact_le {M : V} {t k f v : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hv : IsSemiterm LAct 0 v) (hot : fvOcc LAct t ≤ M) (hok : fvOcc LAct k ≤ M) (hof : fvOcc LAct f ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (funcFact t k f v) ≤ bvOccF LAct (Pfunc : V) * M :=
  fvOccF_fact_le isSemiformula_Pfunc fvOccF_Pfunc _ rfl (List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hf, hof⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩⟩)

noncomputable def bvarFact (t z : V) : V := subst LAct (listToVec [t, z]) Pbvar
lemma isFormula_bvarFact {t z : V} (ht : IsSemiterm LAct 0 t) (hz : IsSemiterm LAct 0 z) : IsFormula LAct (bvarFact t z) :=
  isFormula_fact isSemiformula_Pbvar _ rfl (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hz, List.forall_mem_nil _⟩⟩)
lemma shift_bvarFact {t z : V} (ht : IsSemiterm LAct 0 t) (hz : IsSemiterm LAct 0 z) :
    shift LAct (bvarFact t z) = bvarFact (termShift LAct t) (termShift LAct z) := by
  unfold bvarFact
  rw [shift_subst_listToVec [t, z] isSemiformula_Pbvar shift_Pbvar (n := 0) (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hz, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_bvarFact_le {B : V} (hB : 1 ≤ B) {t z : V} (ht : IsSemiterm LAct 0 t) (hz : IsSemiterm LAct 0 z) (hlt : termLen LAct t ≤ B) (hlz : termLen LAct z ≤ B) :
    formulaLen LAct (bvarFact t z) ≤ formulaLen LAct (Pbvar : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pbvar _ rfl (List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_cons.mpr ⟨⟨hz, hlz⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_bvarFact_le {M : V} {t z : V} (ht : IsSemiterm LAct 0 t) (hz : IsSemiterm LAct 0 z) (hot : fvOcc LAct t ≤ M) (hoz : fvOcc LAct z ≤ M) :
    fvOccF LAct (bvarFact t z) ≤ bvOccF LAct (Pbvar : V) * M :=
  fvOccF_fact_le isSemiformula_Pbvar fvOccF_Pbvar _ rfl (List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_cons.mpr ⟨⟨hz, hoz⟩, List.forall_mem_nil _⟩⟩)

noncomputable def fvarFact (t x : V) : V := subst LAct (listToVec [t, x]) Pfvar
lemma isFormula_fvarFact {t x : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) : IsFormula LAct (fvarFact t x) :=
  isFormula_fact isSemiformula_Pfvar _ rfl (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hx, List.forall_mem_nil _⟩⟩)
lemma shift_fvarFact {t x : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) :
    shift LAct (fvarFact t x) = fvarFact (termShift LAct t) (termShift LAct x) := by
  unfold fvarFact
  rw [shift_subst_listToVec [t, x] isSemiformula_Pfvar shift_Pfvar (n := 0) (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hx, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_fvarFact_le {B : V} (hB : 1 ≤ B) {t x : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) (hlt : termLen LAct t ≤ B) (hlx : termLen LAct x ≤ B) :
    formulaLen LAct (fvarFact t x) ≤ formulaLen LAct (Pfvar : V) * B :=
  formulaLen_fact_le hB isSemiformula_Pfvar _ rfl (List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_cons.mpr ⟨⟨hx, hlx⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_fvarFact_le {M : V} {t x : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) (hot : fvOcc LAct t ≤ M) (hox : fvOcc LAct x ≤ M) :
    fvOccF LAct (fvarFact t x) ≤ bvOccF LAct (Pfvar : V) * M :=
  fvOccF_fact_le isSemiformula_Pfvar fvOccF_Pfvar _ rfl (List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_cons.mpr ⟨⟨hx, hox⟩, List.forall_mem_nil _⟩⟩)

noncomputable def adjFact (w t v : V) : V := subst LAct (listToVec [w, t, v]) Padjoin
lemma isFormula_adjFact {w t v : V} (hw : IsSemiterm LAct 0 w) (ht : IsSemiterm LAct 0 t) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (adjFact w t v) :=
  isFormula_fact isSemiformula_Padjoin _ rfl (List.forall_mem_cons.mpr ⟨hw, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)
lemma shift_adjFact {w t v : V} (hw : IsSemiterm LAct 0 w) (ht : IsSemiterm LAct 0 t) (hv : IsSemiterm LAct 0 v) :
    shift LAct (adjFact w t v) = adjFact (termShift LAct w) (termShift LAct t) (termShift LAct v) := by
  unfold adjFact
  rw [shift_subst_listToVec [w, t, v] isSemiformula_Padjoin shift_Padjoin (n := 0) (List.forall_mem_cons.mpr ⟨hw, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_adjFact_le {B : V} (hB : 1 ≤ B) {w t v : V} (hw : IsSemiterm LAct 0 w) (ht : IsSemiterm LAct 0 t) (hv : IsSemiterm LAct 0 v) (hlw : termLen LAct w ≤ B) (hlt : termLen LAct t ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (adjFact w t v) ≤ formulaLen LAct (Padjoin : V) * B :=
  formulaLen_fact_le hB isSemiformula_Padjoin _ rfl (List.forall_mem_cons.mpr ⟨⟨hw, hlw⟩, List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_adjFact_le {M : V} {w t v : V} (hw : IsSemiterm LAct 0 w) (ht : IsSemiterm LAct 0 t) (hv : IsSemiterm LAct 0 v) (how : fvOcc LAct w ≤ M) (hot : fvOcc LAct t ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (adjFact w t v) ≤ bvOccF LAct (Padjoin : V) * M :=
  fvOccF_fact_le isSemiformula_Padjoin fvOccF_Padjoin _ rfl (List.forall_mem_cons.mpr ⟨⟨hw, how⟩, List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def tPiFact (n t : V) : V := subst LAct (listToVec [n, t]) PtPi
lemma isFormula_tPiFact {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) : IsFormula LAct (tPiFact n t) :=
  isFormula_fact isSemiformula_PtPi _ rfl (List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)
lemma shift_tPiFact {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) :
    shift LAct (tPiFact n t) = tPiFact (termShift LAct n) (termShift LAct t) := by
  unfold tPiFact
  rw [shift_subst_listToVec [n, t] isSemiformula_PtPi shift_PtPi (n := 0) (List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_tPiFact_le {B : V} (hB : 1 ≤ B) {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) (hln : termLen LAct n ≤ B) (hlt : termLen LAct t ≤ B) :
    formulaLen LAct (tPiFact n t) ≤ formulaLen LAct (PtPi : V) * B :=
  formulaLen_fact_le hB isSemiformula_PtPi _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hln⟩, List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_tPiFact_le {M : V} {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) (hon : fvOcc LAct n ≤ M) (hot : fvOcc LAct t ≤ M) :
    fvOccF LAct (tPiFact n t) ≤ bvOccF LAct (PtPi : V) * M :=
  fvOccF_fact_le isSemiformula_PtPi fvOccF_PtPi _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hon⟩, List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_nil _⟩⟩)

noncomputable def tSigmaFact (n t : V) : V := subst LAct (listToVec [n, t]) PtSigma
lemma isFormula_tSigmaFact {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) : IsFormula LAct (tSigmaFact n t) :=
  isFormula_fact isSemiformula_PtSigma _ rfl (List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)
lemma shift_tSigmaFact {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) :
    shift LAct (tSigmaFact n t) = tSigmaFact (termShift LAct n) (termShift LAct t) := by
  unfold tSigmaFact
  rw [shift_subst_listToVec [n, t] isSemiformula_PtSigma shift_PtSigma (n := 0) (List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_tSigmaFact_le {B : V} (hB : 1 ≤ B) {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) (hln : termLen LAct n ≤ B) (hlt : termLen LAct t ≤ B) :
    formulaLen LAct (tSigmaFact n t) ≤ formulaLen LAct (PtSigma : V) * B :=
  formulaLen_fact_le hB isSemiformula_PtSigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hln⟩, List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_tSigmaFact_le {M : V} {n t : V} (hn : IsSemiterm LAct 0 n) (ht : IsSemiterm LAct 0 t) (hon : fvOcc LAct n ≤ M) (hot : fvOcc LAct t ≤ M) :
    fvOccF LAct (tSigmaFact n t) ≤ bvOccF LAct (PtSigma : V) * M :=
  fvOccF_fact_le isSemiformula_PtSigma fvOccF_PtSigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hn, hon⟩, List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_nil _⟩⟩)

noncomputable def tvPiFact (k n v : V) : V := subst LAct (listToVec [k, n, v]) PtvPi
lemma isFormula_tvPiFact {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (tvPiFact k n v) :=
  isFormula_fact isSemiformula_PtvPi _ rfl (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)
lemma shift_tvPiFact {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) :
    shift LAct (tvPiFact k n v) = tvPiFact (termShift LAct k) (termShift LAct n) (termShift LAct v) := by
  unfold tvPiFact
  rw [shift_subst_listToVec [k, n, v] isSemiformula_PtvPi shift_PtvPi (n := 0) (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_tvPiFact_le {B : V} (hB : 1 ≤ B) {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) (hlk : termLen LAct k ≤ B) (hln : termLen LAct n ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (tvPiFact k n v) ≤ formulaLen LAct (PtvPi : V) * B :=
  formulaLen_fact_le hB isSemiformula_PtvPi _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hn, hln⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_tvPiFact_le {M : V} {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) (hok : fvOcc LAct k ≤ M) (hon : fvOcc LAct n ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (tvPiFact k n v) ≤ bvOccF LAct (PtvPi : V) * M :=
  fvOccF_fact_le isSemiformula_PtvPi fvOccF_PtvPi _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hn, hon⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def tvSigmaFact (k n v : V) : V := subst LAct (listToVec [k, n, v]) PtvSigma
lemma isFormula_tvSigmaFact {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (tvSigmaFact k n v) :=
  isFormula_fact isSemiformula_PtvSigma _ rfl (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)
lemma shift_tvSigmaFact {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) :
    shift LAct (tvSigmaFact k n v) = tvSigmaFact (termShift LAct k) (termShift LAct n) (termShift LAct v) := by
  unfold tvSigmaFact
  rw [shift_subst_listToVec [k, n, v] isSemiformula_PtvSigma shift_PtvSigma (n := 0) (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_tvSigmaFact_le {B : V} (hB : 1 ≤ B) {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) (hlk : termLen LAct k ≤ B) (hln : termLen LAct n ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (tvSigmaFact k n v) ≤ formulaLen LAct (PtvSigma : V) * B :=
  formulaLen_fact_le hB isSemiformula_PtvSigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hn, hln⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_tvSigmaFact_le {M : V} {k n v : V} (hk : IsSemiterm LAct 0 k) (hn : IsSemiterm LAct 0 n) (hv : IsSemiterm LAct 0 v) (hok : fvOcc LAct k ≤ M) (hon : fvOcc LAct n ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (tvSigmaFact k n v) ≤ bvOccF LAct (PtvSigma : V) * M :=
  fvOccF_fact_le isSemiformula_PtvSigma fvOccF_PtvSigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hn, hon⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def utvPiFact (k v : V) : V := subst LAct (listToVec [k, v]) PutvPi
lemma isFormula_utvPiFact {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (utvPiFact k v) :=
  isFormula_fact isSemiformula_PutvPi _ rfl (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩)
lemma shift_utvPiFact {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    shift LAct (utvPiFact k v) = utvPiFact (termShift LAct k) (termShift LAct v) := by
  unfold utvPiFact
  rw [shift_subst_listToVec [k, v] isSemiformula_PutvPi shift_PutvPi (n := 0) (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_utvPiFact_le {B : V} (hB : 1 ≤ B) {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) (hlk : termLen LAct k ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (utvPiFact k v) ≤ formulaLen LAct (PutvPi : V) * B :=
  formulaLen_fact_le hB isSemiformula_PutvPi _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_utvPiFact_le {M : V} {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) (hok : fvOcc LAct k ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (utvPiFact k v) ≤ bvOccF LAct (PutvPi : V) * M :=
  fvOccF_fact_le isSemiformula_PutvPi fvOccF_PutvPi _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩)

noncomputable def utvSigmaFact (k v : V) : V := subst LAct (listToVec [k, v]) PutvSigma
lemma isFormula_utvSigmaFact {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (utvSigmaFact k v) :=
  isFormula_fact isSemiformula_PutvSigma _ rfl (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩)
lemma shift_utvSigmaFact {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    shift LAct (utvSigmaFact k v) = utvSigmaFact (termShift LAct k) (termShift LAct v) := by
  unfold utvSigmaFact
  rw [shift_subst_listToVec [k, v] isSemiformula_PutvSigma shift_PutvSigma (n := 0) (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_utvSigmaFact_le {B : V} (hB : 1 ≤ B) {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) (hlk : termLen LAct k ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (utvSigmaFact k v) ≤ formulaLen LAct (PutvSigma : V) * B :=
  formulaLen_fact_le hB isSemiformula_PutvSigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_utvSigmaFact_le {M : V} {k v : V} (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) (hok : fvOcc LAct k ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (utvSigmaFact k v) ≤ bvOccF LAct (PutvSigma : V) * M :=
  fvOccF_fact_le isSemiformula_PutvSigma fvOccF_PutvSigma _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩)

noncomputable def isRelFact (k R : V) : V := subst LAct (listToVec [k, R]) PisRel
lemma isFormula_isRelFact {k R : V} (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) : IsFormula LAct (isRelFact k R) :=
  isFormula_fact isSemiformula_PisRel _ rfl (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hR, List.forall_mem_nil _⟩⟩)
lemma shift_isRelFact {k R : V} (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) :
    shift LAct (isRelFact k R) = isRelFact (termShift LAct k) (termShift LAct R) := by
  unfold isRelFact
  rw [shift_subst_listToVec [k, R] isSemiformula_PisRel shift_PisRel (n := 0) (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hR, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_isRelFact_le {B : V} (hB : 1 ≤ B) {k R : V} (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hlk : termLen LAct k ≤ B) (hlR : termLen LAct R ≤ B) :
    formulaLen LAct (isRelFact k R) ≤ formulaLen LAct (PisRel : V) * B :=
  formulaLen_fact_le hB isSemiformula_PisRel _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hR, hlR⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_isRelFact_le {M : V} {k R : V} (hk : IsSemiterm LAct 0 k) (hR : IsSemiterm LAct 0 R) (hok : fvOcc LAct k ≤ M) (hoR : fvOcc LAct R ≤ M) :
    fvOccF LAct (isRelFact k R) ≤ bvOccF LAct (PisRel : V) * M :=
  fvOccF_fact_le isSemiformula_PisRel fvOccF_PisRel _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hR, hoR⟩, List.forall_mem_nil _⟩⟩)

noncomputable def isFuncFact (k f : V) : V := subst LAct (listToVec [k, f]) PisFunc
lemma isFormula_isFuncFact {k f : V} (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) : IsFormula LAct (isFuncFact k f) :=
  isFormula_fact isSemiformula_PisFunc _ rfl (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hf, List.forall_mem_nil _⟩⟩)
lemma shift_isFuncFact {k f : V} (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) :
    shift LAct (isFuncFact k f) = isFuncFact (termShift LAct k) (termShift LAct f) := by
  unfold isFuncFact
  rw [shift_subst_listToVec [k, f] isSemiformula_PisFunc shift_PisFunc (n := 0) (List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hf, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_isFuncFact_le {B : V} (hB : 1 ≤ B) {k f : V} (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hlk : termLen LAct k ≤ B) (hlf : termLen LAct f ≤ B) :
    formulaLen LAct (isFuncFact k f) ≤ formulaLen LAct (PisFunc : V) * B :=
  formulaLen_fact_le hB isSemiformula_PisFunc _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hf, hlf⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_isFuncFact_le {M : V} {k f : V} (hk : IsSemiterm LAct 0 k) (hf : IsSemiterm LAct 0 f) (hok : fvOcc LAct k ≤ M) (hof : fvOcc LAct f ≤ M) :
    fvOccF LAct (isFuncFact k f) ≤ bvOccF LAct (PisFunc : V) * M :=
  fvOccF_fact_le isSemiformula_PisFunc fvOccF_PisFunc _ rfl (List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hf, hof⟩, List.forall_mem_nil _⟩⟩)

noncomputable def ltFact (a b : V) : V := subst LAct (listToVec [a, b]) Plt
lemma isFormula_ltFact {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) : IsFormula LAct (ltFact a b) :=
  isFormula_fact isSemiformula_Plt _ rfl (List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩)
lemma shift_ltFact {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    shift LAct (ltFact a b) = ltFact (termShift LAct a) (termShift LAct b) := by
  unfold ltFact
  rw [shift_subst_listToVec [a, b] isSemiformula_Plt shift_Plt (n := 0) (List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_ltFact_le {B : V} (hB : 1 ≤ B) {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hla : termLen LAct a ≤ B) (hlb : termLen LAct b ≤ B) :
    formulaLen LAct (ltFact a b) ≤ formulaLen LAct (Plt : V) * B :=
  formulaLen_fact_le hB isSemiformula_Plt _ rfl (List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_cons.mpr ⟨⟨hb, hlb⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_ltFact_le {M : V} {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hoa : fvOcc LAct a ≤ M) (hob : fvOcc LAct b ≤ M) :
    fvOccF LAct (ltFact a b) ≤ bvOccF LAct (Plt : V) * M :=
  fvOccF_fact_le isSemiformula_Plt fvOccF_Plt _ rfl (List.forall_mem_cons.mpr ⟨⟨ha, hoa⟩, List.forall_mem_cons.mpr ⟨⟨hb, hob⟩, List.forall_mem_nil _⟩⟩)

noncomputable def negFact (y p : V) : V := subst LAct (listToVec [y, p]) PnegG
lemma isFormula_negFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (negFact y p) :=
  isFormula_fact isSemiformula_PnegG _ rfl (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)
lemma shift_negFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) :
    shift LAct (negFact y p) = negFact (termShift LAct y) (termShift LAct p) := by
  unfold negFact
  rw [shift_subst_listToVec [y, p] isSemiformula_PnegG shift_PnegG (n := 0) (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_negFact_le {B : V} (hB : 1 ≤ B) {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) (hly : termLen LAct y ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (negFact y p) ≤ formulaLen LAct (PnegG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PnegG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hly⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_negFact_le {M : V} {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) (hoy : fvOcc LAct y ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (negFact y p) ≤ bvOccF LAct (PnegG : V) * M :=
  fvOccF_fact_le isSemiformula_PnegG fvOccF_PnegG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hoy⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩)

noncomputable def shiftFact (y p : V) : V := subst LAct (listToVec [y, p]) PshiftG
lemma isFormula_shiftFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (shiftFact y p) :=
  isFormula_fact isSemiformula_PshiftG _ rfl (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)
lemma shift_shiftFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) :
    shift LAct (shiftFact y p) = shiftFact (termShift LAct y) (termShift LAct p) := by
  unfold shiftFact
  rw [shift_subst_listToVec [y, p] isSemiformula_PshiftG shift_PshiftG (n := 0) (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_shiftFact_le {B : V} (hB : 1 ≤ B) {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) (hly : termLen LAct y ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (shiftFact y p) ≤ formulaLen LAct (PshiftG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PshiftG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hly⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_shiftFact_le {M : V} {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) (hoy : fvOcc LAct y ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (shiftFact y p) ≤ bvOccF LAct (PshiftG : V) * M :=
  fvOccF_fact_le isSemiformula_PshiftG fvOccF_PshiftG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hoy⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩)

noncomputable def substFact (y w p : V) : V := subst LAct (listToVec [y, w, p]) PsubstsG
lemma isFormula_substFact {y w p : V} (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (substFact y w p) :=
  isFormula_fact isSemiformula_PsubstsG _ rfl (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hw, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩⟩)
lemma shift_substFact {y w p : V} (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w) (hp : IsSemiterm LAct 0 p) :
    shift LAct (substFact y w p) = substFact (termShift LAct y) (termShift LAct w) (termShift LAct p) := by
  unfold substFact
  rw [shift_subst_listToVec [y, w, p] isSemiformula_PsubstsG shift_PsubstsG (n := 0) (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hw, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_substFact_le {B : V} (hB : 1 ≤ B) {y w p : V} (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w) (hp : IsSemiterm LAct 0 p) (hly : termLen LAct y ≤ B) (hlw : termLen LAct w ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (substFact y w p) ≤ formulaLen LAct (PsubstsG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PsubstsG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hly⟩, List.forall_mem_cons.mpr ⟨⟨hw, hlw⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_substFact_le {M : V} {y w p : V} (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w) (hp : IsSemiterm LAct 0 p) (hoy : fvOcc LAct y ≤ M) (how : fvOcc LAct w ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (substFact y w p) ≤ bvOccF LAct (PsubstsG : V) * M :=
  fvOccF_fact_le isSemiformula_PsubstsG fvOccF_PsubstsG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hoy⟩, List.forall_mem_cons.mpr ⟨⟨hw, how⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def substs1Fact (y t p : V) : V := subst LAct (listToVec [y, t, p]) Psubsts1G
lemma isFormula_substs1Fact {y t p : V} (hy : IsSemiterm LAct 0 y) (ht : IsSemiterm LAct 0 t) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (substs1Fact y t p) :=
  isFormula_fact isSemiformula_Psubsts1G _ rfl (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩⟩)
lemma shift_substs1Fact {y t p : V} (hy : IsSemiterm LAct 0 y) (ht : IsSemiterm LAct 0 t) (hp : IsSemiterm LAct 0 p) :
    shift LAct (substs1Fact y t p) = substs1Fact (termShift LAct y) (termShift LAct t) (termShift LAct p) := by
  unfold substs1Fact
  rw [shift_subst_listToVec [y, t, p] isSemiformula_Psubsts1G shift_Psubsts1G (n := 0) (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_substs1Fact_le {B : V} (hB : 1 ≤ B) {y t p : V} (hy : IsSemiterm LAct 0 y) (ht : IsSemiterm LAct 0 t) (hp : IsSemiterm LAct 0 p) (hly : termLen LAct y ≤ B) (hlt : termLen LAct t ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (substs1Fact y t p) ≤ formulaLen LAct (Psubsts1G : V) * B :=
  formulaLen_fact_le hB isSemiformula_Psubsts1G _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hly⟩, List.forall_mem_cons.mpr ⟨⟨ht, hlt⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_substs1Fact_le {M : V} {y t p : V} (hy : IsSemiterm LAct 0 y) (ht : IsSemiterm LAct 0 t) (hp : IsSemiterm LAct 0 p) (hoy : fvOcc LAct y ≤ M) (hot : fvOcc LAct t ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (substs1Fact y t p) ≤ bvOccF LAct (Psubsts1G : V) * M :=
  fvOccF_fact_le isSemiformula_Psubsts1G fvOccF_Psubsts1G _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hoy⟩, List.forall_mem_cons.mpr ⟨⟨ht, hot⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩⟩)

noncomputable def freeFact (y p : V) : V := subst LAct (listToVec [y, p]) PfreeG
lemma isFormula_freeFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (freeFact y p) :=
  isFormula_fact isSemiformula_PfreeG _ rfl (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)
lemma shift_freeFact {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) :
    shift LAct (freeFact y p) = freeFact (termShift LAct y) (termShift LAct p) := by
  unfold freeFact
  rw [shift_subst_listToVec [y, p] isSemiformula_PfreeG shift_PfreeG (n := 0) (List.forall_mem_cons.mpr ⟨hy, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_freeFact_le {B : V} (hB : 1 ≤ B) {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) (hly : termLen LAct y ≤ B) (hlp : termLen LAct p ≤ B) :
    formulaLen LAct (freeFact y p) ≤ formulaLen LAct (PfreeG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PfreeG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hly⟩, List.forall_mem_cons.mpr ⟨⟨hp, hlp⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_freeFact_le {M : V} {y p : V} (hy : IsSemiterm LAct 0 y) (hp : IsSemiterm LAct 0 p) (hoy : fvOcc LAct y ≤ M) (hop : fvOcc LAct p ≤ M) :
    fvOccF LAct (freeFact y p) ≤ bvOccF LAct (PfreeG : V) * M :=
  fvOccF_fact_le isSemiformula_PfreeG fvOccF_PfreeG _ rfl (List.forall_mem_cons.mpr ⟨⟨hy, hoy⟩, List.forall_mem_cons.mpr ⟨⟨hp, hop⟩, List.forall_mem_nil _⟩⟩)

noncomputable def qVecFact (u w : V) : V := subst LAct (listToVec [u, w]) PqVecG
lemma isFormula_qVecFact {u w : V} (hu : IsSemiterm LAct 0 u) (hw : IsSemiterm LAct 0 w) : IsFormula LAct (qVecFact u w) :=
  isFormula_fact isSemiformula_PqVecG _ rfl (List.forall_mem_cons.mpr ⟨hu, List.forall_mem_cons.mpr ⟨hw, List.forall_mem_nil _⟩⟩)
lemma shift_qVecFact {u w : V} (hu : IsSemiterm LAct 0 u) (hw : IsSemiterm LAct 0 w) :
    shift LAct (qVecFact u w) = qVecFact (termShift LAct u) (termShift LAct w) := by
  unfold qVecFact
  rw [shift_subst_listToVec [u, w] isSemiformula_PqVecG shift_PqVecG (n := 0) (List.forall_mem_cons.mpr ⟨hu, List.forall_mem_cons.mpr ⟨hw, List.forall_mem_nil _⟩⟩)]
  rfl
lemma formulaLen_qVecFact_le {B : V} (hB : 1 ≤ B) {u w : V} (hu : IsSemiterm LAct 0 u) (hw : IsSemiterm LAct 0 w) (hlu : termLen LAct u ≤ B) (hlw : termLen LAct w ≤ B) :
    formulaLen LAct (qVecFact u w) ≤ formulaLen LAct (PqVecG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PqVecG _ rfl (List.forall_mem_cons.mpr ⟨⟨hu, hlu⟩, List.forall_mem_cons.mpr ⟨⟨hw, hlw⟩, List.forall_mem_nil _⟩⟩)
lemma fvOccF_qVecFact_le {M : V} {u w : V} (hu : IsSemiterm LAct 0 u) (hw : IsSemiterm LAct 0 w) (hou : fvOcc LAct u ≤ M) (how : fvOcc LAct w ≤ M) :
    fvOccF LAct (qVecFact u w) ≤ bvOccF LAct (PqVecG : V) * M :=
  fvOccF_fact_le isSemiformula_PqVecG fvOccF_PqVecG _ rfl (List.forall_mem_cons.mpr ⟨⟨hu, hou⟩, List.forall_mem_cons.mpr ⟨⟨hw, how⟩, List.forall_mem_nil _⟩⟩)

noncomputable def tsvFact (u k w v : V) : V := subst LAct (listToVec [u, k, w, v]) PtsvG
lemma isFormula_tsvFact {u k w v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hw : IsSemiterm LAct 0 w) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (tsvFact u k w v) :=
  isFormula_fact isSemiformula_PtsvG _ rfl (List.forall_mem_cons.mpr ⟨hu, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hw, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)
lemma shift_tsvFact {u k w v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hw : IsSemiterm LAct 0 w) (hv : IsSemiterm LAct 0 v) :
    shift LAct (tsvFact u k w v) = tsvFact (termShift LAct u) (termShift LAct k) (termShift LAct w) (termShift LAct v) := by
  unfold tsvFact
  rw [shift_subst_listToVec [u, k, w, v] isSemiformula_PtsvG shift_PtsvG (n := 0) (List.forall_mem_cons.mpr ⟨hu, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hw, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩⟩)]
  rfl
lemma formulaLen_tsvFact_le {B : V} (hB : 1 ≤ B) {u k w v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hw : IsSemiterm LAct 0 w) (hv : IsSemiterm LAct 0 v) (hlu : termLen LAct u ≤ B) (hlk : termLen LAct k ≤ B) (hlw : termLen LAct w ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (tsvFact u k w v) ≤ formulaLen LAct (PtsvG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PtsvG _ rfl (List.forall_mem_cons.mpr ⟨⟨hu, hlu⟩, List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hw, hlw⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩⟩)
lemma fvOccF_tsvFact_le {M : V} {u k w v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hw : IsSemiterm LAct 0 w) (hv : IsSemiterm LAct 0 v) (hou : fvOcc LAct u ≤ M) (hok : fvOcc LAct k ≤ M) (how : fvOcc LAct w ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (tsvFact u k w v) ≤ bvOccF LAct (PtsvG : V) * M :=
  fvOccF_fact_le isSemiformula_PtsvG fvOccF_PtsvG _ rfl (List.forall_mem_cons.mpr ⟨⟨hu, hou⟩, List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hw, how⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩⟩)

noncomputable def tshvFact (u k v : V) : V := subst LAct (listToVec [u, k, v]) PtshvG
lemma isFormula_tshvFact {u k v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (tshvFact u k v) :=
  isFormula_fact isSemiformula_PtshvG _ rfl (List.forall_mem_cons.mpr ⟨hu, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)
lemma shift_tshvFact {u k v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    shift LAct (tshvFact u k v) = tshvFact (termShift LAct u) (termShift LAct k) (termShift LAct v) := by
  unfold tshvFact
  rw [shift_subst_listToVec [u, k, v] isSemiformula_PtshvG shift_PtshvG (n := 0) (List.forall_mem_cons.mpr ⟨hu, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)]
  rfl
lemma formulaLen_tshvFact_le {B : V} (hB : 1 ≤ B) {u k v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) (hlu : termLen LAct u ≤ B) (hlk : termLen LAct k ≤ B) (hlv : termLen LAct v ≤ B) :
    formulaLen LAct (tshvFact u k v) ≤ formulaLen LAct (PtshvG : V) * B :=
  formulaLen_fact_le hB isSemiformula_PtshvG _ rfl (List.forall_mem_cons.mpr ⟨⟨hu, hlu⟩, List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_cons.mpr ⟨⟨hv, hlv⟩, List.forall_mem_nil _⟩⟩⟩)
lemma fvOccF_tshvFact_le {M : V} {u k v : V} (hu : IsSemiterm LAct 0 u) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) (hou : fvOcc LAct u ≤ M) (hok : fvOcc LAct k ≤ M) (hov : fvOcc LAct v ≤ M) :
    fvOccF LAct (tshvFact u k v) ≤ bvOccF LAct (PtshvG : V) * M :=
  fvOccF_fact_le isSemiformula_PtshvG fvOccF_PtshvG _ rfl (List.forall_mem_cons.mpr ⟨⟨hu, hou⟩, List.forall_mem_cons.mpr ⟨⟨hk, hok⟩, List.forall_mem_cons.mpr ⟨⟨hv, hov⟩, List.forall_mem_nil _⟩⟩⟩)

end facts

/-! ## 3. The rows: pieces, row-shape, formula-ness, instantiation -/

section rows

/-! ### `qqRelTotal` — `“v R k. …”`, `m = 3` -/

noncomputable def row_qqRelTotal_as : List V := []
noncomputable def row_qqRelTotal_body : V := subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Prel
noncomputable def row_qqRelTotal_R : V := row_qqRelTotal_body
noncomputable def row_qqRelTotal_c : V := ^∃ row_qqRelTotal_R

theorem quote_row_qqRelTotal : (⌜Semiformula.lMap emb qqRelTotalB⌝ : V) = impChain LAct row_qqRelTotal_as row_qqRelTotal_c := by
  unfold qqRelTotalB row_qqRelTotal_as row_qqRelTotal_c row_qqRelTotal_R row_qqRelTotal_body Prel
  all_goals row_shape

lemma isSemiformula_qqRelTotal_as : ∀ A ∈ row_qqRelTotal_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_qqRelTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqRelTotal_c : IsSemiformula LAct ((3 : ℕ) : V) row_qqRelTotal_c := by
  unfold row_qqRelTotal_c row_qqRelTotal_R row_qqRelTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries))
lemma isSemiformula_qqRelTotal_R : IsSemiformula LAct ((4 : ℕ) : V) row_qqRelTotal_R := by
  unfold row_qqRelTotal_R row_qqRelTotal_body
  exact isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)
lemma isSemiformula_qqRelTotal_body : IsSemiformula LAct ((4 : ℕ) : V) row_qqRelTotal_body := by
  unfold row_qqRelTotal_body
  exact isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)
lemma row_qqRelTotal_R_eq : (row_qqRelTotal_R : V) = exsIter 0 row_qqRelTotal_body := rfl

/-- `qqRelTotal` at the witnesses `[wk, wR, wv]` (the DSL variables right-to-left). -/
lemma inst_qqRelTotal {wk wR wv : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) :
    row_qqRelTotal_as.map (instOuter LAct [wk, wR, wv]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, wR, wv] row_qqRelTotal_body) = relFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wR) (termShift LAct wv) := by
  have hes : ∀ e ∈ ([wk, wR, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩)
  unfold row_qqRelTotal_as row_qqRelTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Prel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Prel shift_Prel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwR 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1]
    try rfl

/-! ### `qqNRelTotal` — `“v R k. …”`, `m = 3` -/

noncomputable def row_qqNRelTotal_as : List V := []
noncomputable def row_qqNRelTotal_body : V := subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Pnrel
noncomputable def row_qqNRelTotal_R : V := row_qqNRelTotal_body
noncomputable def row_qqNRelTotal_c : V := ^∃ row_qqNRelTotal_R

theorem quote_row_qqNRelTotal : (⌜Semiformula.lMap emb qqNRelTotalB⌝ : V) = impChain LAct row_qqNRelTotal_as row_qqNRelTotal_c := by
  unfold qqNRelTotalB row_qqNRelTotal_as row_qqNRelTotal_c row_qqNRelTotal_R row_qqNRelTotal_body Pnrel
  all_goals row_shape

lemma isSemiformula_qqNRelTotal_as : ∀ A ∈ row_qqNRelTotal_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_qqNRelTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqNRelTotal_c : IsSemiformula LAct ((3 : ℕ) : V) row_qqNRelTotal_c := by
  unfold row_qqNRelTotal_c row_qqNRelTotal_R row_qqNRelTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries))
lemma isSemiformula_qqNRelTotal_R : IsSemiformula LAct ((4 : ℕ) : V) row_qqNRelTotal_R := by
  unfold row_qqNRelTotal_R row_qqNRelTotal_body
  exact isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)
lemma isSemiformula_qqNRelTotal_body : IsSemiformula LAct ((4 : ℕ) : V) row_qqNRelTotal_body := by
  unfold row_qqNRelTotal_body
  exact isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)
lemma row_qqNRelTotal_R_eq : (row_qqNRelTotal_R : V) = exsIter 0 row_qqNRelTotal_body := rfl

/-- `qqNRelTotal` at the witnesses `[wk, wR, wv]` (the DSL variables right-to-left). -/
lemma inst_qqNRelTotal {wk wR wv : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) :
    row_qqNRelTotal_as.map (instOuter LAct [wk, wR, wv]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, wR, wv] row_qqNRelTotal_body) = nrelFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wR) (termShift LAct wv) := by
  have hes : ∀ e ∈ ([wk, wR, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩)
  unfold row_qqNRelTotal_as row_qqNRelTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pnrel shift_Pnrel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwR 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1]
    try rfl

/-! ### `qqVerumTotal` — `“ …”`, `m = 0` -/

noncomputable def row_qqVerumTotal_as : List V := []
noncomputable def row_qqVerumTotal_body : V := subst LAct (listToVec [bv 0]) Pverum
noncomputable def row_qqVerumTotal_R : V := row_qqVerumTotal_body
noncomputable def row_qqVerumTotal_c : V := ^∃ row_qqVerumTotal_R

theorem quote_row_qqVerumTotal : (⌜Semiformula.lMap emb qqVerumTotalB⌝ : V) = impChain LAct row_qqVerumTotal_as row_qqVerumTotal_c := by
  unfold qqVerumTotalB row_qqVerumTotal_as row_qqVerumTotal_c row_qqVerumTotal_R row_qqVerumTotal_body Pverum
  all_goals row_shape

lemma isSemiformula_qqVerumTotal_as : ∀ A ∈ row_qqVerumTotal_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_qqVerumTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqVerumTotal_c : IsSemiformula LAct ((0 : ℕ) : V) row_qqVerumTotal_c := by
  unfold row_qqVerumTotal_c row_qqVerumTotal_R row_qqVerumTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries))
lemma isSemiformula_qqVerumTotal_R : IsSemiformula LAct ((1 : ℕ) : V) row_qqVerumTotal_R := by
  unfold row_qqVerumTotal_R row_qqVerumTotal_body
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries)
lemma isSemiformula_qqVerumTotal_body : IsSemiformula LAct ((1 : ℕ) : V) row_qqVerumTotal_body := by
  unfold row_qqVerumTotal_body
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries)
lemma row_qqVerumTotal_R_eq : (row_qqVerumTotal_R : V) = exsIter 0 row_qqVerumTotal_body := rfl

/-- `qqVerumTotal` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_qqVerumTotal  :
    row_qqVerumTotal_as.map (instOuter LAct ([] : List V)) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 ([] : List V) row_qqVerumTotal_body) = verumFact (^&((0 : ℕ) : V)) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_qqVerumTotal_as row_qqVerumTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pverum (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pverum shift_Pverum (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num)]
    try rfl

/-! ### `qqFalsumTotal` — `“ …”`, `m = 0` -/

noncomputable def row_qqFalsumTotal_as : List V := []
noncomputable def row_qqFalsumTotal_body : V := subst LAct (listToVec [bv 0]) Pfalsum
noncomputable def row_qqFalsumTotal_R : V := row_qqFalsumTotal_body
noncomputable def row_qqFalsumTotal_c : V := ^∃ row_qqFalsumTotal_R

theorem quote_row_qqFalsumTotal : (⌜Semiformula.lMap emb qqFalsumTotalB⌝ : V) = impChain LAct row_qqFalsumTotal_as row_qqFalsumTotal_c := by
  unfold qqFalsumTotalB row_qqFalsumTotal_as row_qqFalsumTotal_c row_qqFalsumTotal_R row_qqFalsumTotal_body Pfalsum
  all_goals row_shape

lemma isSemiformula_qqFalsumTotal_as : ∀ A ∈ row_qqFalsumTotal_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_qqFalsumTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqFalsumTotal_c : IsSemiformula LAct ((0 : ℕ) : V) row_qqFalsumTotal_c := by
  unfold row_qqFalsumTotal_c row_qqFalsumTotal_R row_qqFalsumTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries))
lemma isSemiformula_qqFalsumTotal_R : IsSemiformula LAct ((1 : ℕ) : V) row_qqFalsumTotal_R := by
  unfold row_qqFalsumTotal_R row_qqFalsumTotal_body
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries)
lemma isSemiformula_qqFalsumTotal_body : IsSemiformula LAct ((1 : ℕ) : V) row_qqFalsumTotal_body := by
  unfold row_qqFalsumTotal_body
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries)
lemma row_qqFalsumTotal_R_eq : (row_qqFalsumTotal_R : V) = exsIter 0 row_qqFalsumTotal_body := rfl

/-- `qqFalsumTotal` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_qqFalsumTotal  :
    row_qqFalsumTotal_as.map (instOuter LAct ([] : List V)) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 ([] : List V) row_qqFalsumTotal_body) = falsumFact (^&((0 : ℕ) : V)) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_qqFalsumTotal_as row_qqFalsumTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pfalsum shift_Pfalsum (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num)]
    try rfl

/-! ### `qqAndTotal` — `“q p. …”`, `m = 2` -/

noncomputable def row_qqAndTotal_as : List V := []
noncomputable def row_qqAndTotal_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand
noncomputable def row_qqAndTotal_R : V := row_qqAndTotal_body
noncomputable def row_qqAndTotal_c : V := ^∃ row_qqAndTotal_R

theorem quote_row_qqAndTotal : (⌜Semiformula.lMap emb qqAndTotalB⌝ : V) = impChain LAct row_qqAndTotal_as row_qqAndTotal_c := by
  unfold qqAndTotalB row_qqAndTotal_as row_qqAndTotal_c row_qqAndTotal_R row_qqAndTotal_body Pand
  all_goals row_shape

lemma isSemiformula_qqAndTotal_as : ∀ A ∈ row_qqAndTotal_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_qqAndTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqAndTotal_c : IsSemiformula LAct ((2 : ℕ) : V) row_qqAndTotal_c := by
  unfold row_qqAndTotal_c row_qqAndTotal_R row_qqAndTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries))
lemma isSemiformula_qqAndTotal_R : IsSemiformula LAct ((3 : ℕ) : V) row_qqAndTotal_R := by
  unfold row_qqAndTotal_R row_qqAndTotal_body
  exact isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)
lemma isSemiformula_qqAndTotal_body : IsSemiformula LAct ((3 : ℕ) : V) row_qqAndTotal_body := by
  unfold row_qqAndTotal_body
  exact isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)
lemma row_qqAndTotal_R_eq : (row_qqAndTotal_R : V) = exsIter 0 row_qqAndTotal_body := rfl

/-- `qqAndTotal` at the witnesses `[wp, wq]` (the DSL variables right-to-left). -/
lemma inst_qqAndTotal {wp wq : V} (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) :
    row_qqAndTotal_as.map (instOuter LAct [wp, wq]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp, wq] row_qqAndTotal_body) = andFact (^&((0 : ℕ) : V)) (termShift LAct wp) (termShift LAct wq) := by
  have hes : ∀ e ∈ ([wp, wq] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_nil _⟩⟩)
  unfold row_qqAndTotal_as row_qqAndTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pand (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pand shift_Pand (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwq 1]
    try rfl

/-! ### `qqOrTotal` — `“q p. …”`, `m = 2` -/

noncomputable def row_qqOrTotal_as : List V := []
noncomputable def row_qqOrTotal_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Por
noncomputable def row_qqOrTotal_R : V := row_qqOrTotal_body
noncomputable def row_qqOrTotal_c : V := ^∃ row_qqOrTotal_R

theorem quote_row_qqOrTotal : (⌜Semiformula.lMap emb qqOrTotalB⌝ : V) = impChain LAct row_qqOrTotal_as row_qqOrTotal_c := by
  unfold qqOrTotalB row_qqOrTotal_as row_qqOrTotal_c row_qqOrTotal_R row_qqOrTotal_body Por
  all_goals row_shape

lemma isSemiformula_qqOrTotal_as : ∀ A ∈ row_qqOrTotal_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_qqOrTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqOrTotal_c : IsSemiformula LAct ((2 : ℕ) : V) row_qqOrTotal_c := by
  unfold row_qqOrTotal_c row_qqOrTotal_R row_qqOrTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries))
lemma isSemiformula_qqOrTotal_R : IsSemiformula LAct ((3 : ℕ) : V) row_qqOrTotal_R := by
  unfold row_qqOrTotal_R row_qqOrTotal_body
  exact isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)
lemma isSemiformula_qqOrTotal_body : IsSemiformula LAct ((3 : ℕ) : V) row_qqOrTotal_body := by
  unfold row_qqOrTotal_body
  exact isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)
lemma row_qqOrTotal_R_eq : (row_qqOrTotal_R : V) = exsIter 0 row_qqOrTotal_body := rfl

/-- `qqOrTotal` at the witnesses `[wp, wq]` (the DSL variables right-to-left). -/
lemma inst_qqOrTotal {wp wq : V} (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) :
    row_qqOrTotal_as.map (instOuter LAct [wp, wq]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp, wq] row_qqOrTotal_body) = orFact (^&((0 : ℕ) : V)) (termShift LAct wp) (termShift LAct wq) := by
  have hes : ∀ e ∈ ([wp, wq] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_nil _⟩⟩)
  unfold row_qqOrTotal_as row_qqOrTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Por (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Por shift_Por (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwq 1]
    try rfl

/-! ### `qqAllTotal` — `“p. …”`, `m = 1` -/

noncomputable def row_qqAllTotal_as : List V := []
noncomputable def row_qqAllTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) Pall
noncomputable def row_qqAllTotal_R : V := row_qqAllTotal_body
noncomputable def row_qqAllTotal_c : V := ^∃ row_qqAllTotal_R

theorem quote_row_qqAllTotal : (⌜Semiformula.lMap emb qqAllTotalB⌝ : V) = impChain LAct row_qqAllTotal_as row_qqAllTotal_c := by
  unfold qqAllTotalB row_qqAllTotal_as row_qqAllTotal_c row_qqAllTotal_R row_qqAllTotal_body Pall
  all_goals row_shape

lemma isSemiformula_qqAllTotal_as : ∀ A ∈ row_qqAllTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_qqAllTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqAllTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_qqAllTotal_c := by
  unfold row_qqAllTotal_c row_qqAllTotal_R row_qqAllTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries))
lemma isSemiformula_qqAllTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_qqAllTotal_R := by
  unfold row_qqAllTotal_R row_qqAllTotal_body
  exact isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)
lemma isSemiformula_qqAllTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_qqAllTotal_body := by
  unfold row_qqAllTotal_body
  exact isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)
lemma row_qqAllTotal_R_eq : (row_qqAllTotal_R : V) = exsIter 0 row_qqAllTotal_body := rfl

/-- `qqAllTotal` at the witnesses `[wp]` (the DSL variables right-to-left). -/
lemma inst_qqAllTotal {wp : V} (hwp : IsSemiterm LAct 0 wp) :
    row_qqAllTotal_as.map (instOuter LAct [wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp] row_qqAllTotal_body) = allFact (^&((0 : ℕ) : V)) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩)
  unfold row_qqAllTotal_as row_qqAllTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pall (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pall shift_Pall (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1]
    try rfl

/-! ### `qqExsTotal` — `“p. …”`, `m = 1` -/

noncomputable def row_qqExsTotal_as : List V := []
noncomputable def row_qqExsTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) Pexs
noncomputable def row_qqExsTotal_R : V := row_qqExsTotal_body
noncomputable def row_qqExsTotal_c : V := ^∃ row_qqExsTotal_R

theorem quote_row_qqExsTotal : (⌜Semiformula.lMap emb qqExsTotalB⌝ : V) = impChain LAct row_qqExsTotal_as row_qqExsTotal_c := by
  unfold qqExsTotalB row_qqExsTotal_as row_qqExsTotal_c row_qqExsTotal_R row_qqExsTotal_body Pexs
  all_goals row_shape

lemma isSemiformula_qqExsTotal_as : ∀ A ∈ row_qqExsTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_qqExsTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqExsTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_qqExsTotal_c := by
  unfold row_qqExsTotal_c row_qqExsTotal_R row_qqExsTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries))
lemma isSemiformula_qqExsTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_qqExsTotal_R := by
  unfold row_qqExsTotal_R row_qqExsTotal_body
  exact isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)
lemma isSemiformula_qqExsTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_qqExsTotal_body := by
  unfold row_qqExsTotal_body
  exact isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)
lemma row_qqExsTotal_R_eq : (row_qqExsTotal_R : V) = exsIter 0 row_qqExsTotal_body := rfl

/-- `qqExsTotal` at the witnesses `[wp]` (the DSL variables right-to-left). -/
lemma inst_qqExsTotal {wp : V} (hwp : IsSemiterm LAct 0 wp) :
    row_qqExsTotal_as.map (instOuter LAct [wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp] row_qqExsTotal_body) = exsFact (^&((0 : ℕ) : V)) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩)
  unfold row_qqExsTotal_as row_qqExsTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pexs (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pexs shift_Pexs (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1]
    try rfl

/-! ### `qqFuncTotal` — `“v f k. …”`, `m = 3` -/

noncomputable def row_qqFuncTotal_as : List V := []
noncomputable def row_qqFuncTotal_body : V := subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Pfunc
noncomputable def row_qqFuncTotal_R : V := row_qqFuncTotal_body
noncomputable def row_qqFuncTotal_c : V := ^∃ row_qqFuncTotal_R

theorem quote_row_qqFuncTotal : (⌜Semiformula.lMap emb qqFuncTotalB⌝ : V) = impChain LAct row_qqFuncTotal_as row_qqFuncTotal_c := by
  unfold qqFuncTotalB row_qqFuncTotal_as row_qqFuncTotal_c row_qqFuncTotal_R row_qqFuncTotal_body Pfunc
  all_goals row_shape

lemma isSemiformula_qqFuncTotal_as : ∀ A ∈ row_qqFuncTotal_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_qqFuncTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqFuncTotal_c : IsSemiformula LAct ((3 : ℕ) : V) row_qqFuncTotal_c := by
  unfold row_qqFuncTotal_c row_qqFuncTotal_R row_qqFuncTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pfunc _ (by rfl) (by row_entries))
lemma isSemiformula_qqFuncTotal_R : IsSemiformula LAct ((4 : ℕ) : V) row_qqFuncTotal_R := by
  unfold row_qqFuncTotal_R row_qqFuncTotal_body
  exact isSemiformula_substRow isSemiformula_Pfunc _ (by rfl) (by row_entries)
lemma isSemiformula_qqFuncTotal_body : IsSemiformula LAct ((4 : ℕ) : V) row_qqFuncTotal_body := by
  unfold row_qqFuncTotal_body
  exact isSemiformula_substRow isSemiformula_Pfunc _ (by rfl) (by row_entries)
lemma row_qqFuncTotal_R_eq : (row_qqFuncTotal_R : V) = exsIter 0 row_qqFuncTotal_body := rfl

/-- `qqFuncTotal` at the witnesses `[wk, wf, wv]` (the DSL variables right-to-left). -/
lemma inst_qqFuncTotal {wk wf wv : V} (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) :
    row_qqFuncTotal_as.map (instOuter LAct [wk, wf, wv]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, wf, wv] row_qqFuncTotal_body) = funcFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wf) (termShift LAct wv) := by
  have hes : ∀ e ∈ ([wk, wf, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩)
  unfold row_qqFuncTotal_as row_qqFuncTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pfunc (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pfunc shift_Pfunc (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwf 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1]
    try rfl

/-! ### `qqBvarTotal` — `“z. …”`, `m = 1` -/

noncomputable def row_qqBvarTotal_as : List V := []
noncomputable def row_qqBvarTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) Pbvar
noncomputable def row_qqBvarTotal_R : V := row_qqBvarTotal_body
noncomputable def row_qqBvarTotal_c : V := ^∃ row_qqBvarTotal_R

theorem quote_row_qqBvarTotal : (⌜Semiformula.lMap emb qqBvarTotalB⌝ : V) = impChain LAct row_qqBvarTotal_as row_qqBvarTotal_c := by
  unfold qqBvarTotalB row_qqBvarTotal_as row_qqBvarTotal_c row_qqBvarTotal_R row_qqBvarTotal_body Pbvar
  all_goals row_shape

lemma isSemiformula_qqBvarTotal_as : ∀ A ∈ row_qqBvarTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_qqBvarTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqBvarTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_qqBvarTotal_c := by
  unfold row_qqBvarTotal_c row_qqBvarTotal_R row_qqBvarTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pbvar _ (by rfl) (by row_entries))
lemma isSemiformula_qqBvarTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_qqBvarTotal_R := by
  unfold row_qqBvarTotal_R row_qqBvarTotal_body
  exact isSemiformula_substRow isSemiformula_Pbvar _ (by rfl) (by row_entries)
lemma isSemiformula_qqBvarTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_qqBvarTotal_body := by
  unfold row_qqBvarTotal_body
  exact isSemiformula_substRow isSemiformula_Pbvar _ (by rfl) (by row_entries)
lemma row_qqBvarTotal_R_eq : (row_qqBvarTotal_R : V) = exsIter 0 row_qqBvarTotal_body := rfl

/-- `qqBvarTotal` at the witnesses `[wz]` (the DSL variables right-to-left). -/
lemma inst_qqBvarTotal {wz : V} (hwz : IsSemiterm LAct 0 wz) :
    row_qqBvarTotal_as.map (instOuter LAct [wz]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wz] row_qqBvarTotal_body) = bvarFact (^&((0 : ℕ) : V)) (termShift LAct wz) := by
  have hes : ∀ e ∈ ([wz] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_nil _⟩)
  unfold row_qqBvarTotal_as row_qqBvarTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pbvar (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pbvar shift_Pbvar (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwz 1]
    try rfl

/-! ### `qqFvarTotal` — `“x. …”`, `m = 1` -/

noncomputable def row_qqFvarTotal_as : List V := []
noncomputable def row_qqFvarTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) Pfvar
noncomputable def row_qqFvarTotal_R : V := row_qqFvarTotal_body
noncomputable def row_qqFvarTotal_c : V := ^∃ row_qqFvarTotal_R

theorem quote_row_qqFvarTotal : (⌜Semiformula.lMap emb qqFvarTotalB⌝ : V) = impChain LAct row_qqFvarTotal_as row_qqFvarTotal_c := by
  unfold qqFvarTotalB row_qqFvarTotal_as row_qqFvarTotal_c row_qqFvarTotal_R row_qqFvarTotal_body Pfvar
  all_goals row_shape

lemma isSemiformula_qqFvarTotal_as : ∀ A ∈ row_qqFvarTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_qqFvarTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qqFvarTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_qqFvarTotal_c := by
  unfold row_qqFvarTotal_c row_qqFvarTotal_R row_qqFvarTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries))
lemma isSemiformula_qqFvarTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_qqFvarTotal_R := by
  unfold row_qqFvarTotal_R row_qqFvarTotal_body
  exact isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)
lemma isSemiformula_qqFvarTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_qqFvarTotal_body := by
  unfold row_qqFvarTotal_body
  exact isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)
lemma row_qqFvarTotal_R_eq : (row_qqFvarTotal_R : V) = exsIter 0 row_qqFvarTotal_body := rfl

/-- `qqFvarTotal` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_qqFvarTotal {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_qqFvarTotal_as.map (instOuter LAct [wx]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wx] row_qqFvarTotal_body) = fvarFact (^&((0 : ℕ) : V)) (termShift LAct wx) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_qqFvarTotal_as row_qqFvarTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pfvar (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pfvar shift_Pfvar (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwx 1]
    try rfl

/-! ### `adjoinTotal` — `“v t. …”`, `m = 2` -/

noncomputable def row_adjoinTotal_as : List V := []
noncomputable def row_adjoinTotal_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin
noncomputable def row_adjoinTotal_R : V := row_adjoinTotal_body
noncomputable def row_adjoinTotal_c : V := ^∃ row_adjoinTotal_R

theorem quote_row_adjoinTotal : (⌜Semiformula.lMap emb adjoinTotalB⌝ : V) = impChain LAct row_adjoinTotal_as row_adjoinTotal_c := by
  unfold adjoinTotalB row_adjoinTotal_as row_adjoinTotal_c row_adjoinTotal_R row_adjoinTotal_body Padjoin
  all_goals row_shape

lemma isSemiformula_adjoinTotal_as : ∀ A ∈ row_adjoinTotal_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_adjoinTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_adjoinTotal_c : IsSemiformula LAct ((2 : ℕ) : V) row_adjoinTotal_c := by
  unfold row_adjoinTotal_c row_adjoinTotal_R row_adjoinTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries))
lemma isSemiformula_adjoinTotal_R : IsSemiformula LAct ((3 : ℕ) : V) row_adjoinTotal_R := by
  unfold row_adjoinTotal_R row_adjoinTotal_body
  exact isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)
lemma isSemiformula_adjoinTotal_body : IsSemiformula LAct ((3 : ℕ) : V) row_adjoinTotal_body := by
  unfold row_adjoinTotal_body
  exact isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)
lemma row_adjoinTotal_R_eq : (row_adjoinTotal_R : V) = exsIter 0 row_adjoinTotal_body := rfl

/-- `adjoinTotal` at the witnesses `[wt, wv]` (the DSL variables right-to-left). -/
lemma inst_adjoinTotal {wt wv : V} (hwt : IsSemiterm LAct 0 wt) (hwv : IsSemiterm LAct 0 wv) :
    row_adjoinTotal_as.map (instOuter LAct [wt, wv]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wt, wv] row_adjoinTotal_body) = adjFact (^&((0 : ℕ) : V)) (termShift LAct wt) (termShift LAct wv) := by
  have hes : ∀ e ∈ ([wt, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩)
  unfold row_adjoinTotal_as row_adjoinTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Padjoin shift_Padjoin (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwt 1, freeIterT_closed 0 hwv 1]
    try rfl

/-! ### `negTotal` — `“p. …”`, `m = 1` -/

noncomputable def row_negTotal_as : List V := []
noncomputable def row_negTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) PnegG
noncomputable def row_negTotal_R : V := row_negTotal_body
noncomputable def row_negTotal_c : V := ^∃ row_negTotal_R

theorem quote_row_negTotal : (⌜Semiformula.lMap emb negTotalB⌝ : V) = impChain LAct row_negTotal_as row_negTotal_c := by
  unfold negTotalB row_negTotal_as row_negTotal_c row_negTotal_R row_negTotal_body PnegG
  all_goals row_shape

lemma isSemiformula_negTotal_as : ∀ A ∈ row_negTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_negTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_negTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_negTotal_c := by
  unfold row_negTotal_c row_negTotal_R row_negTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries))
lemma isSemiformula_negTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_negTotal_R := by
  unfold row_negTotal_R row_negTotal_body
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)
lemma isSemiformula_negTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_negTotal_body := by
  unfold row_negTotal_body
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)
lemma row_negTotal_R_eq : (row_negTotal_R : V) = exsIter 0 row_negTotal_body := rfl

/-- `negTotal` at the witnesses `[wp]` (the DSL variables right-to-left). -/
lemma inst_negTotal {wp : V} (hwp : IsSemiterm LAct 0 wp) :
    row_negTotal_as.map (instOuter LAct [wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp] row_negTotal_body) = negFact (^&((0 : ℕ) : V)) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩)
  unfold row_negTotal_as row_negTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1]
    try rfl

/-! ### `shiftTotal` — `“p. …”`, `m = 1` -/

noncomputable def row_shiftTotal_as : List V := []
noncomputable def row_shiftTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) PshiftG
noncomputable def row_shiftTotal_R : V := row_shiftTotal_body
noncomputable def row_shiftTotal_c : V := ^∃ row_shiftTotal_R

theorem quote_row_shiftTotal : (⌜Semiformula.lMap emb shiftTotalB⌝ : V) = impChain LAct row_shiftTotal_as row_shiftTotal_c := by
  unfold shiftTotalB row_shiftTotal_as row_shiftTotal_c row_shiftTotal_R row_shiftTotal_body PshiftG
  all_goals row_shape

lemma isSemiformula_shiftTotal_as : ∀ A ∈ row_shiftTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_shiftTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_shiftTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_shiftTotal_c := by
  unfold row_shiftTotal_c row_shiftTotal_R row_shiftTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries))
lemma isSemiformula_shiftTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_shiftTotal_R := by
  unfold row_shiftTotal_R row_shiftTotal_body
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)
lemma isSemiformula_shiftTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_shiftTotal_body := by
  unfold row_shiftTotal_body
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)
lemma row_shiftTotal_R_eq : (row_shiftTotal_R : V) = exsIter 0 row_shiftTotal_body := rfl

/-- `shiftTotal` at the witnesses `[wp]` (the DSL variables right-to-left). -/
lemma inst_shiftTotal {wp : V} (hwp : IsSemiterm LAct 0 wp) :
    row_shiftTotal_as.map (instOuter LAct [wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp] row_shiftTotal_body) = shiftFact (^&((0 : ℕ) : V)) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩)
  unfold row_shiftTotal_as row_shiftTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1]
    try rfl

/-! ### `substsTotal` — `“p w. …”`, `m = 2` -/

noncomputable def row_substsTotal_as : List V := []
noncomputable def row_substsTotal_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG
noncomputable def row_substsTotal_R : V := row_substsTotal_body
noncomputable def row_substsTotal_c : V := ^∃ row_substsTotal_R

theorem quote_row_substsTotal : (⌜Semiformula.lMap emb substsTotalB⌝ : V) = impChain LAct row_substsTotal_as row_substsTotal_c := by
  unfold substsTotalB row_substsTotal_as row_substsTotal_c row_substsTotal_R row_substsTotal_body PsubstsG
  all_goals row_shape

lemma isSemiformula_substsTotal_as : ∀ A ∈ row_substsTotal_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_substsTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_substsTotal_c : IsSemiformula LAct ((2 : ℕ) : V) row_substsTotal_c := by
  unfold row_substsTotal_c row_substsTotal_R row_substsTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries))
lemma isSemiformula_substsTotal_R : IsSemiformula LAct ((3 : ℕ) : V) row_substsTotal_R := by
  unfold row_substsTotal_R row_substsTotal_body
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)
lemma isSemiformula_substsTotal_body : IsSemiformula LAct ((3 : ℕ) : V) row_substsTotal_body := by
  unfold row_substsTotal_body
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)
lemma row_substsTotal_R_eq : (row_substsTotal_R : V) = exsIter 0 row_substsTotal_body := rfl

/-- `substsTotal` at the witnesses `[ww, wp]` (the DSL variables right-to-left). -/
lemma inst_substsTotal {ww wp : V} (hww : IsSemiterm LAct 0 ww) (hwp : IsSemiterm LAct 0 wp) :
    row_substsTotal_as.map (instOuter LAct [ww, wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [ww, wp] row_substsTotal_body) = substFact (^&((0 : ℕ) : V)) (termShift LAct ww) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([ww, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩)
  unfold row_substsTotal_as row_substsTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hww 1]
    try rfl

/-! ### `substs1Total` — `“p t. …”`, `m = 2` -/

noncomputable def row_substs1Total_as : List V := []
noncomputable def row_substs1Total_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Psubsts1G
noncomputable def row_substs1Total_R : V := row_substs1Total_body
noncomputable def row_substs1Total_c : V := ^∃ row_substs1Total_R

theorem quote_row_substs1Total : (⌜Semiformula.lMap emb substs1TotalB⌝ : V) = impChain LAct row_substs1Total_as row_substs1Total_c := by
  unfold substs1TotalB row_substs1Total_as row_substs1Total_c row_substs1Total_R row_substs1Total_body Psubsts1G
  all_goals row_shape

lemma isSemiformula_substs1Total_as : ∀ A ∈ row_substs1Total_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_substs1Total_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_substs1Total_c : IsSemiformula LAct ((2 : ℕ) : V) row_substs1Total_c := by
  unfold row_substs1Total_c row_substs1Total_R row_substs1Total_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_Psubsts1G _ (by rfl) (by row_entries))
lemma isSemiformula_substs1Total_R : IsSemiformula LAct ((3 : ℕ) : V) row_substs1Total_R := by
  unfold row_substs1Total_R row_substs1Total_body
  exact isSemiformula_substRow isSemiformula_Psubsts1G _ (by rfl) (by row_entries)
lemma isSemiformula_substs1Total_body : IsSemiformula LAct ((3 : ℕ) : V) row_substs1Total_body := by
  unfold row_substs1Total_body
  exact isSemiformula_substRow isSemiformula_Psubsts1G _ (by rfl) (by row_entries)
lemma row_substs1Total_R_eq : (row_substs1Total_R : V) = exsIter 0 row_substs1Total_body := rfl

/-- `substs1Total` at the witnesses `[wt, wp]` (the DSL variables right-to-left). -/
lemma inst_substs1Total {wt wp : V} (hwt : IsSemiterm LAct 0 wt) (hwp : IsSemiterm LAct 0 wp) :
    row_substs1Total_as.map (instOuter LAct [wt, wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wt, wp] row_substs1Total_body) = substs1Fact (^&((0 : ℕ) : V)) (termShift LAct wt) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([wt, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩)
  unfold row_substs1Total_as row_substs1Total_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Psubsts1G (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Psubsts1G shift_Psubsts1G (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwt 1]
    try rfl

/-! ### `freeTotal` — `“p. …”`, `m = 1` -/

noncomputable def row_freeTotal_as : List V := []
noncomputable def row_freeTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) PfreeG
noncomputable def row_freeTotal_R : V := row_freeTotal_body
noncomputable def row_freeTotal_c : V := ^∃ row_freeTotal_R

theorem quote_row_freeTotal : (⌜Semiformula.lMap emb freeTotalB⌝ : V) = impChain LAct row_freeTotal_as row_freeTotal_c := by
  unfold freeTotalB row_freeTotal_as row_freeTotal_c row_freeTotal_R row_freeTotal_body PfreeG
  all_goals row_shape

lemma isSemiformula_freeTotal_as : ∀ A ∈ row_freeTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_freeTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_freeTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_freeTotal_c := by
  unfold row_freeTotal_c row_freeTotal_R row_freeTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries))
lemma isSemiformula_freeTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_freeTotal_R := by
  unfold row_freeTotal_R row_freeTotal_body
  exact isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)
lemma isSemiformula_freeTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_freeTotal_body := by
  unfold row_freeTotal_body
  exact isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)
lemma row_freeTotal_R_eq : (row_freeTotal_R : V) = exsIter 0 row_freeTotal_body := rfl

/-- `freeTotal` at the witnesses `[wp]` (the DSL variables right-to-left). -/
lemma inst_freeTotal {wp : V} (hwp : IsSemiterm LAct 0 wp) :
    row_freeTotal_as.map (instOuter LAct [wp]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wp] row_freeTotal_body) = freeFact (^&((0 : ℕ) : V)) (termShift LAct wp) := by
  have hes : ∀ e ∈ ([wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩)
  unfold row_freeTotal_as row_freeTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PfreeG shift_PfreeG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1]
    try rfl

/-! ### `qVecTotal` — `“w. …”`, `m = 1` -/

noncomputable def row_qVecTotal_as : List V := []
noncomputable def row_qVecTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) PqVecG
noncomputable def row_qVecTotal_R : V := row_qVecTotal_body
noncomputable def row_qVecTotal_c : V := ^∃ row_qVecTotal_R

theorem quote_row_qVecTotal : (⌜Semiformula.lMap emb qVecTotalB⌝ : V) = impChain LAct row_qVecTotal_as row_qVecTotal_c := by
  unfold qVecTotalB row_qVecTotal_as row_qVecTotal_c row_qVecTotal_R row_qVecTotal_body PqVecG
  all_goals row_shape

lemma isSemiformula_qVecTotal_as : ∀ A ∈ row_qVecTotal_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_qVecTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_qVecTotal_c : IsSemiformula LAct ((1 : ℕ) : V) row_qVecTotal_c := by
  unfold row_qVecTotal_c row_qVecTotal_R row_qVecTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries))
lemma isSemiformula_qVecTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_qVecTotal_R := by
  unfold row_qVecTotal_R row_qVecTotal_body
  exact isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)
lemma isSemiformula_qVecTotal_body : IsSemiformula LAct ((2 : ℕ) : V) row_qVecTotal_body := by
  unfold row_qVecTotal_body
  exact isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)
lemma row_qVecTotal_R_eq : (row_qVecTotal_R : V) = exsIter 0 row_qVecTotal_body := rfl

/-- `qVecTotal` at the witnesses `[ww]` (the DSL variables right-to-left). -/
lemma inst_qVecTotal {ww : V} (hww : IsSemiterm LAct 0 ww) :
    row_qVecTotal_as.map (instOuter LAct [ww]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [ww] row_qVecTotal_body) = qVecFact (^&((0 : ℕ) : V)) (termShift LAct ww) := by
  have hes : ∀ e ∈ ([ww] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_nil _⟩)
  unfold row_qVecTotal_as row_qVecTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PqVecG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hww 1]
    try rfl

/-! ### `termSubstVecTotal` — `“v w k. …”`, `m = 3` -/

noncomputable def row_termSubstVecTotal_as : List V := []
noncomputable def row_termSubstVecTotal_body : V := subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) PtsvG
noncomputable def row_termSubstVecTotal_R : V := row_termSubstVecTotal_body
noncomputable def row_termSubstVecTotal_c : V := ^∃ row_termSubstVecTotal_R

theorem quote_row_termSubstVecTotal : (⌜Semiformula.lMap emb termSubstVecTotalB⌝ : V) = impChain LAct row_termSubstVecTotal_as row_termSubstVecTotal_c := by
  unfold termSubstVecTotalB row_termSubstVecTotal_as row_termSubstVecTotal_c row_termSubstVecTotal_R row_termSubstVecTotal_body PtsvG
  all_goals row_shape

lemma isSemiformula_termSubstVecTotal_as : ∀ A ∈ row_termSubstVecTotal_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_termSubstVecTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_termSubstVecTotal_c : IsSemiformula LAct ((3 : ℕ) : V) row_termSubstVecTotal_c := by
  unfold row_termSubstVecTotal_c row_termSubstVecTotal_R row_termSubstVecTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries))
lemma isSemiformula_termSubstVecTotal_R : IsSemiformula LAct ((4 : ℕ) : V) row_termSubstVecTotal_R := by
  unfold row_termSubstVecTotal_R row_termSubstVecTotal_body
  exact isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)
lemma isSemiformula_termSubstVecTotal_body : IsSemiformula LAct ((4 : ℕ) : V) row_termSubstVecTotal_body := by
  unfold row_termSubstVecTotal_body
  exact isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)
lemma row_termSubstVecTotal_R_eq : (row_termSubstVecTotal_R : V) = exsIter 0 row_termSubstVecTotal_body := rfl

/-- `termSubstVecTotal` at the witnesses `[wk, ww, wv]` (the DSL variables right-to-left). -/
lemma inst_termSubstVecTotal {wk ww wv : V} (hwk : IsSemiterm LAct 0 wk) (hww : IsSemiterm LAct 0 ww) (hwv : IsSemiterm LAct 0 wv) :
    row_termSubstVecTotal_as.map (instOuter LAct [wk, ww, wv]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, ww, wv] row_termSubstVecTotal_body) = tsvFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct ww) (termShift LAct wv) := by
  have hes : ∀ e ∈ ([wk, ww, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩)
  unfold row_termSubstVecTotal_as row_termSubstVecTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PtsvG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1, freeIterT_closed 0 hww 1]
    try rfl

/-! ### `termShiftVecTotal` — `“v k. …”`, `m = 2` -/

noncomputable def row_termShiftVecTotal_as : List V := []
noncomputable def row_termShiftVecTotal_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) PtshvG
noncomputable def row_termShiftVecTotal_R : V := row_termShiftVecTotal_body
noncomputable def row_termShiftVecTotal_c : V := ^∃ row_termShiftVecTotal_R

theorem quote_row_termShiftVecTotal : (⌜Semiformula.lMap emb termShiftVecTotalB⌝ : V) = impChain LAct row_termShiftVecTotal_as row_termShiftVecTotal_c := by
  unfold termShiftVecTotalB row_termShiftVecTotal_as row_termShiftVecTotal_c row_termShiftVecTotal_R row_termShiftVecTotal_body PtshvG
  all_goals row_shape

lemma isSemiformula_termShiftVecTotal_as : ∀ A ∈ row_termShiftVecTotal_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_termShiftVecTotal_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_termShiftVecTotal_c : IsSemiformula LAct ((2 : ℕ) : V) row_termShiftVecTotal_c := by
  unfold row_termShiftVecTotal_c row_termShiftVecTotal_R row_termShiftVecTotal_body
  exact isSemiformula_exs_cast (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries))
lemma isSemiformula_termShiftVecTotal_R : IsSemiformula LAct ((3 : ℕ) : V) row_termShiftVecTotal_R := by
  unfold row_termShiftVecTotal_R row_termShiftVecTotal_body
  exact isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)
lemma isSemiformula_termShiftVecTotal_body : IsSemiformula LAct ((3 : ℕ) : V) row_termShiftVecTotal_body := by
  unfold row_termShiftVecTotal_body
  exact isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)
lemma row_termShiftVecTotal_R_eq : (row_termShiftVecTotal_R : V) = exsIter 0 row_termShiftVecTotal_body := rfl

/-- `termShiftVecTotal` at the witnesses `[wk, wv]` (the DSL variables right-to-left). -/
lemma inst_termShiftVecTotal {wk wv : V} (hwk : IsSemiterm LAct 0 wk) (hwv : IsSemiterm LAct 0 wv) :
    row_termShiftVecTotal_as.map (instOuter LAct [wk, wv]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, wv] row_termShiftVecTotal_body) = tshvFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wv) := by
  have hes : ∀ e ∈ ([wk, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩)
  unfold row_termShiftVecTotal_as row_termShiftVecTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PtshvG (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1]
    try rfl

/-! ### `isSemiformulaRel` — `“p v R k n. …”`, `m = 5` -/

noncomputable def row_isSemiformulaRel_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PisRel, subst LAct (listToVec [bv 3, bv 4, bv 1]) PtvPi, subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Prel]
noncomputable def row_isSemiformulaRel_c : V := subst LAct (listToVec [bv 4, bv 0]) Psigma

theorem quote_row_isSemiformulaRel : (⌜Semiformula.lMap emb isSemiformulaRelB⌝ : V) = impChain LAct row_isSemiformulaRel_as row_isSemiformulaRel_c := by
  unfold isSemiformulaRelB row_isSemiformulaRel_as row_isSemiformulaRel_c PisRel Prel Psigma PtvPi
  all_goals row_shape

lemma isSemiformula_isSemiformulaRel_as : ∀ A ∈ row_isSemiformulaRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_isSemiformulaRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemiformulaRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_isSemiformulaRel_c := by
  unfold row_isSemiformulaRel_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaRel` at the witnesses `[wn, wk, wR, wv, wp]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaRel {wn wk wR wv wp : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwp : IsSemiterm LAct 0 wp) :
    row_isSemiformulaRel_as.map (instOuter LAct [wn, wk, wR, wv, wp]) = [isRelFact wk wR, tvPiFact wk wn wv, relFact wp wk wR wv] ∧
    instOuter LAct [wn, wk, wR, wv, wp] row_isSemiformulaRel_c = sigmaFact wn wp := by
  have hes : ∀ e ∈ ([wn, wk, wR, wv, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_isSemiformulaRel_as row_isSemiformulaRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaNRel` — `“p v R k n. …”`, `m = 5` -/

noncomputable def row_isSemiformulaNRel_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PisRel, subst LAct (listToVec [bv 3, bv 4, bv 1]) PtvPi, subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Pnrel]
noncomputable def row_isSemiformulaNRel_c : V := subst LAct (listToVec [bv 4, bv 0]) Psigma

theorem quote_row_isSemiformulaNRel : (⌜Semiformula.lMap emb isSemiformulaNRelB⌝ : V) = impChain LAct row_isSemiformulaNRel_as row_isSemiformulaNRel_c := by
  unfold isSemiformulaNRelB row_isSemiformulaNRel_as row_isSemiformulaNRel_c PisRel Pnrel Psigma PtvPi
  all_goals row_shape

lemma isSemiformula_isSemiformulaNRel_as : ∀ A ∈ row_isSemiformulaNRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_isSemiformulaNRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemiformulaNRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_isSemiformulaNRel_c := by
  unfold row_isSemiformulaNRel_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaNRel` at the witnesses `[wn, wk, wR, wv, wp]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaNRel {wn wk wR wv wp : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwp : IsSemiterm LAct 0 wp) :
    row_isSemiformulaNRel_as.map (instOuter LAct [wn, wk, wR, wv, wp]) = [isRelFact wk wR, tvPiFact wk wn wv, nrelFact wp wk wR wv] ∧
    instOuter LAct [wn, wk, wR, wv, wp] row_isSemiformulaNRel_c = sigmaFact wn wp := by
  have hes : ∀ e ∈ ([wn, wk, wR, wv, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_isSemiformulaNRel_as row_isSemiformulaNRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaVerum` — `“p n. …”`, `m = 2` -/

noncomputable def row_isSemiformulaVerum_as : List V := [subst LAct (listToVec [bv 0]) Pverum]
noncomputable def row_isSemiformulaVerum_c : V := subst LAct (listToVec [bv 1, bv 0]) Psigma

theorem quote_row_isSemiformulaVerum : (⌜Semiformula.lMap emb isSemiformulaVerumB⌝ : V) = impChain LAct row_isSemiformulaVerum_as row_isSemiformulaVerum_c := by
  unfold isSemiformulaVerumB row_isSemiformulaVerum_as row_isSemiformulaVerum_c Psigma Pverum
  all_goals row_shape

lemma isSemiformula_isSemiformulaVerum_as : ∀ A ∈ row_isSemiformulaVerum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_isSemiformulaVerum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isSemiformulaVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_isSemiformulaVerum_c := by
  unfold row_isSemiformulaVerum_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaVerum` at the witnesses `[wn, wp]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaVerum {wn wp : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) :
    row_isSemiformulaVerum_as.map (instOuter LAct [wn, wp]) = [verumFact wp] ∧
    instOuter LAct [wn, wp] row_isSemiformulaVerum_c = sigmaFact wn wp := by
  have hes : ∀ e ∈ ([wn, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩)
  unfold row_isSemiformulaVerum_as row_isSemiformulaVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaFalsum` — `“p n. …”`, `m = 2` -/

noncomputable def row_isSemiformulaFalsum_as : List V := [subst LAct (listToVec [bv 0]) Pfalsum]
noncomputable def row_isSemiformulaFalsum_c : V := subst LAct (listToVec [bv 1, bv 0]) Psigma

theorem quote_row_isSemiformulaFalsum : (⌜Semiformula.lMap emb isSemiformulaFalsumB⌝ : V) = impChain LAct row_isSemiformulaFalsum_as row_isSemiformulaFalsum_c := by
  unfold isSemiformulaFalsumB row_isSemiformulaFalsum_as row_isSemiformulaFalsum_c Pfalsum Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaFalsum_as : ∀ A ∈ row_isSemiformulaFalsum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_isSemiformulaFalsum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isSemiformulaFalsum_c : IsSemiformula LAct ((2 : ℕ) : V) row_isSemiformulaFalsum_c := by
  unfold row_isSemiformulaFalsum_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaFalsum` at the witnesses `[wn, wp]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaFalsum {wn wp : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) :
    row_isSemiformulaFalsum_as.map (instOuter LAct [wn, wp]) = [falsumFact wp] ∧
    instOuter LAct [wn, wp] row_isSemiformulaFalsum_c = sigmaFact wn wp := by
  have hes : ∀ e ∈ ([wn, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩)
  unfold row_isSemiformulaFalsum_as row_isSemiformulaFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaAnd` — `“r q p n. …”`, `m = 4` -/

noncomputable def row_isSemiformulaAnd_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Ppi, subst LAct (listToVec [bv 3, bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand]
noncomputable def row_isSemiformulaAnd_c : V := subst LAct (listToVec [bv 3, bv 0]) Psigma

theorem quote_row_isSemiformulaAnd : (⌜Semiformula.lMap emb isSemiformulaAndB⌝ : V) = impChain LAct row_isSemiformulaAnd_as row_isSemiformulaAnd_c := by
  unfold isSemiformulaAndB row_isSemiformulaAnd_as row_isSemiformulaAnd_c Pand Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaAnd_as : ∀ A ∈ row_isSemiformulaAnd_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_isSemiformulaAnd_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemiformulaAnd_c : IsSemiformula LAct ((4 : ℕ) : V) row_isSemiformulaAnd_c := by
  unfold row_isSemiformulaAnd_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaAnd` at the witnesses `[wn, wp, wq, wr]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaAnd {wn wp wq wr : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) :
    row_isSemiformulaAnd_as.map (instOuter LAct [wn, wp, wq, wr]) = [piFact wn wp, piFact wn wq, andFact wr wp wq] ∧
    instOuter LAct [wn, wp, wq, wr] row_isSemiformulaAnd_c = sigmaFact wn wr := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_isSemiformulaAnd_as row_isSemiformulaAnd_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaOr` — `“r q p n. …”`, `m = 4` -/

noncomputable def row_isSemiformulaOr_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Ppi, subst LAct (listToVec [bv 3, bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 2, bv 1]) Por]
noncomputable def row_isSemiformulaOr_c : V := subst LAct (listToVec [bv 3, bv 0]) Psigma

theorem quote_row_isSemiformulaOr : (⌜Semiformula.lMap emb isSemiformulaOrB⌝ : V) = impChain LAct row_isSemiformulaOr_as row_isSemiformulaOr_c := by
  unfold isSemiformulaOrB row_isSemiformulaOr_as row_isSemiformulaOr_c Por Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaOr_as : ∀ A ∈ row_isSemiformulaOr_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_isSemiformulaOr_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemiformulaOr_c : IsSemiformula LAct ((4 : ℕ) : V) row_isSemiformulaOr_c := by
  unfold row_isSemiformulaOr_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaOr` at the witnesses `[wn, wp, wq, wr]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaOr {wn wp wq wr : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) :
    row_isSemiformulaOr_as.map (instOuter LAct [wn, wp, wq, wr]) = [piFact wn wp, piFact wn wq, orFact wr wp wq] ∧
    instOuter LAct [wn, wp, wq, wr] row_isSemiformulaOr_c = sigmaFact wn wr := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_isSemiformulaOr_as row_isSemiformulaOr_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaAll` — `“q p n. …”`, `m = 3` -/

noncomputable def row_isSemiformulaAll_as : List V := [subst LAct (listToVec [bv 2 ^+ (𝟏 : V), bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1]) Pall]
noncomputable def row_isSemiformulaAll_c : V := subst LAct (listToVec [bv 2, bv 0]) Psigma

theorem quote_row_isSemiformulaAll : (⌜Semiformula.lMap emb isSemiformulaAllB⌝ : V) = impChain LAct row_isSemiformulaAll_as row_isSemiformulaAll_c := by
  unfold isSemiformulaAllB row_isSemiformulaAll_as row_isSemiformulaAll_c Pall Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaAll_as : ∀ A ∈ row_isSemiformulaAll_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemiformulaAll_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isSemiformulaAll_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemiformulaAll_c := by
  unfold row_isSemiformulaAll_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaAll` at the witnesses `[wn, wp, wq]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaAll {wn wp wq : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) :
    row_isSemiformulaAll_as.map (instOuter LAct [wn, wp, wq]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wq wp] ∧
    instOuter LAct [wn, wp, wq] row_isSemiformulaAll_c = sigmaFact wn wq := by
  have hes : ∀ e ∈ ([wn, wp, wq] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemiformulaAll_as row_isSemiformulaAll_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaExs` — `“q p n. …”`, `m = 3` -/

noncomputable def row_isSemiformulaExs_as : List V := [subst LAct (listToVec [bv 2 ^+ (𝟏 : V), bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1]) Pexs]
noncomputable def row_isSemiformulaExs_c : V := subst LAct (listToVec [bv 2, bv 0]) Psigma

theorem quote_row_isSemiformulaExs : (⌜Semiformula.lMap emb isSemiformulaExsB⌝ : V) = impChain LAct row_isSemiformulaExs_as row_isSemiformulaExs_c := by
  unfold isSemiformulaExsB row_isSemiformulaExs_as row_isSemiformulaExs_c Pexs Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaExs_as : ∀ A ∈ row_isSemiformulaExs_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemiformulaExs_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isSemiformulaExs_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemiformulaExs_c := by
  unfold row_isSemiformulaExs_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaExs` at the witnesses `[wn, wp, wq]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaExs {wn wp wq : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) :
    row_isSemiformulaExs_as.map (instOuter LAct [wn, wp, wq]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wq wp] ∧
    instOuter LAct [wn, wp, wq] row_isSemiformulaExs_c = sigmaFact wn wq := by
  have hes : ∀ e ∈ ([wn, wp, wq] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemiformulaExs_as row_isSemiformulaExs_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaNeg` — `“y p n. …”`, `m = 3` -/

noncomputable def row_isSemiformulaNeg_as : List V := [subst LAct (listToVec [bv 2, bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_isSemiformulaNeg_c : V := subst LAct (listToVec [bv 2, bv 0]) Psigma

theorem quote_row_isSemiformulaNeg : (⌜Semiformula.lMap emb isSemiformulaNegB⌝ : V) = impChain LAct row_isSemiformulaNeg_as row_isSemiformulaNeg_c := by
  unfold isSemiformulaNegB row_isSemiformulaNeg_as row_isSemiformulaNeg_c PnegG Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaNeg_as : ∀ A ∈ row_isSemiformulaNeg_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemiformulaNeg_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isSemiformulaNeg_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemiformulaNeg_c := by
  unfold row_isSemiformulaNeg_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaNeg` at the witnesses `[wn, wp, wy]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaNeg {wn wp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwy : IsSemiterm LAct 0 wy) :
    row_isSemiformulaNeg_as.map (instOuter LAct [wn, wp, wy]) = [piFact wn wp, negFact wy wp] ∧
    instOuter LAct [wn, wp, wy] row_isSemiformulaNeg_c = sigmaFact wn wy := by
  have hes : ∀ e ∈ ([wn, wp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemiformulaNeg_as row_isSemiformulaNeg_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaShift` — `“y p n. …”`, `m = 3` -/

noncomputable def row_isSemiformulaShift_as : List V := [subst LAct (listToVec [bv 2, bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_isSemiformulaShift_c : V := subst LAct (listToVec [bv 2, bv 0]) Psigma

theorem quote_row_isSemiformulaShift : (⌜Semiformula.lMap emb isSemiformulaShiftB⌝ : V) = impChain LAct row_isSemiformulaShift_as row_isSemiformulaShift_c := by
  unfold isSemiformulaShiftB row_isSemiformulaShift_as row_isSemiformulaShift_c Ppi PshiftG Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaShift_as : ∀ A ∈ row_isSemiformulaShift_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemiformulaShift_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isSemiformulaShift_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemiformulaShift_c := by
  unfold row_isSemiformulaShift_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaShift` at the witnesses `[wn, wp, wy]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaShift {wn wp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwy : IsSemiterm LAct 0 wy) :
    row_isSemiformulaShift_as.map (instOuter LAct [wn, wp, wy]) = [piFact wn wp, shiftFact wy wp] ∧
    instOuter LAct [wn, wp, wy] row_isSemiformulaShift_c = sigmaFact wn wy := by
  have hes : ∀ e ∈ ([wn, wp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemiformulaShift_as row_isSemiformulaShift_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaSubst` — `“y w p m n. …”`, `m = 5` -/

noncomputable def row_isSemiformulaSubst_as : List V := [subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 4, bv 3, bv 1]) PtvPi, subst LAct (listToVec [bv 0, bv 1, bv 2]) PsubstsG]
noncomputable def row_isSemiformulaSubst_c : V := subst LAct (listToVec [bv 3, bv 0]) Psigma

theorem quote_row_isSemiformulaSubst : (⌜Semiformula.lMap emb isSemiformulaSubstB⌝ : V) = impChain LAct row_isSemiformulaSubst_as row_isSemiformulaSubst_c := by
  unfold isSemiformulaSubstB row_isSemiformulaSubst_as row_isSemiformulaSubst_c Ppi Psigma PsubstsG PtvPi
  all_goals row_shape

lemma isSemiformula_isSemiformulaSubst_as : ∀ A ∈ row_isSemiformulaSubst_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_isSemiformulaSubst_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemiformulaSubst_c : IsSemiformula LAct ((5 : ℕ) : V) row_isSemiformulaSubst_c := by
  unfold row_isSemiformulaSubst_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaSubst` at the witnesses `[wn, wm, wp, ww, wy]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaSubst {wn wm wp ww wy : V} (hwn : IsSemiterm LAct 0 wn) (hwm : IsSemiterm LAct 0 wm) (hwp : IsSemiterm LAct 0 wp) (hww : IsSemiterm LAct 0 ww) (hwy : IsSemiterm LAct 0 wy) :
    row_isSemiformulaSubst_as.map (instOuter LAct [wn, wm, wp, ww, wy]) = [piFact wn wp, tvPiFact wn wm ww, substFact wy ww wp] ∧
    instOuter LAct [wn, wm, wp, ww, wy] row_isSemiformulaSubst_c = sigmaFact wm wy := by
  have hes : ∀ e ∈ ([wn, wm, wp, ww, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwm, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_isSemiformulaSubst_as row_isSemiformulaSubst_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaSubsts1` — `“y p t n. …”`, `m = 4` -/

noncomputable def row_isSemiformulaSubsts1_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PtPi, subst LAct (listToVec [(𝟏 : V), bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 2, bv 1]) Psubsts1G]
noncomputable def row_isSemiformulaSubsts1_c : V := subst LAct (listToVec [bv 3, bv 0]) Psigma

theorem quote_row_isSemiformulaSubsts1 : (⌜Semiformula.lMap emb isSemiformulaSubsts1B⌝ : V) = impChain LAct row_isSemiformulaSubsts1_as row_isSemiformulaSubsts1_c := by
  unfold isSemiformulaSubsts1B row_isSemiformulaSubsts1_as row_isSemiformulaSubsts1_c Ppi Psigma Psubsts1G PtPi
  all_goals row_shape

lemma isSemiformula_isSemiformulaSubsts1_as : ∀ A ∈ row_isSemiformulaSubsts1_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_isSemiformulaSubsts1_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Psubsts1G _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemiformulaSubsts1_c : IsSemiformula LAct ((4 : ℕ) : V) row_isSemiformulaSubsts1_c := by
  unfold row_isSemiformulaSubsts1_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isSemiformulaSubsts1` at the witnesses `[wn, wt, wp, wy]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaSubsts1 {wn wt wp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwt : IsSemiterm LAct 0 wt) (hwp : IsSemiterm LAct 0 wp) (hwy : IsSemiterm LAct 0 wy) :
    row_isSemiformulaSubsts1_as.map (instOuter LAct [wn, wt, wp, wy]) = [tPiFact wn wt, piFact (𝟏 : V) wp, substs1Fact wy wt wp] ∧
    instOuter LAct [wn, wt, wp, wy] row_isSemiformulaSubsts1_c = sigmaFact wn wy := by
  have hes : ∀ e ∈ ([wn, wt, wp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_isSemiformulaSubsts1_as row_isSemiformulaSubsts1_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psubsts1G (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFormulaFree` — `“y p. …”`, `m = 2` -/

noncomputable def row_isFormulaFree_as : List V := [subst LAct (listToVec [(𝟏 : V), bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_isFormulaFree_c : V := subst LAct (listToVec [(𝟎 : V), bv 0]) Psigma

theorem quote_row_isFormulaFree : (⌜Semiformula.lMap emb isFormulaFreeB⌝ : V) = impChain LAct row_isFormulaFree_as row_isFormulaFree_c := by
  unfold isFormulaFreeB row_isFormulaFree_as row_isFormulaFree_c PfreeG Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isFormulaFree_as : ∀ A ∈ row_isFormulaFree_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_isFormulaFree_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isFormulaFree_c : IsSemiformula LAct ((2 : ℕ) : V) row_isFormulaFree_c := by
  unfold row_isFormulaFree_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries)

/-- `isFormulaFree` at the witnesses `[wp, wy]` (the DSL variables right-to-left). -/
lemma inst_isFormulaFree {wp wy : V} (hwp : IsSemiterm LAct 0 wp) (hwy : IsSemiterm LAct 0 wy) :
    row_isFormulaFree_as.map (instOuter LAct [wp, wy]) = [piFact (𝟏 : V) wp, freeFact wy wp] ∧
    instOuter LAct [wp, wy] row_isFormulaFree_c = sigmaFact (𝟎 : V) wy := by
  have hes : ∀ e ∈ ([wp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_isFormulaFree_as row_isFormulaFree_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermFunc` — `“t v f k n. …”`, `m = 5` -/

noncomputable def row_isSemitermFunc_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PisFunc, subst LAct (listToVec [bv 3, bv 4, bv 1]) PtvPi, subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Pfunc]
noncomputable def row_isSemitermFunc_c : V := subst LAct (listToVec [bv 4, bv 0]) PtSigma

theorem quote_row_isSemitermFunc : (⌜Semiformula.lMap emb isSemitermFuncB⌝ : V) = impChain LAct row_isSemitermFunc_as row_isSemitermFunc_c := by
  unfold isSemitermFuncB row_isSemitermFunc_as row_isSemitermFunc_c Pfunc PisFunc PtSigma PtvPi
  all_goals row_shape

lemma isSemiformula_isSemitermFunc_as : ∀ A ∈ row_isSemitermFunc_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_isSemitermFunc_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfunc _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemitermFunc_c : IsSemiformula LAct ((5 : ℕ) : V) row_isSemitermFunc_c := by
  unfold row_isSemitermFunc_c
  exact isSemiformula_substRow isSemiformula_PtSigma _ (by rfl) (by row_entries)

/-- `isSemitermFunc` at the witnesses `[wn, wk, wf, wv, wt]` (the DSL variables right-to-left). -/
lemma inst_isSemitermFunc {wn wk wf wv wt : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwt : IsSemiterm LAct 0 wt) :
    row_isSemitermFunc_as.map (instOuter LAct [wn, wk, wf, wv, wt]) = [isFuncFact wk wf, tvPiFact wk wn wv, funcFact wt wk wf wv] ∧
    instOuter LAct [wn, wk, wf, wv, wt] row_isSemitermFunc_c = tSigmaFact wn wt := by
  have hes : ∀ e ∈ ([wn, wk, wf, wv, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_isSemitermFunc_as row_isSemitermFunc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermBvar` — `“t z n. …”`, `m = 3` -/

noncomputable def row_isSemitermBvar_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Plt, subst LAct (listToVec [bv 0, bv 1]) Pbvar]
noncomputable def row_isSemitermBvar_c : V := subst LAct (listToVec [bv 2, bv 0]) PtSigma

theorem quote_row_isSemitermBvar : (⌜Semiformula.lMap emb isSemitermBvarB⌝ : V) = impChain LAct row_isSemitermBvar_as row_isSemitermBvar_c := by
  unfold isSemitermBvarB row_isSemitermBvar_as row_isSemitermBvar_c Pbvar Plt PtSigma
  all_goals row_shape

lemma isSemiformula_isSemitermBvar_as : ∀ A ∈ row_isSemitermBvar_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemitermBvar_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Plt _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pbvar _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isSemitermBvar_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemitermBvar_c := by
  unfold row_isSemitermBvar_c
  exact isSemiformula_substRow isSemiformula_PtSigma _ (by rfl) (by row_entries)

/-- `isSemitermBvar` at the witnesses `[wn, wz, wt]` (the DSL variables right-to-left). -/
lemma inst_isSemitermBvar {wn wz wt : V} (hwn : IsSemiterm LAct 0 wn) (hwz : IsSemiterm LAct 0 wz) (hwt : IsSemiterm LAct 0 wt) :
    row_isSemitermBvar_as.map (instOuter LAct [wn, wz, wt]) = [ltFact wz wn, bvarFact wt wz] ∧
    instOuter LAct [wn, wz, wt] row_isSemitermBvar_c = tSigmaFact wn wt := by
  have hes : ∀ e ∈ ([wn, wz, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemitermBvar_as row_isSemitermBvar_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermFvar` — `“t x n. …”`, `m = 3` -/

noncomputable def row_isSemitermFvar_as : List V := [subst LAct (listToVec [bv 0, bv 1]) Pfvar]
noncomputable def row_isSemitermFvar_c : V := subst LAct (listToVec [bv 2, bv 0]) PtSigma

theorem quote_row_isSemitermFvar : (⌜Semiformula.lMap emb isSemitermFvarB⌝ : V) = impChain LAct row_isSemitermFvar_as row_isSemitermFvar_c := by
  unfold isSemitermFvarB row_isSemitermFvar_as row_isSemitermFvar_c Pfvar PtSigma
  all_goals row_shape

lemma isSemiformula_isSemitermFvar_as : ∀ A ∈ row_isSemitermFvar_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemitermFvar_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isSemitermFvar_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemitermFvar_c := by
  unfold row_isSemitermFvar_c
  exact isSemiformula_substRow isSemiformula_PtSigma _ (by rfl) (by row_entries)

/-- `isSemitermFvar` at the witnesses `[wn, wx, wt]` (the DSL variables right-to-left). -/
lemma inst_isSemitermFvar {wn wx wt : V} (hwn : IsSemiterm LAct 0 wn) (hwx : IsSemiterm LAct 0 wx) (hwt : IsSemiterm LAct 0 wt) :
    row_isSemitermFvar_as.map (instOuter LAct [wn, wx, wt]) = [fvarFact wt wx] ∧
    instOuter LAct [wn, wx, wt] row_isSemitermFvar_c = tSigmaFact wn wt := by
  have hes : ∀ e ∈ ([wn, wx, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemitermFvar_as row_isSemitermFvar_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermVecNil` — `“n. …”`, `m = 1` -/

noncomputable def row_isSemitermVecNil_as : List V := []
noncomputable def row_isSemitermVecNil_c : V := subst LAct (listToVec [(𝟎 : V), bv 0, (𝟎 : V)]) PtvSigma

theorem quote_row_isSemitermVecNil : (⌜Semiformula.lMap emb isSemitermVecNilB⌝ : V) = impChain LAct row_isSemitermVecNil_as row_isSemitermVecNil_c := by
  unfold isSemitermVecNilB row_isSemitermVecNil_as row_isSemitermVecNil_c PtvSigma
  all_goals row_shape

lemma isSemiformula_isSemitermVecNil_as : ∀ A ∈ row_isSemitermVecNil_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_isSemitermVecNil_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isSemitermVecNil_c : IsSemiformula LAct ((1 : ℕ) : V) row_isSemitermVecNil_c := by
  unfold row_isSemitermVecNil_c
  exact isSemiformula_substRow isSemiformula_PtvSigma _ (by rfl) (by row_entries)

/-- `isSemitermVecNil` at the witnesses `[wn]` (the DSL variables right-to-left). -/
lemma inst_isSemitermVecNil {wn : V} (hwn : IsSemiterm LAct 0 wn) :
    row_isSemitermVecNil_as.map (instOuter LAct [wn]) = [] ∧
    instOuter LAct [wn] row_isSemitermVecNil_c = tvSigmaFact (𝟎 : V) wn (𝟎 : V) := by
  have hes : ∀ e ∈ ([wn] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_nil _⟩)
  unfold row_isSemitermVecNil_as row_isSemitermVecNil_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtvSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermVecAdjoin` — `“u t w n k. …”`, `m = 5` -/

noncomputable def row_isSemitermVecAdjoin_as : List V := [subst LAct (listToVec [bv 4, bv 3, bv 2]) PtvPi, subst LAct (listToVec [bv 3, bv 1]) PtPi, subst LAct (listToVec [bv 0, bv 1, bv 2]) Padjoin]
noncomputable def row_isSemitermVecAdjoin_c : V := subst LAct (listToVec [bv 4 ^+ (𝟏 : V), bv 3, bv 0]) PtvSigma

theorem quote_row_isSemitermVecAdjoin : (⌜Semiformula.lMap emb isSemitermVecAdjoinB⌝ : V) = impChain LAct row_isSemitermVecAdjoin_as row_isSemitermVecAdjoin_c := by
  unfold isSemitermVecAdjoinB row_isSemitermVecAdjoin_as row_isSemitermVecAdjoin_c Padjoin PtPi PtvPi PtvSigma
  all_goals row_shape

lemma isSemiformula_isSemitermVecAdjoin_as : ∀ A ∈ row_isSemitermVecAdjoin_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_isSemitermVecAdjoin_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_isSemitermVecAdjoin_c : IsSemiformula LAct ((5 : ℕ) : V) row_isSemitermVecAdjoin_c := by
  unfold row_isSemitermVecAdjoin_c
  exact isSemiformula_substRow isSemiformula_PtvSigma _ (by rfl) (by row_entries)

/-- `isSemitermVecAdjoin` at the witnesses `[wk, wn, ww, wt, wu]` (the DSL variables right-to-left). -/
lemma inst_isSemitermVecAdjoin {wk wn ww wt wu : V} (hwk : IsSemiterm LAct 0 wk) (hwn : IsSemiterm LAct 0 wn) (hww : IsSemiterm LAct 0 ww) (hwt : IsSemiterm LAct 0 wt) (hwu : IsSemiterm LAct 0 wu) :
    row_isSemitermVecAdjoin_as.map (instOuter LAct [wk, wn, ww, wt, wu]) = [tvPiFact wk wn ww, tPiFact wn wt, adjFact wu wt ww] ∧
    instOuter LAct [wk, wn, ww, wt, wu] row_isSemitermVecAdjoin_c = tvSigmaFact (wk ^+ (𝟏 : V)) wn wu := by
  have hes : ∀ e ∈ ([wk, wn, ww, wt, wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_isSemitermVecAdjoin_as row_isSemitermVecAdjoin_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemiformulaSigmaPi` — `“p n. …”`, `m = 2` -/

noncomputable def row_isSemiformulaSigmaPi_as : List V := [subst LAct (listToVec [bv 1, bv 0]) Psigma]
noncomputable def row_isSemiformulaSigmaPi_c : V := subst LAct (listToVec [bv 1, bv 0]) Ppi

theorem quote_row_isSemiformulaSigmaPi : (⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ : V) = impChain LAct row_isSemiformulaSigmaPi_as row_isSemiformulaSigmaPi_c := by
  unfold isSemiformulaSigmaPiB row_isSemiformulaSigmaPi_as row_isSemiformulaSigmaPi_c Ppi Psigma
  all_goals row_shape

lemma isSemiformula_isSemiformulaSigmaPi_as : ∀ A ∈ row_isSemiformulaSigmaPi_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_isSemiformulaSigmaPi_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isSemiformulaSigmaPi_c : IsSemiformula LAct ((2 : ℕ) : V) row_isSemiformulaSigmaPi_c := by
  unfold row_isSemiformulaSigmaPi_c
  exact isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries)

/-- `isSemiformulaSigmaPi` at the witnesses `[wn, wp]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaSigmaPi {wn wp : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) :
    row_isSemiformulaSigmaPi_as.map (instOuter LAct [wn, wp]) = [sigmaFact wn wp] ∧
    instOuter LAct [wn, wp] row_isSemiformulaSigmaPi_c = piFact wn wp := by
  have hes : ∀ e ∈ ([wn, wp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_nil _⟩⟩)
  unfold row_isSemiformulaSigmaPi_as row_isSemiformulaSigmaPi_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermSigmaPiLAct` — `“t n. …”`, `m = 2` -/

noncomputable def row_isSemitermSigmaPiLAct_as : List V := [subst LAct (listToVec [bv 1, bv 0]) PtSigma]
noncomputable def row_isSemitermSigmaPiLAct_c : V := subst LAct (listToVec [bv 1, bv 0]) PtPi

theorem quote_row_isSemitermSigmaPiLAct : (⌜Semiformula.lMap emb isSemitermSigmaPiLActB⌝ : V) = impChain LAct row_isSemitermSigmaPiLAct_as row_isSemitermSigmaPiLAct_c := by
  unfold isSemitermSigmaPiLActB row_isSemitermSigmaPiLAct_as row_isSemitermSigmaPiLAct_c PtPi PtSigma
  all_goals row_shape

lemma isSemiformula_isSemitermSigmaPiLAct_as : ∀ A ∈ row_isSemitermSigmaPiLAct_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_isSemitermSigmaPiLAct_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtSigma _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isSemitermSigmaPiLAct_c : IsSemiformula LAct ((2 : ℕ) : V) row_isSemitermSigmaPiLAct_c := by
  unfold row_isSemitermSigmaPiLAct_c
  exact isSemiformula_substRow isSemiformula_PtPi _ (by rfl) (by row_entries)

/-- `isSemitermSigmaPiLAct` at the witnesses `[wn, wt]` (the DSL variables right-to-left). -/
lemma inst_isSemitermSigmaPiLAct {wn wt : V} (hwn : IsSemiterm LAct 0 wn) (hwt : IsSemiterm LAct 0 wt) :
    row_isSemitermSigmaPiLAct_as.map (instOuter LAct [wn, wt]) = [tSigmaFact wn wt] ∧
    instOuter LAct [wn, wt] row_isSemitermSigmaPiLAct_c = tPiFact wn wt := by
  have hes : ∀ e ∈ ([wn, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩)
  unfold row_isSemitermSigmaPiLAct_as row_isSemitermSigmaPiLAct_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtSigma (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermVecSigmaPiLAct` — `“v n k. …”`, `m = 3` -/

noncomputable def row_isSemitermVecSigmaPiLAct_as : List V := [subst LAct (listToVec [bv 2, bv 1, bv 0]) PtvSigma]
noncomputable def row_isSemitermVecSigmaPiLAct_c : V := subst LAct (listToVec [bv 2, bv 1, bv 0]) PtvPi

theorem quote_row_isSemitermVecSigmaPiLAct : (⌜Semiformula.lMap emb isSemitermVecSigmaPiLActB⌝ : V) = impChain LAct row_isSemitermVecSigmaPiLAct_as row_isSemitermVecSigmaPiLAct_c := by
  unfold isSemitermVecSigmaPiLActB row_isSemitermVecSigmaPiLAct_as row_isSemitermVecSigmaPiLAct_c PtvPi PtvSigma
  all_goals row_shape

lemma isSemiformula_isSemitermVecSigmaPiLAct_as : ∀ A ∈ row_isSemitermVecSigmaPiLAct_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isSemitermVecSigmaPiLAct_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvSigma _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isSemitermVecSigmaPiLAct_c : IsSemiformula LAct ((3 : ℕ) : V) row_isSemitermVecSigmaPiLAct_c := by
  unfold row_isSemitermVecSigmaPiLAct_c
  exact isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries)

/-- `isSemitermVecSigmaPiLAct` at the witnesses `[wk, wn, wv]` (the DSL variables right-to-left). -/
lemma inst_isSemitermVecSigmaPiLAct {wk wn wv : V} (hwk : IsSemiterm LAct 0 wk) (hwn : IsSemiterm LAct 0 wn) (hwv : IsSemiterm LAct 0 wv) :
    row_isSemitermVecSigmaPiLAct_as.map (instOuter LAct [wk, wn, wv]) = [tvSigmaFact wk wn wv] ∧
    instOuter LAct [wk, wn, wv] row_isSemitermVecSigmaPiLAct_c = tvPiFact wk wn wv := by
  have hes : ∀ e ∈ ([wk, wn, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isSemitermVecSigmaPiLAct_as row_isSemitermVecSigmaPiLAct_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtvSigma (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isUTermVecSigmaPiLAct` — `“v k. …”`, `m = 2` -/

noncomputable def row_isUTermVecSigmaPiLAct_as : List V := [subst LAct (listToVec [bv 1, bv 0]) PutvSigma]
noncomputable def row_isUTermVecSigmaPiLAct_c : V := subst LAct (listToVec [bv 1, bv 0]) PutvPi

theorem quote_row_isUTermVecSigmaPiLAct : (⌜Semiformula.lMap emb isUTermVecSigmaPiLActB⌝ : V) = impChain LAct row_isUTermVecSigmaPiLAct_as row_isUTermVecSigmaPiLAct_c := by
  unfold isUTermVecSigmaPiLActB row_isUTermVecSigmaPiLAct_as row_isUTermVecSigmaPiLAct_c PutvPi PutvSigma
  all_goals row_shape

lemma isSemiformula_isUTermVecSigmaPiLAct_as : ∀ A ∈ row_isUTermVecSigmaPiLAct_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_isUTermVecSigmaPiLAct_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvSigma _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isUTermVecSigmaPiLAct_c : IsSemiformula LAct ((2 : ℕ) : V) row_isUTermVecSigmaPiLAct_c := by
  unfold row_isUTermVecSigmaPiLAct_c
  exact isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries)

/-- `isUTermVecSigmaPiLAct` at the witnesses `[wk, wv]` (the DSL variables right-to-left). -/
lemma inst_isUTermVecSigmaPiLAct {wk wv : V} (hwk : IsSemiterm LAct 0 wk) (hwv : IsSemiterm LAct 0 wv) :
    row_isUTermVecSigmaPiLAct_as.map (instOuter LAct [wk, wv]) = [utvSigmaFact wk wv] ∧
    instOuter LAct [wk, wv] row_isUTermVecSigmaPiLAct_c = utvPiFact wk wv := by
  have hes : ∀ e ∈ ([wk, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩)
  unfold row_isUTermVecSigmaPiLAct_as row_isUTermVecSigmaPiLAct_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PutvSigma (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `zeroLtSucc` — `“y. …”`, `m = 1` -/

noncomputable def row_zeroLtSucc_as : List V := []
noncomputable def row_zeroLtSucc_c : V := subst LAct (listToVec [(𝟎 : V), bv 0 ^+ (𝟏 : V)]) Plt

theorem quote_row_zeroLtSucc : (⌜Semiformula.lMap emb zeroLtSuccB⌝ : V) = impChain LAct row_zeroLtSucc_as row_zeroLtSucc_c := by
  unfold zeroLtSuccB row_zeroLtSucc_as row_zeroLtSucc_c Plt
  all_goals row_shape

lemma isSemiformula_zeroLtSucc_as : ∀ A ∈ row_zeroLtSucc_as, IsSemiformula LAct ((1 : ℕ) : V) A := by
  unfold row_zeroLtSucc_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_zeroLtSucc_c : IsSemiformula LAct ((1 : ℕ) : V) row_zeroLtSucc_c := by
  unfold row_zeroLtSucc_c
  exact isSemiformula_substRow isSemiformula_Plt _ (by rfl) (by row_entries)

/-- `zeroLtSucc` at the witnesses `[wy]` (the DSL variables right-to-left). -/
lemma inst_zeroLtSucc {wy : V} (hwy : IsSemiterm LAct 0 wy) :
    row_zeroLtSucc_as.map (instOuter LAct [wy]) = [] ∧
    instOuter LAct [wy] row_zeroLtSucc_c = ltFact (𝟎 : V) (wy ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩)
  unfold row_zeroLtSucc_as row_zeroLtSucc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `succLtSucc` — `“y x. …”`, `m = 2` -/

noncomputable def row_succLtSucc_as : List V := [subst LAct (listToVec [bv 1, bv 0]) Plt]
noncomputable def row_succLtSucc_c : V := subst LAct (listToVec [bv 1 ^+ (𝟏 : V), bv 0 ^+ (𝟏 : V)]) Plt

theorem quote_row_succLtSucc : (⌜Semiformula.lMap emb succLtSuccB⌝ : V) = impChain LAct row_succLtSucc_as row_succLtSucc_c := by
  unfold succLtSuccB row_succLtSucc_as row_succLtSucc_c Plt
  all_goals row_shape

lemma isSemiformula_succLtSucc_as : ∀ A ∈ row_succLtSucc_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_succLtSucc_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Plt _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_succLtSucc_c : IsSemiformula LAct ((2 : ℕ) : V) row_succLtSucc_c := by
  unfold row_succLtSucc_c
  exact isSemiformula_substRow isSemiformula_Plt _ (by rfl) (by row_entries)

/-- `succLtSucc` at the witnesses `[wx, wy]` (the DSL variables right-to-left). -/
lemma inst_succLtSucc {wx wy : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_succLtSucc_as.map (instOuter LAct [wx, wy]) = [ltFact wx wy] ∧
    instOuter LAct [wx, wy] row_succLtSucc_c = ltFact (wx ^+ (𝟏 : V)) (wy ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_succLtSucc_as row_succLtSucc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isRelConst_eq` — `“ …”`, `m = 0` -/

noncomputable def row_isRelConst_eq_as : List V := []
noncomputable def row_isRelConst_eq_c : V := subst LAct (listToVec [cT 2, cT 0]) PisRel

theorem quote_row_isRelConst_eq : (⌜Semiformula.lMap emb isRelConst_eqB⌝ : V) = impChain LAct row_isRelConst_eq_as row_isRelConst_eq_c := by
  unfold row_isRelConst_eq_as row_isRelConst_eq_c PisRel
  rw [show isRelConst_eqB = (↑LAct.isRel : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 0] from rfl]
  all_goals row_shape

lemma isSemiformula_isRelConst_eq_as : ∀ A ∈ row_isRelConst_eq_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isRelConst_eq_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isRelConst_eq_c : IsSemiformula LAct ((0 : ℕ) : V) row_isRelConst_eq_c := by
  unfold row_isRelConst_eq_c
  exact isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries)

/-- `isRelConst_eq` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isRelConst_eq  :
    row_isRelConst_eq_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isRelConst_eq_c = isRelFact (cT 2) (cT 0) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isRelConst_eq_as row_isRelConst_eq_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isRelConst_lt` — `“ …”`, `m = 0` -/

noncomputable def row_isRelConst_lt_as : List V := []
noncomputable def row_isRelConst_lt_c : V := subst LAct (listToVec [cT 2, cT 1]) PisRel

theorem quote_row_isRelConst_lt : (⌜Semiformula.lMap emb isRelConst_ltB⌝ : V) = impChain LAct row_isRelConst_lt_as row_isRelConst_lt_c := by
  unfold row_isRelConst_lt_as row_isRelConst_lt_c PisRel
  rw [show isRelConst_ltB = (↑LAct.isRel : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 1] from rfl]
  all_goals row_shape

lemma isSemiformula_isRelConst_lt_as : ∀ A ∈ row_isRelConst_lt_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isRelConst_lt_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isRelConst_lt_c : IsSemiformula LAct ((0 : ℕ) : V) row_isRelConst_lt_c := by
  unfold row_isRelConst_lt_c
  exact isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries)

/-- `isRelConst_lt` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isRelConst_lt  :
    row_isRelConst_lt_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isRelConst_lt_c = isRelFact (cT 2) (cT 1) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isRelConst_lt_as row_isRelConst_lt_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFuncConst_zero` — `“ …”`, `m = 0` -/

noncomputable def row_isFuncConst_zero_as : List V := []
noncomputable def row_isFuncConst_zero_c : V := subst LAct (listToVec [cT 0, cT 0]) PisFunc

theorem quote_row_isFuncConst_zero : (⌜Semiformula.lMap emb isFuncConst_zeroB⌝ : V) = impChain LAct row_isFuncConst_zero_as row_isFuncConst_zero_c := by
  unfold row_isFuncConst_zero_as row_isFuncConst_zero_c PisFunc
  rw [show isFuncConst_zeroB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 0] from rfl]
  all_goals row_shape

lemma isSemiformula_isFuncConst_zero_as : ∀ A ∈ row_isFuncConst_zero_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isFuncConst_zero_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isFuncConst_zero_c : IsSemiformula LAct ((0 : ℕ) : V) row_isFuncConst_zero_c := by
  unfold row_isFuncConst_zero_c
  exact isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries)

/-- `isFuncConst_zero` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isFuncConst_zero  :
    row_isFuncConst_zero_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isFuncConst_zero_c = isFuncFact (cT 0) (cT 0) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isFuncConst_zero_as row_isFuncConst_zero_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFuncConst_one` — `“ …”`, `m = 0` -/

noncomputable def row_isFuncConst_one_as : List V := []
noncomputable def row_isFuncConst_one_c : V := subst LAct (listToVec [cT 0, cT 1]) PisFunc

theorem quote_row_isFuncConst_one : (⌜Semiformula.lMap emb isFuncConst_oneB⌝ : V) = impChain LAct row_isFuncConst_one_as row_isFuncConst_one_c := by
  unfold row_isFuncConst_one_as row_isFuncConst_one_c PisFunc
  rw [show isFuncConst_oneB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 1] from rfl]
  all_goals row_shape

lemma isSemiformula_isFuncConst_one_as : ∀ A ∈ row_isFuncConst_one_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isFuncConst_one_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isFuncConst_one_c : IsSemiformula LAct ((0 : ℕ) : V) row_isFuncConst_one_c := by
  unfold row_isFuncConst_one_c
  exact isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries)

/-- `isFuncConst_one` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isFuncConst_one  :
    row_isFuncConst_one_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isFuncConst_one_c = isFuncFact (cT 0) (cT 1) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isFuncConst_one_as row_isFuncConst_one_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFuncConst_add` — `“ …”`, `m = 0` -/

noncomputable def row_isFuncConst_add_as : List V := []
noncomputable def row_isFuncConst_add_c : V := subst LAct (listToVec [cT 2, cT 0]) PisFunc

theorem quote_row_isFuncConst_add : (⌜Semiformula.lMap emb isFuncConst_addB⌝ : V) = impChain LAct row_isFuncConst_add_as row_isFuncConst_add_c := by
  unfold row_isFuncConst_add_as row_isFuncConst_add_c PisFunc
  rw [show isFuncConst_addB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 0] from rfl]
  all_goals row_shape

lemma isSemiformula_isFuncConst_add_as : ∀ A ∈ row_isFuncConst_add_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isFuncConst_add_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isFuncConst_add_c : IsSemiformula LAct ((0 : ℕ) : V) row_isFuncConst_add_c := by
  unfold row_isFuncConst_add_c
  exact isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries)

/-- `isFuncConst_add` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isFuncConst_add  :
    row_isFuncConst_add_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isFuncConst_add_c = isFuncFact (cT 2) (cT 0) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isFuncConst_add_as row_isFuncConst_add_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFuncConst_mul` — `“ …”`, `m = 0` -/

noncomputable def row_isFuncConst_mul_as : List V := []
noncomputable def row_isFuncConst_mul_c : V := subst LAct (listToVec [cT 2, cT 1]) PisFunc

theorem quote_row_isFuncConst_mul : (⌜Semiformula.lMap emb isFuncConst_mulB⌝ : V) = impChain LAct row_isFuncConst_mul_as row_isFuncConst_mul_c := by
  unfold row_isFuncConst_mul_as row_isFuncConst_mul_c PisFunc
  rw [show isFuncConst_mulB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 1] from rfl]
  all_goals row_shape

lemma isSemiformula_isFuncConst_mul_as : ∀ A ∈ row_isFuncConst_mul_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isFuncConst_mul_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isFuncConst_mul_c : IsSemiformula LAct ((0 : ℕ) : V) row_isFuncConst_mul_c := by
  unfold row_isFuncConst_mul_c
  exact isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries)

/-- `isFuncConst_mul` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isFuncConst_mul  :
    row_isFuncConst_mul_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isFuncConst_mul_c = isFuncFact (cT 2) (cT 1) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isFuncConst_mul_as row_isFuncConst_mul_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFuncConst_cC` — `“ …”`, `m = 0` -/

noncomputable def row_isFuncConst_cC_as : List V := []
noncomputable def row_isFuncConst_cC_c : V := subst LAct (listToVec [cT 0, cT 2]) PisFunc

theorem quote_row_isFuncConst_cC : (⌜Semiformula.lMap emb isFuncConst_cCB⌝ : V) = impChain LAct row_isFuncConst_cC_as row_isFuncConst_cC_c := by
  unfold row_isFuncConst_cC_as row_isFuncConst_cC_c PisFunc
  rw [show isFuncConst_cCB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 2] from rfl]
  all_goals row_shape

lemma isSemiformula_isFuncConst_cC_as : ∀ A ∈ row_isFuncConst_cC_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isFuncConst_cC_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isFuncConst_cC_c : IsSemiformula LAct ((0 : ℕ) : V) row_isFuncConst_cC_c := by
  unfold row_isFuncConst_cC_c
  exact isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries)

/-- `isFuncConst_cC` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isFuncConst_cC  :
    row_isFuncConst_cC_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isFuncConst_cC_c = isFuncFact (cT 0) (cT 2) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isFuncConst_cC_as row_isFuncConst_cC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFuncConst_cD` — `“ …”`, `m = 0` -/

noncomputable def row_isFuncConst_cD_as : List V := []
noncomputable def row_isFuncConst_cD_c : V := subst LAct (listToVec [cT 0, cT 3]) PisFunc

theorem quote_row_isFuncConst_cD : (⌜Semiformula.lMap emb isFuncConst_cDB⌝ : V) = impChain LAct row_isFuncConst_cD_as row_isFuncConst_cD_c := by
  unfold row_isFuncConst_cD_as row_isFuncConst_cD_c PisFunc
  rw [show isFuncConst_cDB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 3] from rfl]
  all_goals row_shape

lemma isSemiformula_isFuncConst_cD_as : ∀ A ∈ row_isFuncConst_cD_as, IsSemiformula LAct ((0 : ℕ) : V) A := by
  unfold row_isFuncConst_cD_as
  exact (List.forall_mem_nil _)
lemma isSemiformula_isFuncConst_cD_c : IsSemiformula LAct ((0 : ℕ) : V) row_isFuncConst_cD_c := by
  unfold row_isFuncConst_cD_c
  exact isSemiformula_substRow isSemiformula_PisFunc _ (by rfl) (by row_entries)

/-- `isFuncConst_cD` at the witnesses `([] : List V)` (the DSL variables right-to-left). -/
lemma inst_isFuncConst_cD  :
    row_isFuncConst_cD_as.map (instOuter LAct ([] : List V)) = [] ∧
    instOuter LAct ([] : List V) row_isFuncConst_cD_c = isFuncFact (cT 0) (cT 3) := by
  have hes : ∀ e ∈ (([] : List V) : List V), IsSemiterm LAct 0 e := (List.forall_mem_nil _)
  unfold row_isFuncConst_cD_as row_isFuncConst_cD_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isUTermVecOfSemitermVecLAct` — `“v n k. …”`, `m = 3` -/

noncomputable def row_isUTermVecOfSemitermVecLAct_as : List V := [subst LAct (listToVec [bv 2, bv 1, bv 0]) PtvPi]
noncomputable def row_isUTermVecOfSemitermVecLAct_c : V := subst LAct (listToVec [bv 2, bv 0]) PutvSigma

theorem quote_row_isUTermVecOfSemitermVecLAct : (⌜Semiformula.lMap emb isUTermVecOfSemitermVecLActB⌝ : V) = impChain LAct row_isUTermVecOfSemitermVecLAct_as row_isUTermVecOfSemitermVecLAct_c := by
  unfold isUTermVecOfSemitermVecLActB row_isUTermVecOfSemitermVecLAct_as row_isUTermVecOfSemitermVecLAct_c PtvPi PutvSigma
  all_goals row_shape

lemma isSemiformula_isUTermVecOfSemitermVecLAct_as : ∀ A ∈ row_isUTermVecOfSemitermVecLAct_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_isUTermVecOfSemitermVecLAct_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_nil _⟩)
lemma isSemiformula_isUTermVecOfSemitermVecLAct_c : IsSemiformula LAct ((3 : ℕ) : V) row_isUTermVecOfSemitermVecLAct_c := by
  unfold row_isUTermVecOfSemitermVecLAct_c
  exact isSemiformula_substRow isSemiformula_PutvSigma _ (by rfl) (by row_entries)

/-- `isUTermVecOfSemitermVecLAct` at the witnesses `[wk, wn, wv]` (the DSL variables right-to-left). -/
lemma inst_isUTermVecOfSemitermVecLAct {wk wn wv : V} (hwk : IsSemiterm LAct 0 wk) (hwn : IsSemiterm LAct 0 wn) (hwv : IsSemiterm LAct 0 wv) :
    row_isUTermVecOfSemitermVecLAct_as.map (instOuter LAct [wk, wn, wv]) = [tvPiFact wk wn wv] ∧
    instOuter LAct [wk, wn, wv] row_isUTermVecOfSemitermVecLAct_c = utvSigmaFact wk wv := by
  have hes : ∀ e ∈ ([wk, wn, wv] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isUTermVecOfSemitermVecLAct_as row_isUTermVecOfSemitermVecLAct_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isSemitermVecQVec` — `“u w m n. …”`, `m = 4` -/

noncomputable def row_isSemitermVecQVec_as : List V := [subst LAct (listToVec [bv 3, bv 2, bv 1]) PtvPi, subst LAct (listToVec [bv 0, bv 1]) PqVecG]
noncomputable def row_isSemitermVecQVec_c : V := subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2 ^+ (𝟏 : V), bv 0]) PtvSigma

theorem quote_row_isSemitermVecQVec : (⌜Semiformula.lMap emb isSemitermVecQVecB⌝ : V) = impChain LAct row_isSemitermVecQVec_as row_isSemitermVecQVec_c := by
  unfold isSemitermVecQVecB row_isSemitermVecQVec_as row_isSemitermVecQVec_c PqVecG PtvPi PtvSigma
  all_goals row_shape

lemma isSemiformula_isSemitermVecQVec_as : ∀ A ∈ row_isSemitermVecQVec_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_isSemitermVecQVec_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PtvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_isSemitermVecQVec_c : IsSemiformula LAct ((4 : ℕ) : V) row_isSemitermVecQVec_c := by
  unfold row_isSemitermVecQVec_c
  exact isSemiformula_substRow isSemiformula_PtvSigma _ (by rfl) (by row_entries)

/-- `isSemitermVecQVec` at the witnesses `[wn, wm, ww, wu]` (the DSL variables right-to-left). -/
lemma inst_isSemitermVecQVec {wn wm ww wu : V} (hwn : IsSemiterm LAct 0 wn) (hwm : IsSemiterm LAct 0 wm) (hww : IsSemiterm LAct 0 ww) (hwu : IsSemiterm LAct 0 wu) :
    row_isSemitermVecQVec_as.map (instOuter LAct [wn, wm, ww, wu]) = [tvPiFact wn wm ww, qVecFact wu ww] ∧
    instOuter LAct [wn, wm, ww, wu] row_isSemitermVecQVec_c = tvSigmaFact (wn ^+ (𝟏 : V)) (wm ^+ (𝟏 : V)) wu := by
  have hes : ∀ e ∈ ([wn, wm, ww, wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwm, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_isSemitermVecQVec_as row_isSemitermVecQVec_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PqVecG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PtvSigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `substs1Substs` — `“y w t p. …”`, `m = 4` -/

noncomputable def row_substs1Substs_as : List V := [subst LAct (listToVec [bv 1, bv 2, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 0, bv 2, bv 3]) Psubsts1G]
noncomputable def row_substs1Substs_c : V := subst LAct (listToVec [bv 0, bv 1, bv 3]) PsubstsG

theorem quote_row_substs1Substs : (⌜Semiformula.lMap emb substs1SubstsB⌝ : V) = impChain LAct row_substs1Substs_as row_substs1Substs_c := by
  unfold substs1SubstsB row_substs1Substs_as row_substs1Substs_c Padjoin Psubsts1G PsubstsG
  all_goals row_shape

lemma isSemiformula_substs1Substs_as : ∀ A ∈ row_substs1Substs_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_substs1Substs_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Psubsts1G _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_substs1Substs_c : IsSemiformula LAct ((4 : ℕ) : V) row_substs1Substs_c := by
  unfold row_substs1Substs_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)

/-- `substs1Substs` at the witnesses `[wp, wt, ww, wy]` (the DSL variables right-to-left). -/
lemma inst_substs1Substs {wp wt ww wy : V} (hwp : IsSemiterm LAct 0 wp) (hwt : IsSemiterm LAct 0 wt) (hww : IsSemiterm LAct 0 ww) (hwy : IsSemiterm LAct 0 wy) :
    row_substs1Substs_as.map (instOuter LAct [wp, wt, ww, wy]) = [adjFact ww wt (𝟎 : V), substs1Fact wy wt wp] ∧
    instOuter LAct [wp, wt, ww, wy] row_substs1Substs_c = substFact wy ww wp := by
  have hes : ∀ e ∈ ([wp, wt, ww, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_substs1Substs_as row_substs1Substs_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psubsts1G (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `negRel` — `“y r v R k. …”`, `m = 5` -/

noncomputable def row_negRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negRel_c : V := subst LAct (listToVec [bv 0, bv 4, bv 3, bv 2]) Pnrel

theorem quote_row_negRel : (⌜Semiformula.lMap emb negRelB⌝ : V) = impChain LAct row_negRel_as row_negRel_c := by
  unfold negRelB row_negRel_as row_negRel_c PisRel PnegG Pnrel Prel PutvPi
  all_goals row_shape

lemma isSemiformula_negRel_as : ∀ A ∈ row_negRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_negRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_negRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_negRel_c := by
  unfold row_negRel_c
  exact isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)

/-- `negRel` at the witnesses `[wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negRel {wk wR wv wr wy : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negRel_as.map (instOuter LAct [wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, negFact wy wr] ∧
    instOuter LAct [wk, wR, wv, wr, wy] row_negRel_c = nrelFact wy wk wR wv := by
  have hes : ∀ e ∈ ([wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negRel_as row_negRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `negNRel` — `“y r v R k. …”`, `m = 5` -/

noncomputable def row_negNRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negNRel_c : V := subst LAct (listToVec [bv 0, bv 4, bv 3, bv 2]) Prel

theorem quote_row_negNRel : (⌜Semiformula.lMap emb negNRelB⌝ : V) = impChain LAct row_negNRel_as row_negNRel_c := by
  unfold negNRelB row_negNRel_as row_negNRel_c PisRel PnegG Pnrel Prel PutvPi
  all_goals row_shape

lemma isSemiformula_negNRel_as : ∀ A ∈ row_negNRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_negNRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_negNRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_negNRel_c := by
  unfold row_negNRel_c
  exact isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)

/-- `negNRel` at the witnesses `[wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negNRel {wk wR wv wr wy : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negNRel_as.map (instOuter LAct [wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, negFact wy wr] ∧
    instOuter LAct [wk, wR, wv, wr, wy] row_negNRel_c = relFact wy wk wR wv := by
  have hes : ∀ e ∈ ([wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negNRel_as row_negNRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `negVerum` — `“y r. …”`, `m = 2` -/

noncomputable def row_negVerum_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negVerum_c : V := subst LAct (listToVec [bv 0]) Pfalsum

theorem quote_row_negVerum : (⌜Semiformula.lMap emb negVerumB⌝ : V) = impChain LAct row_negVerum_as row_negVerum_c := by
  unfold negVerumB row_negVerum_as row_negVerum_c Pfalsum PnegG Pverum
  all_goals row_shape

lemma isSemiformula_negVerum_as : ∀ A ∈ row_negVerum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_negVerum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_negVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_negVerum_c := by
  unfold row_negVerum_c
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries)

/-- `negVerum` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negVerum {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negVerum_as.map (instOuter LAct [wr, wy]) = [verumFact wr, negFact wy wr] ∧
    instOuter LAct [wr, wy] row_negVerum_c = falsumFact wy := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_negVerum_as row_negVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `negFalsum` — `“y r. …”`, `m = 2` -/

noncomputable def row_negFalsum_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negFalsum_c : V := subst LAct (listToVec [bv 0]) Pverum

theorem quote_row_negFalsum : (⌜Semiformula.lMap emb negFalsumB⌝ : V) = impChain LAct row_negFalsum_as row_negFalsum_c := by
  unfold negFalsumB row_negFalsum_as row_negFalsum_c Pfalsum PnegG Pverum
  all_goals row_shape

lemma isSemiformula_negFalsum_as : ∀ A ∈ row_negFalsum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_negFalsum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_negFalsum_c : IsSemiformula LAct ((2 : ℕ) : V) row_negFalsum_c := by
  unfold row_negFalsum_c
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries)

/-- `negFalsum` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negFalsum {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negFalsum_as.map (instOuter LAct [wr, wy]) = [falsumFact wr, negFact wy wr] ∧
    instOuter LAct [wr, wy] row_negFalsum_c = verumFact wy := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_negFalsum_as row_negFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `negAnd` — `“y r q p n. …”`, `m = 5` -/

noncomputable def row_negAnd_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Pand, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negAnd_body : V := subst LAct (listToVec [bv 1, bv 5]) PnegG ^⋏ (subst LAct (listToVec [bv 0, bv 4]) PnegG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Por)
noncomputable def row_negAnd_R : V := ^∃ row_negAnd_body
noncomputable def row_negAnd_c : V := ^∃ row_negAnd_R

theorem quote_row_negAnd : (⌜Semiformula.lMap emb negAndB⌝ : V) = impChain LAct row_negAnd_as row_negAnd_c := by
  unfold negAndB row_negAnd_as row_negAnd_c row_negAnd_R row_negAnd_body Pand PnegG Por Ppi
  all_goals row_shape

lemma isSemiformula_negAnd_as : ∀ A ∈ row_negAnd_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_negAnd_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_negAnd_c : IsSemiformula LAct ((5 : ℕ) : V) row_negAnd_c := by
  unfold row_negAnd_c row_negAnd_R row_negAnd_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_negAnd_R : IsSemiformula LAct ((6 : ℕ) : V) row_negAnd_R := by
  unfold row_negAnd_R row_negAnd_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_negAnd_body : IsSemiformula LAct ((7 : ℕ) : V) row_negAnd_body := by
  unfold row_negAnd_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩
lemma row_negAnd_R_eq : (row_negAnd_R : V) = exsIter 1 row_negAnd_body := rfl

/-- `negAnd` at the witnesses `[wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negAnd {wn wp wq wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negAnd_as.map (instOuter LAct [wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, negFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wq, wr, wy] row_negAnd_body) = negFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (negFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] wq) ^⋏ (orFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negAnd_as row_negAnd_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Por (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Por shift_Por (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `negOr` — `“y r q p n. …”`, `m = 5` -/

noncomputable def row_negOr_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Por, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negOr_body : V := subst LAct (listToVec [bv 1, bv 5]) PnegG ^⋏ (subst LAct (listToVec [bv 0, bv 4]) PnegG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Pand)
noncomputable def row_negOr_R : V := ^∃ row_negOr_body
noncomputable def row_negOr_c : V := ^∃ row_negOr_R

theorem quote_row_negOr : (⌜Semiformula.lMap emb negOrB⌝ : V) = impChain LAct row_negOr_as row_negOr_c := by
  unfold negOrB row_negOr_as row_negOr_c row_negOr_R row_negOr_body Pand PnegG Por Ppi
  all_goals row_shape

lemma isSemiformula_negOr_as : ∀ A ∈ row_negOr_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_negOr_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_negOr_c : IsSemiformula LAct ((5 : ℕ) : V) row_negOr_c := by
  unfold row_negOr_c row_negOr_R row_negOr_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_negOr_R : IsSemiformula LAct ((6 : ℕ) : V) row_negOr_R := by
  unfold row_negOr_R row_negOr_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_negOr_body : IsSemiformula LAct ((7 : ℕ) : V) row_negOr_body := by
  unfold row_negOr_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩
lemma row_negOr_R_eq : (row_negOr_R : V) = exsIter 1 row_negOr_body := rfl

/-- `negOr` at the witnesses `[wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negOr {wn wp wq wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negOr_as.map (instOuter LAct [wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, negFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wq, wr, wy] row_negOr_body) = negFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (negFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] wq) ^⋏ (andFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negOr_as row_negOr_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Pand (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pand shift_Pand (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `negAll` — `“y r p n. …”`, `m = 4` -/

noncomputable def row_negAll_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pall, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negAll_body : V := subst LAct (listToVec [bv 0, bv 3]) PnegG ^⋏ subst LAct (listToVec [bv 1, bv 0]) Pexs
noncomputable def row_negAll_R : V := row_negAll_body
noncomputable def row_negAll_c : V := ^∃ row_negAll_R

theorem quote_row_negAll : (⌜Semiformula.lMap emb negAllB⌝ : V) = impChain LAct row_negAll_as row_negAll_c := by
  unfold negAllB row_negAll_as row_negAll_c row_negAll_R row_negAll_body Pall Pexs PnegG Ppi
  all_goals row_shape

lemma isSemiformula_negAll_as : ∀ A ∈ row_negAll_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_negAll_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_negAll_c : IsSemiformula LAct ((4 : ℕ) : V) row_negAll_c := by
  unfold row_negAll_c row_negAll_R row_negAll_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_negAll_R : IsSemiformula LAct ((5 : ℕ) : V) row_negAll_R := by
  unfold row_negAll_R row_negAll_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩
lemma isSemiformula_negAll_body : IsSemiformula LAct ((5 : ℕ) : V) row_negAll_body := by
  unfold row_negAll_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩
lemma row_negAll_R_eq : (row_negAll_R : V) = exsIter 0 row_negAll_body := rfl

/-- `negAll` at the witnesses `[wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negAll {wn wp wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negAll_as.map (instOuter LAct [wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, negFact wy wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wn, wp, wr, wy] row_negAll_body) = negFact (^&((0 : ℕ) : V)) (termShift LAct wp) ^⋏ (exsFact (termShift LAct wy) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_negAll_as row_negAll_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Pexs (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Pexs shift_Pexs (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `negExs` — `“y r p n. …”`, `m = 4` -/

noncomputable def row_negExs_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pexs, subst LAct (listToVec [bv 0, bv 1]) PnegG]
noncomputable def row_negExs_body : V := subst LAct (listToVec [bv 0, bv 3]) PnegG ^⋏ subst LAct (listToVec [bv 1, bv 0]) Pall
noncomputable def row_negExs_R : V := row_negExs_body
noncomputable def row_negExs_c : V := ^∃ row_negExs_R

theorem quote_row_negExs : (⌜Semiformula.lMap emb negExsB⌝ : V) = impChain LAct row_negExs_as row_negExs_c := by
  unfold negExsB row_negExs_as row_negExs_c row_negExs_R row_negExs_body Pall Pexs PnegG Ppi
  all_goals row_shape

lemma isSemiformula_negExs_as : ∀ A ∈ row_negExs_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_negExs_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_negExs_c : IsSemiformula LAct ((4 : ℕ) : V) row_negExs_c := by
  unfold row_negExs_c row_negExs_R row_negExs_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_negExs_R : IsSemiformula LAct ((5 : ℕ) : V) row_negExs_R := by
  unfold row_negExs_R row_negExs_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩
lemma isSemiformula_negExs_body : IsSemiformula LAct ((5 : ℕ) : V) row_negExs_body := by
  unfold row_negExs_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩
lemma row_negExs_R_eq : (row_negExs_R : V) = exsIter 0 row_negExs_body := rfl

/-- `negExs` at the witnesses `[wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negExs {wn wp wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negExs_as.map (instOuter LAct [wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, negFact wy wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wn, wp, wr, wy] row_negExs_body) = negFact (^&((0 : ℕ) : V)) (termShift LAct wp) ^⋏ (allFact (termShift LAct wy) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_negExs_as row_negExs_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PnegG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Pall (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PnegG shift_PnegG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Pall shift_Pall (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `substsRel` — `“y r v R k w. …”`, `m = 6` -/

noncomputable def row_substsRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 0, bv 5, bv 1]) PsubstsG]
noncomputable def row_substsRel_body : V := subst LAct (listToVec [bv 0, bv 5, bv 6, bv 3]) PtsvG ^⋏ subst LAct (listToVec [bv 1, bv 5, bv 4, bv 0]) Prel
noncomputable def row_substsRel_R : V := row_substsRel_body
noncomputable def row_substsRel_c : V := ^∃ row_substsRel_R

theorem quote_row_substsRel : (⌜Semiformula.lMap emb substsRelB⌝ : V) = impChain LAct row_substsRel_as row_substsRel_c := by
  unfold substsRelB row_substsRel_as row_substsRel_c row_substsRel_R row_substsRel_body PisRel Prel PsubstsG PtsvG PutvPi
  all_goals row_shape

lemma isSemiformula_substsRel_as : ∀ A ∈ row_substsRel_as, IsSemiformula LAct ((6 : ℕ) : V) A := by
  unfold row_substsRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_substsRel_c : IsSemiformula LAct ((6 : ℕ) : V) row_substsRel_c := by
  unfold row_substsRel_c row_substsRel_R row_substsRel_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_substsRel_R : IsSemiformula LAct ((7 : ℕ) : V) row_substsRel_R := by
  unfold row_substsRel_R row_substsRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩
lemma isSemiformula_substsRel_body : IsSemiformula LAct ((7 : ℕ) : V) row_substsRel_body := by
  unfold row_substsRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩
lemma row_substsRel_R_eq : (row_substsRel_R : V) = exsIter 0 row_substsRel_body := rfl

/-- `substsRel` at the witnesses `[ww, wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsRel {ww wk wR wv wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsRel_as.map (instOuter LAct [ww, wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, substFact wy ww wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [ww, wk, wR, wv, wr, wy] row_substsRel_body) = tsvFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct ww) (termShift LAct wv) ^⋏ (relFact (termShift LAct wy) (termShift LAct wk) (termShift LAct wR) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([ww, wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_substsRel_as row_substsRel_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PtsvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Prel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Prel shift_Prel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwR 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1, freeIterT_closed 0 hww 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `substsNRel` — `“y r v R k w. …”`, `m = 6` -/

noncomputable def row_substsNRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 0, bv 5, bv 1]) PsubstsG]
noncomputable def row_substsNRel_body : V := subst LAct (listToVec [bv 0, bv 5, bv 6, bv 3]) PtsvG ^⋏ subst LAct (listToVec [bv 1, bv 5, bv 4, bv 0]) Pnrel
noncomputable def row_substsNRel_R : V := row_substsNRel_body
noncomputable def row_substsNRel_c : V := ^∃ row_substsNRel_R

theorem quote_row_substsNRel : (⌜Semiformula.lMap emb substsNRelB⌝ : V) = impChain LAct row_substsNRel_as row_substsNRel_c := by
  unfold substsNRelB row_substsNRel_as row_substsNRel_c row_substsNRel_R row_substsNRel_body PisRel Pnrel PsubstsG PtsvG PutvPi
  all_goals row_shape

lemma isSemiformula_substsNRel_as : ∀ A ∈ row_substsNRel_as, IsSemiformula LAct ((6 : ℕ) : V) A := by
  unfold row_substsNRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_substsNRel_c : IsSemiformula LAct ((6 : ℕ) : V) row_substsNRel_c := by
  unfold row_substsNRel_c row_substsNRel_R row_substsNRel_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_substsNRel_R : IsSemiformula LAct ((7 : ℕ) : V) row_substsNRel_R := by
  unfold row_substsNRel_R row_substsNRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩
lemma isSemiformula_substsNRel_body : IsSemiformula LAct ((7 : ℕ) : V) row_substsNRel_body := by
  unfold row_substsNRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩
lemma row_substsNRel_R_eq : (row_substsNRel_R : V) = exsIter 0 row_substsNRel_body := rfl

/-- `substsNRel` at the witnesses `[ww, wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsNRel {ww wk wR wv wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsNRel_as.map (instOuter LAct [ww, wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, substFact wy ww wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [ww, wk, wR, wv, wr, wy] row_substsNRel_body) = tsvFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct ww) (termShift LAct wv) ^⋏ (nrelFact (termShift LAct wy) (termShift LAct wk) (termShift LAct wR) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([ww, wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_substsNRel_as row_substsNRel_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PtsvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Pnrel shift_Pnrel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwR 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1, freeIterT_closed 0 hww 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `substsVerum` — `“y r w. …”`, `m = 3` -/

noncomputable def row_substsVerum_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG]
noncomputable def row_substsVerum_c : V := subst LAct (listToVec [bv 0]) Pverum

theorem quote_row_substsVerum : (⌜Semiformula.lMap emb substsVerumB⌝ : V) = impChain LAct row_substsVerum_as row_substsVerum_c := by
  unfold substsVerumB row_substsVerum_as row_substsVerum_c PsubstsG Pverum
  all_goals row_shape

lemma isSemiformula_substsVerum_as : ∀ A ∈ row_substsVerum_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_substsVerum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_substsVerum_c : IsSemiformula LAct ((3 : ℕ) : V) row_substsVerum_c := by
  unfold row_substsVerum_c
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries)

/-- `substsVerum` at the witnesses `[ww, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsVerum {ww wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsVerum_as.map (instOuter LAct [ww, wr, wy]) = [verumFact wr, substFact wy ww wr] ∧
    instOuter LAct [ww, wr, wy] row_substsVerum_c = verumFact wy := by
  have hes : ∀ e ∈ ([ww, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_substsVerum_as row_substsVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `substsFalsum` — `“y r w. …”`, `m = 3` -/

noncomputable def row_substsFalsum_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG]
noncomputable def row_substsFalsum_c : V := subst LAct (listToVec [bv 0]) Pfalsum

theorem quote_row_substsFalsum : (⌜Semiformula.lMap emb substsFalsumB⌝ : V) = impChain LAct row_substsFalsum_as row_substsFalsum_c := by
  unfold substsFalsumB row_substsFalsum_as row_substsFalsum_c Pfalsum PsubstsG
  all_goals row_shape

lemma isSemiformula_substsFalsum_as : ∀ A ∈ row_substsFalsum_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_substsFalsum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_substsFalsum_c : IsSemiformula LAct ((3 : ℕ) : V) row_substsFalsum_c := by
  unfold row_substsFalsum_c
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries)

/-- `substsFalsum` at the witnesses `[ww, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsFalsum {ww wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsFalsum_as.map (instOuter LAct [ww, wr, wy]) = [falsumFact wr, substFact wy ww wr] ∧
    instOuter LAct [ww, wr, wy] row_substsFalsum_c = falsumFact wy := by
  have hes : ∀ e ∈ ([ww, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_substsFalsum_as row_substsFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `substsAnd` — `“y r q p n w. …”`, `m = 6` -/

noncomputable def row_substsAnd_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Pand, subst LAct (listToVec [bv 0, bv 5, bv 1]) PsubstsG]
noncomputable def row_substsAnd_body : V := subst LAct (listToVec [bv 1, bv 7, bv 5]) PsubstsG ^⋏ (subst LAct (listToVec [bv 0, bv 7, bv 4]) PsubstsG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Pand)
noncomputable def row_substsAnd_R : V := ^∃ row_substsAnd_body
noncomputable def row_substsAnd_c : V := ^∃ row_substsAnd_R

theorem quote_row_substsAnd : (⌜Semiformula.lMap emb substsAndB⌝ : V) = impChain LAct row_substsAnd_as row_substsAnd_c := by
  unfold substsAndB row_substsAnd_as row_substsAnd_c row_substsAnd_R row_substsAnd_body Pand Ppi PsubstsG
  all_goals row_shape

lemma isSemiformula_substsAnd_as : ∀ A ∈ row_substsAnd_as, IsSemiformula LAct ((6 : ℕ) : V) A := by
  unfold row_substsAnd_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_substsAnd_c : IsSemiformula LAct ((6 : ℕ) : V) row_substsAnd_c := by
  unfold row_substsAnd_c row_substsAnd_R row_substsAnd_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_substsAnd_R : IsSemiformula LAct ((7 : ℕ) : V) row_substsAnd_R := by
  unfold row_substsAnd_R row_substsAnd_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_substsAnd_body : IsSemiformula LAct ((8 : ℕ) : V) row_substsAnd_body := by
  unfold row_substsAnd_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩
lemma row_substsAnd_R_eq : (row_substsAnd_R : V) = exsIter 1 row_substsAnd_body := rfl

/-- `substsAnd` at the witnesses `[ww, wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsAnd {ww wn wp wq wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsAnd_as.map (instOuter LAct [ww, wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, substFact wy ww wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [ww, wn, wp, wq, wr, wy] row_substsAnd_body) = substFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] ww) ((termShift LAct)^[2] wp) ^⋏ (substFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] ww) ((termShift LAct)^[2] wq) ^⋏ (andFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([ww, wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_substsAnd_as row_substsAnd_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Pand (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pand shift_Pand (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hww 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `substsOr` — `“y r q p n w. …”`, `m = 6` -/

noncomputable def row_substsOr_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Por, subst LAct (listToVec [bv 0, bv 5, bv 1]) PsubstsG]
noncomputable def row_substsOr_body : V := subst LAct (listToVec [bv 1, bv 7, bv 5]) PsubstsG ^⋏ (subst LAct (listToVec [bv 0, bv 7, bv 4]) PsubstsG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Por)
noncomputable def row_substsOr_R : V := ^∃ row_substsOr_body
noncomputable def row_substsOr_c : V := ^∃ row_substsOr_R

theorem quote_row_substsOr : (⌜Semiformula.lMap emb substsOrB⌝ : V) = impChain LAct row_substsOr_as row_substsOr_c := by
  unfold substsOrB row_substsOr_as row_substsOr_c row_substsOr_R row_substsOr_body Por Ppi PsubstsG
  all_goals row_shape

lemma isSemiformula_substsOr_as : ∀ A ∈ row_substsOr_as, IsSemiformula LAct ((6 : ℕ) : V) A := by
  unfold row_substsOr_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_substsOr_c : IsSemiformula LAct ((6 : ℕ) : V) row_substsOr_c := by
  unfold row_substsOr_c row_substsOr_R row_substsOr_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_substsOr_R : IsSemiformula LAct ((7 : ℕ) : V) row_substsOr_R := by
  unfold row_substsOr_R row_substsOr_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_substsOr_body : IsSemiformula LAct ((8 : ℕ) : V) row_substsOr_body := by
  unfold row_substsOr_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩
lemma row_substsOr_R_eq : (row_substsOr_R : V) = exsIter 1 row_substsOr_body := rfl

/-- `substsOr` at the witnesses `[ww, wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsOr {ww wn wp wq wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsOr_as.map (instOuter LAct [ww, wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, substFact wy ww wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [ww, wn, wp, wq, wr, wy] row_substsOr_body) = substFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] ww) ((termShift LAct)^[2] wp) ^⋏ (substFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] ww) ((termShift LAct)^[2] wq) ^⋏ (orFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([ww, wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_substsOr_as row_substsOr_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Por (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Por shift_Por (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hww 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `substsAll` — `“y r p n w. …”`, `m = 5` -/

noncomputable def row_substsAll_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pall, subst LAct (listToVec [bv 0, bv 4, bv 1]) PsubstsG]
noncomputable def row_substsAll_body : V := subst LAct (listToVec [bv 1, bv 6]) PqVecG ^⋏ (subst LAct (listToVec [bv 0, bv 1, bv 4]) PsubstsG ^⋏ subst LAct (listToVec [bv 2, bv 0]) Pall)
noncomputable def row_substsAll_R : V := ^∃ row_substsAll_body
noncomputable def row_substsAll_c : V := ^∃ row_substsAll_R

theorem quote_row_substsAll : (⌜Semiformula.lMap emb substsAllB⌝ : V) = impChain LAct row_substsAll_as row_substsAll_c := by
  unfold substsAllB row_substsAll_as row_substsAll_c row_substsAll_R row_substsAll_body Pall Ppi PqVecG PsubstsG
  all_goals row_shape

lemma isSemiformula_substsAll_as : ∀ A ∈ row_substsAll_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_substsAll_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_substsAll_c : IsSemiformula LAct ((5 : ℕ) : V) row_substsAll_c := by
  unfold row_substsAll_c row_substsAll_R row_substsAll_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_substsAll_R : IsSemiformula LAct ((6 : ℕ) : V) row_substsAll_R := by
  unfold row_substsAll_R row_substsAll_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_substsAll_body : IsSemiformula LAct ((7 : ℕ) : V) row_substsAll_body := by
  unfold row_substsAll_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩
lemma row_substsAll_R_eq : (row_substsAll_R : V) = exsIter 1 row_substsAll_body := rfl

/-- `substsAll` at the witnesses `[ww, wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsAll {ww wn wp wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsAll_as.map (instOuter LAct [ww, wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, substFact wy ww wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [ww, wn, wp, wr, wy] row_substsAll_body) = qVecFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] ww) ^⋏ (substFact (^&((0 : ℕ) : V)) (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (allFact ((termShift LAct)^[2] wy) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([ww, wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_substsAll_as row_substsAll_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PqVecG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Pall (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pall shift_Pall (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hww 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `substsExs` — `“y r p n w. …”`, `m = 5` -/

noncomputable def row_substsExs_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pexs, subst LAct (listToVec [bv 0, bv 4, bv 1]) PsubstsG]
noncomputable def row_substsExs_body : V := subst LAct (listToVec [bv 1, bv 6]) PqVecG ^⋏ (subst LAct (listToVec [bv 0, bv 1, bv 4]) PsubstsG ^⋏ subst LAct (listToVec [bv 2, bv 0]) Pexs)
noncomputable def row_substsExs_R : V := ^∃ row_substsExs_body
noncomputable def row_substsExs_c : V := ^∃ row_substsExs_R

theorem quote_row_substsExs : (⌜Semiformula.lMap emb substsExsB⌝ : V) = impChain LAct row_substsExs_as row_substsExs_c := by
  unfold substsExsB row_substsExs_as row_substsExs_c row_substsExs_R row_substsExs_body Pexs Ppi PqVecG PsubstsG
  all_goals row_shape

lemma isSemiformula_substsExs_as : ∀ A ∈ row_substsExs_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_substsExs_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_substsExs_c : IsSemiformula LAct ((5 : ℕ) : V) row_substsExs_c := by
  unfold row_substsExs_c row_substsExs_R row_substsExs_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_substsExs_R : IsSemiformula LAct ((6 : ℕ) : V) row_substsExs_R := by
  unfold row_substsExs_R row_substsExs_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_substsExs_body : IsSemiformula LAct ((7 : ℕ) : V) row_substsExs_body := by
  unfold row_substsExs_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩
lemma row_substsExs_R_eq : (row_substsExs_R : V) = exsIter 1 row_substsExs_body := rfl

/-- `substsExs` at the witnesses `[ww, wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsExs {ww wn wp wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsExs_as.map (instOuter LAct [ww, wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, substFact wy ww wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [ww, wn, wp, wr, wy] row_substsExs_body) = qVecFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] ww) ^⋏ (substFact (^&((0 : ℕ) : V)) (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (exsFact ((termShift LAct)^[2] wy) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([ww, wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_substsExs_as row_substsExs_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PqVecG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Pexs (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pexs shift_Pexs (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hww 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `shiftRel` — `“y r v R k. …”`, `m = 5` -/

noncomputable def row_shiftRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftRel_body : V := subst LAct (listToVec [bv 0, bv 5, bv 3]) PtshvG ^⋏ subst LAct (listToVec [bv 1, bv 5, bv 4, bv 0]) Prel
noncomputable def row_shiftRel_R : V := row_shiftRel_body
noncomputable def row_shiftRel_c : V := ^∃ row_shiftRel_R

theorem quote_row_shiftRel : (⌜Semiformula.lMap emb shiftRelB⌝ : V) = impChain LAct row_shiftRel_as row_shiftRel_c := by
  unfold shiftRelB row_shiftRel_as row_shiftRel_c row_shiftRel_R row_shiftRel_body PisRel Prel PshiftG PtshvG PutvPi
  all_goals row_shape

lemma isSemiformula_shiftRel_as : ∀ A ∈ row_shiftRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_shiftRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_shiftRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_shiftRel_c := by
  unfold row_shiftRel_c row_shiftRel_R row_shiftRel_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_shiftRel_R : IsSemiformula LAct ((6 : ℕ) : V) row_shiftRel_R := by
  unfold row_shiftRel_R row_shiftRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩
lemma isSemiformula_shiftRel_body : IsSemiformula LAct ((6 : ℕ) : V) row_shiftRel_body := by
  unfold row_shiftRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩
lemma row_shiftRel_R_eq : (row_shiftRel_R : V) = exsIter 0 row_shiftRel_body := rfl

/-- `shiftRel` at the witnesses `[wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftRel {wk wR wv wr wy : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftRel_as.map (instOuter LAct [wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, shiftFact wy wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, wR, wv, wr, wy] row_shiftRel_body) = tshvFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wv) ^⋏ (relFact (termShift LAct wy) (termShift LAct wk) (termShift LAct wR) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_shiftRel_as row_shiftRel_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PtshvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Prel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Prel shift_Prel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwR 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `shiftNRel` — `“y r v R k. …”`, `m = 5` -/

noncomputable def row_shiftNRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftNRel_body : V := subst LAct (listToVec [bv 0, bv 5, bv 3]) PtshvG ^⋏ subst LAct (listToVec [bv 1, bv 5, bv 4, bv 0]) Pnrel
noncomputable def row_shiftNRel_R : V := row_shiftNRel_body
noncomputable def row_shiftNRel_c : V := ^∃ row_shiftNRel_R

theorem quote_row_shiftNRel : (⌜Semiformula.lMap emb shiftNRelB⌝ : V) = impChain LAct row_shiftNRel_as row_shiftNRel_c := by
  unfold shiftNRelB row_shiftNRel_as row_shiftNRel_c row_shiftNRel_R row_shiftNRel_body PisRel Pnrel PshiftG PtshvG PutvPi
  all_goals row_shape

lemma isSemiformula_shiftNRel_as : ∀ A ∈ row_shiftNRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_shiftNRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_shiftNRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_shiftNRel_c := by
  unfold row_shiftNRel_c row_shiftNRel_R row_shiftNRel_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_shiftNRel_R : IsSemiformula LAct ((6 : ℕ) : V) row_shiftNRel_R := by
  unfold row_shiftNRel_R row_shiftNRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩
lemma isSemiformula_shiftNRel_body : IsSemiformula LAct ((6 : ℕ) : V) row_shiftNRel_body := by
  unfold row_shiftNRel_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩
lemma row_shiftNRel_R_eq : (row_shiftNRel_R : V) = exsIter 0 row_shiftNRel_body := rfl

/-- `shiftNRel` at the witnesses `[wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftNRel {wk wR wv wr wy : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftNRel_as.map (instOuter LAct [wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, shiftFact wy wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wk, wR, wv, wr, wy] row_shiftNRel_body) = tshvFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wv) ^⋏ (nrelFact (termShift LAct wy) (termShift LAct wk) (termShift LAct wR) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_shiftNRel_as row_shiftNRel_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PtshvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Pnrel shift_Pnrel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwR 1, freeIterT_closed 0 hwk 1, freeIterT_closed 0 hwv 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `shiftVerum` — `“y r. …”`, `m = 2` -/

noncomputable def row_shiftVerum_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftVerum_c : V := subst LAct (listToVec [bv 0]) Pverum

theorem quote_row_shiftVerum : (⌜Semiformula.lMap emb shiftVerumB⌝ : V) = impChain LAct row_shiftVerum_as row_shiftVerum_c := by
  unfold shiftVerumB row_shiftVerum_as row_shiftVerum_c PshiftG Pverum
  all_goals row_shape

lemma isSemiformula_shiftVerum_as : ∀ A ∈ row_shiftVerum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_shiftVerum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_shiftVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_shiftVerum_c := by
  unfold row_shiftVerum_c
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries)

/-- `shiftVerum` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftVerum {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftVerum_as.map (instOuter LAct [wr, wy]) = [verumFact wr, shiftFact wy wr] ∧
    instOuter LAct [wr, wy] row_shiftVerum_c = verumFact wy := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_shiftVerum_as row_shiftVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `shiftFalsum` — `“y r. …”`, `m = 2` -/

noncomputable def row_shiftFalsum_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftFalsum_c : V := subst LAct (listToVec [bv 0]) Pfalsum

theorem quote_row_shiftFalsum : (⌜Semiformula.lMap emb shiftFalsumB⌝ : V) = impChain LAct row_shiftFalsum_as row_shiftFalsum_c := by
  unfold shiftFalsumB row_shiftFalsum_as row_shiftFalsum_c Pfalsum PshiftG
  all_goals row_shape

lemma isSemiformula_shiftFalsum_as : ∀ A ∈ row_shiftFalsum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_shiftFalsum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_shiftFalsum_c : IsSemiformula LAct ((2 : ℕ) : V) row_shiftFalsum_c := by
  unfold row_shiftFalsum_c
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries)

/-- `shiftFalsum` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftFalsum {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftFalsum_as.map (instOuter LAct [wr, wy]) = [falsumFact wr, shiftFact wy wr] ∧
    instOuter LAct [wr, wy] row_shiftFalsum_c = falsumFact wy := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_shiftFalsum_as row_shiftFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `shiftAnd` — `“y r q p n. …”`, `m = 5` -/

noncomputable def row_shiftAnd_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Pand, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftAnd_body : V := subst LAct (listToVec [bv 1, bv 5]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 4]) PshiftG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Pand)
noncomputable def row_shiftAnd_R : V := ^∃ row_shiftAnd_body
noncomputable def row_shiftAnd_c : V := ^∃ row_shiftAnd_R

theorem quote_row_shiftAnd : (⌜Semiformula.lMap emb shiftAndB⌝ : V) = impChain LAct row_shiftAnd_as row_shiftAnd_c := by
  unfold shiftAndB row_shiftAnd_as row_shiftAnd_c row_shiftAnd_R row_shiftAnd_body Pand Ppi PshiftG
  all_goals row_shape

lemma isSemiformula_shiftAnd_as : ∀ A ∈ row_shiftAnd_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_shiftAnd_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_shiftAnd_c : IsSemiformula LAct ((5 : ℕ) : V) row_shiftAnd_c := by
  unfold row_shiftAnd_c row_shiftAnd_R row_shiftAnd_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_shiftAnd_R : IsSemiformula LAct ((6 : ℕ) : V) row_shiftAnd_R := by
  unfold row_shiftAnd_R row_shiftAnd_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_shiftAnd_body : IsSemiformula LAct ((7 : ℕ) : V) row_shiftAnd_body := by
  unfold row_shiftAnd_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩
lemma row_shiftAnd_R_eq : (row_shiftAnd_R : V) = exsIter 1 row_shiftAnd_body := rfl

/-- `shiftAnd` at the witnesses `[wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftAnd {wn wp wq wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftAnd_as.map (instOuter LAct [wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, shiftFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wq, wr, wy] row_shiftAnd_body) = shiftFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (shiftFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] wq) ^⋏ (andFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_shiftAnd_as row_shiftAnd_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Pand (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pand shift_Pand (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `shiftOr` — `“y r q p n. …”`, `m = 5` -/

noncomputable def row_shiftOr_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Por, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftOr_body : V := subst LAct (listToVec [bv 1, bv 5]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 4]) PshiftG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Por)
noncomputable def row_shiftOr_R : V := ^∃ row_shiftOr_body
noncomputable def row_shiftOr_c : V := ^∃ row_shiftOr_R

theorem quote_row_shiftOr : (⌜Semiformula.lMap emb shiftOrB⌝ : V) = impChain LAct row_shiftOr_as row_shiftOr_c := by
  unfold shiftOrB row_shiftOr_as row_shiftOr_c row_shiftOr_R row_shiftOr_body Por Ppi PshiftG
  all_goals row_shape

lemma isSemiformula_shiftOr_as : ∀ A ∈ row_shiftOr_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_shiftOr_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_shiftOr_c : IsSemiformula LAct ((5 : ℕ) : V) row_shiftOr_c := by
  unfold row_shiftOr_c row_shiftOr_R row_shiftOr_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_shiftOr_R : IsSemiformula LAct ((6 : ℕ) : V) row_shiftOr_R := by
  unfold row_shiftOr_R row_shiftOr_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_shiftOr_body : IsSemiformula LAct ((7 : ℕ) : V) row_shiftOr_body := by
  unfold row_shiftOr_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩
lemma row_shiftOr_R_eq : (row_shiftOr_R : V) = exsIter 1 row_shiftOr_body := rfl

/-- `shiftOr` at the witnesses `[wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftOr {wn wp wq wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftOr_as.map (instOuter LAct [wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, shiftFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wq, wr, wy] row_shiftOr_body) = shiftFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (shiftFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] wq) ^⋏ (orFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_shiftOr_as row_shiftOr_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Por (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Por shift_Por (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `shiftAll` — `“y r p n. …”`, `m = 4` -/

noncomputable def row_shiftAll_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pall, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftAll_body : V := subst LAct (listToVec [bv 0, bv 3]) PshiftG ^⋏ subst LAct (listToVec [bv 1, bv 0]) Pall
noncomputable def row_shiftAll_R : V := row_shiftAll_body
noncomputable def row_shiftAll_c : V := ^∃ row_shiftAll_R

theorem quote_row_shiftAll : (⌜Semiformula.lMap emb shiftAllB⌝ : V) = impChain LAct row_shiftAll_as row_shiftAll_c := by
  unfold shiftAllB row_shiftAll_as row_shiftAll_c row_shiftAll_R row_shiftAll_body Pall Ppi PshiftG
  all_goals row_shape

lemma isSemiformula_shiftAll_as : ∀ A ∈ row_shiftAll_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_shiftAll_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_shiftAll_c : IsSemiformula LAct ((4 : ℕ) : V) row_shiftAll_c := by
  unfold row_shiftAll_c row_shiftAll_R row_shiftAll_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_shiftAll_R : IsSemiformula LAct ((5 : ℕ) : V) row_shiftAll_R := by
  unfold row_shiftAll_R row_shiftAll_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩
lemma isSemiformula_shiftAll_body : IsSemiformula LAct ((5 : ℕ) : V) row_shiftAll_body := by
  unfold row_shiftAll_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩
lemma row_shiftAll_R_eq : (row_shiftAll_R : V) = exsIter 0 row_shiftAll_body := rfl

/-- `shiftAll` at the witnesses `[wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftAll {wn wp wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftAll_as.map (instOuter LAct [wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, shiftFact wy wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wn, wp, wr, wy] row_shiftAll_body) = shiftFact (^&((0 : ℕ) : V)) (termShift LAct wp) ^⋏ (allFact (termShift LAct wy) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_shiftAll_as row_shiftAll_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Pall (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Pall shift_Pall (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `shiftExs` — `“y r p n. …”`, `m = 4` -/

noncomputable def row_shiftExs_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pexs, subst LAct (listToVec [bv 0, bv 1]) PshiftG]
noncomputable def row_shiftExs_body : V := subst LAct (listToVec [bv 0, bv 3]) PshiftG ^⋏ subst LAct (listToVec [bv 1, bv 0]) Pexs
noncomputable def row_shiftExs_R : V := row_shiftExs_body
noncomputable def row_shiftExs_c : V := ^∃ row_shiftExs_R

theorem quote_row_shiftExs : (⌜Semiformula.lMap emb shiftExsB⌝ : V) = impChain LAct row_shiftExs_as row_shiftExs_c := by
  unfold shiftExsB row_shiftExs_as row_shiftExs_c row_shiftExs_R row_shiftExs_body Pexs Ppi PshiftG
  all_goals row_shape

lemma isSemiformula_shiftExs_as : ∀ A ∈ row_shiftExs_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_shiftExs_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_shiftExs_c : IsSemiformula LAct ((4 : ℕ) : V) row_shiftExs_c := by
  unfold row_shiftExs_c row_shiftExs_R row_shiftExs_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩)
lemma isSemiformula_shiftExs_R : IsSemiformula LAct ((5 : ℕ) : V) row_shiftExs_R := by
  unfold row_shiftExs_R row_shiftExs_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩
lemma isSemiformula_shiftExs_body : IsSemiformula LAct ((5 : ℕ) : V) row_shiftExs_body := by
  unfold row_shiftExs_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩
lemma row_shiftExs_R_eq : (row_shiftExs_R : V) = exsIter 0 row_shiftExs_body := rfl

/-- `shiftExs` at the witnesses `[wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftExs {wn wp wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftExs_as.map (instOuter LAct [wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, shiftFact wy wr] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wn, wp, wr, wy] row_shiftExs_body) = shiftFact (^&((0 : ℕ) : V)) (termShift LAct wp) ^⋏ (exsFact (termShift LAct wy) (^&((0 : ℕ) : V))) := by
  have hes : ∀ e ∈ ([wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_shiftExs_as row_shiftExs_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 1 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 1 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 1 _ isSemiformula_Pexs (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 1 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 1 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 1 _ isSemiformula_Pexs shift_Pexs (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwp 1, freeIterT_closed 0 hwy 1]
    try rfl

/-! ### `freeRel` — `“y r v R k. …”`, `m = 5` -/

noncomputable def row_freeRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeRel_inner : V := subst LAct (listToVec [bv 1, bv 8, bv 6]) PtshvG ^⋏ (subst LAct (listToVec [bv 0, bv 8, bv 2, bv 1]) PtsvG ^⋏ subst LAct (listToVec [bv 4, bv 8, bv 7, bv 0]) Prel)
noncomputable def row_freeRel_body : V := subst LAct (listToVec [bv 1, (𝟎 : V)]) Pfvar ^⋏ (subst LAct (listToVec [bv 0, bv 1, (𝟎 : V)]) Padjoin ^⋏ (^∃ ^∃ row_freeRel_inner))
noncomputable def row_freeRel_R : V := ^∃ row_freeRel_body
noncomputable def row_freeRel_c : V := ^∃ row_freeRel_R

theorem quote_row_freeRel : (⌜Semiformula.lMap emb freeRelB⌝ : V) = impChain LAct row_freeRel_as row_freeRel_c := by
  unfold freeRelB row_freeRel_as row_freeRel_c row_freeRel_R row_freeRel_body row_freeRel_inner Padjoin PfreeG Pfvar PisRel Prel PtshvG PtsvG PutvPi
  all_goals row_shape

lemma isSemiformula_freeRel_as : ∀ A ∈ row_freeRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_freeRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_freeRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_freeRel_c := by
  unfold row_freeRel_c row_freeRel_R row_freeRel_body row_freeRel_inner
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))⟩⟩))
lemma isSemiformula_freeRel_R : IsSemiformula LAct ((6 : ℕ) : V) row_freeRel_R := by
  unfold row_freeRel_R row_freeRel_body row_freeRel_inner
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))⟩⟩)
lemma isSemiformula_freeRel_body : IsSemiformula LAct ((7 : ℕ) : V) row_freeRel_body := by
  unfold row_freeRel_body row_freeRel_inner
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))⟩⟩
lemma row_freeRel_R_eq : (row_freeRel_R : V) = exsIter 1 row_freeRel_body := rfl

/-- `freeRel` at the witnesses `[wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeRel {wk wR wv wr wy : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeRel_as.map (instOuter LAct [wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, freeFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wk, wR, wv, wr, wy] row_freeRel_body) = fvarFact (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (adjFact (^&((0 : ℕ) : V)) (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (^∃ ^∃ (freeIterAt 2 2 (subst LAct (listToVec [bv 1, wk, wv]) PtshvG ^⋏ (subst LAct (listToVec [bv 0, wk, bv 2, bv 1]) PtsvG ^⋏ subst LAct (listToVec [wy, wk, wR, bv 0]) Prel))))) ∧
    freeIter LAct 2 (freeIterAt 2 2 (subst LAct (listToVec [bv 1, wk, wv]) PtshvG ^⋏ (subst LAct (listToVec [bv 0, wk, bv 2, bv 1]) PtsvG ^⋏ subst LAct (listToVec [wy, wk, wR, bv 0]) Prel))) = tshvFact (^&((1 : ℕ) : V)) ((termShift LAct)^[4] wk) ((termShift LAct)^[4] wv) ^⋏ (tsvFact (^&((0 : ℕ) : V)) ((termShift LAct)^[4] wk) (^&((2 : ℕ) : V)) (^&((1 : ℕ) : V)) ^⋏ (relFact ((termShift LAct)^[4] wy) ((termShift LAct)^[4] wk) ((termShift LAct)^[4] wR) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_freeRel_as row_freeRel_body row_freeRel_inner
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_, ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))) hes, instOuterAt_exs 2 _ (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩)) hes, instOuterAt_exs 3 _ (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩) hes, instOuterAt_and 4 _ (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 4 _ (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_Pfvar (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 4 _ isSemiformula_PtshvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 4 _ isSemiformula_PtsvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 4 _ isSemiformula_Prel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩))), freeIter_exs2 2 (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩⟩), freeIter_subst_listToVec' 2 _ isSemiformula_Pfvar shift_Pfvar (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Padjoin shift_Padjoin (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 (isSemiterm_qqZero_LAct 0) 2, iterate_termShift_qqZero 2]
    try rfl
  · rw [freeIterAt_and 2 2 (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩), freeIterAt_and 2 2 (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)), freeIterAt_subst_listToVec 2 2 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries), freeIterAt_subst_listToVec 2 2 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries), freeIterAt_subst_listToVec 2 2 _ isSemiformula_Prel shift_Prel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv_lt 2 2 0 (by norm_num), freeIterT_bv_lt 2 2 1 (by norm_num), freeIterT_bv_ge 2 2 2 (by norm_num) (by norm_num), freeIterT_closed 2 hwR 2, freeIterT_closed 2 hwk 2, freeIterT_closed 2 hwv 2, freeIterT_closed 2 hwy 2]
    try simp only [Nat.reduceSub]
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Prel shift_Prel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 (t := ^&((0 : ℕ) : V)) (by simp) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwR 2) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwk 2) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwv 2) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwy 2) 2]
    try simp only [termShift_iterate_fvar, ← Function.iterate_add_apply, ← Nat.cast_add, Nat.reduceAdd]
    try rfl

/-! ### `freeNRel` — `“y r v R k. …”`, `m = 5` -/

noncomputable def row_freeNRel_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeNRel_inner : V := subst LAct (listToVec [bv 1, bv 8, bv 6]) PtshvG ^⋏ (subst LAct (listToVec [bv 0, bv 8, bv 2, bv 1]) PtsvG ^⋏ subst LAct (listToVec [bv 4, bv 8, bv 7, bv 0]) Pnrel)
noncomputable def row_freeNRel_body : V := subst LAct (listToVec [bv 1, (𝟎 : V)]) Pfvar ^⋏ (subst LAct (listToVec [bv 0, bv 1, (𝟎 : V)]) Padjoin ^⋏ (^∃ ^∃ row_freeNRel_inner))
noncomputable def row_freeNRel_R : V := ^∃ row_freeNRel_body
noncomputable def row_freeNRel_c : V := ^∃ row_freeNRel_R

theorem quote_row_freeNRel : (⌜Semiformula.lMap emb freeNRelB⌝ : V) = impChain LAct row_freeNRel_as row_freeNRel_c := by
  unfold freeNRelB row_freeNRel_as row_freeNRel_c row_freeNRel_R row_freeNRel_body row_freeNRel_inner Padjoin PfreeG Pfvar PisRel Pnrel PtshvG PtsvG PutvPi
  all_goals row_shape

lemma isSemiformula_freeNRel_as : ∀ A ∈ row_freeNRel_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_freeNRel_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PisRel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PutvPi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_freeNRel_c : IsSemiformula LAct ((5 : ℕ) : V) row_freeNRel_c := by
  unfold row_freeNRel_c row_freeNRel_R row_freeNRel_body row_freeNRel_inner
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))⟩⟩))
lemma isSemiformula_freeNRel_R : IsSemiformula LAct ((6 : ℕ) : V) row_freeNRel_R := by
  unfold row_freeNRel_R row_freeNRel_body row_freeNRel_inner
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))⟩⟩)
lemma isSemiformula_freeNRel_body : IsSemiformula LAct ((7 : ℕ) : V) row_freeNRel_body := by
  unfold row_freeNRel_body row_freeNRel_inner
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))⟩⟩
lemma row_freeNRel_R_eq : (row_freeNRel_R : V) = exsIter 1 row_freeNRel_body := rfl

/-- `freeNRel` at the witnesses `[wk, wR, wv, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeNRel {wk wR wv wr wy : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeNRel_as.map (instOuter LAct [wk, wR, wv, wr, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, freeFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wk, wR, wv, wr, wy] row_freeNRel_body) = fvarFact (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (adjFact (^&((0 : ℕ) : V)) (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (^∃ ^∃ (freeIterAt 2 2 (subst LAct (listToVec [bv 1, wk, wv]) PtshvG ^⋏ (subst LAct (listToVec [bv 0, wk, bv 2, bv 1]) PtsvG ^⋏ subst LAct (listToVec [wy, wk, wR, bv 0]) Pnrel))))) ∧
    freeIter LAct 2 (freeIterAt 2 2 (subst LAct (listToVec [bv 1, wk, wv]) PtshvG ^⋏ (subst LAct (listToVec [bv 0, wk, bv 2, bv 1]) PtsvG ^⋏ subst LAct (listToVec [wy, wk, wR, bv 0]) Pnrel))) = tshvFact (^&((1 : ℕ) : V)) ((termShift LAct)^[4] wk) ((termShift LAct)^[4] wv) ^⋏ (tsvFact (^&((0 : ℕ) : V)) ((termShift LAct)^[4] wk) (^&((2 : ℕ) : V)) (^&((1 : ℕ) : V)) ^⋏ (nrelFact ((termShift LAct)^[4] wy) ((termShift LAct)^[4] wk) ((termShift LAct)^[4] wR) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wk, wR, wv, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_freeNRel_as row_freeNRel_body row_freeNRel_inner
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_, ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))) hes, instOuterAt_exs 2 _ (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩)) hes, instOuterAt_exs 3 _ (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩) hes, instOuterAt_and 4 _ (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 4 _ (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_Pfvar (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 4 _ isSemiformula_PtshvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 4 _ isSemiformula_PtsvG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 4 _ isSemiformula_Pnrel (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩))), freeIter_exs2 2 (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩⟩), freeIter_subst_listToVec' 2 _ isSemiformula_Pfvar shift_Pfvar (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Padjoin shift_Padjoin (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 (isSemiterm_qqZero_LAct 0) 2, iterate_termShift_qqZero 2]
    try rfl
  · rw [freeIterAt_and 2 2 (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩), freeIterAt_and 2 2 (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)), freeIterAt_subst_listToVec 2 2 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries), freeIterAt_subst_listToVec 2 2 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries), freeIterAt_subst_listToVec 2 2 _ isSemiformula_Pnrel shift_Pnrel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv_lt 2 2 0 (by norm_num), freeIterT_bv_lt 2 2 1 (by norm_num), freeIterT_bv_ge 2 2 2 (by norm_num) (by norm_num), freeIterT_closed 2 hwR 2, freeIterT_closed 2 hwk 2, freeIterT_closed 2 hwv 2, freeIterT_closed 2 hwy 2]
    try simp only [Nat.reduceSub]
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PtshvG shift_PtshvG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PtsvG shift_PtsvG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pnrel shift_Pnrel (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 (t := ^&((0 : ℕ) : V)) (by simp) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwR 2) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwk 2) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwv 2) 2, freeIterT_closed 0 (isSemiterm_iterate_termShift hwy 2) 2]
    try simp only [termShift_iterate_fvar, ← Function.iterate_add_apply, ← Nat.cast_add, Nat.reduceAdd]
    try rfl

/-! ### `freeVerum` — `“y r. …”`, `m = 2` -/

noncomputable def row_freeVerum_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeVerum_c : V := subst LAct (listToVec [bv 0]) Pverum

theorem quote_row_freeVerum : (⌜Semiformula.lMap emb freeVerumB⌝ : V) = impChain LAct row_freeVerum_as row_freeVerum_c := by
  unfold freeVerumB row_freeVerum_as row_freeVerum_c PfreeG Pverum
  all_goals row_shape

lemma isSemiformula_freeVerum_as : ∀ A ∈ row_freeVerum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_freeVerum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_freeVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_freeVerum_c := by
  unfold row_freeVerum_c
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entries)

/-- `freeVerum` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeVerum {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeVerum_as.map (instOuter LAct [wr, wy]) = [verumFact wr, freeFact wy wr] ∧
    instOuter LAct [wr, wy] row_freeVerum_c = verumFact wy := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_freeVerum_as row_freeVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `freeFalsum` — `“y r. …”`, `m = 2` -/

noncomputable def row_freeFalsum_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeFalsum_c : V := subst LAct (listToVec [bv 0]) Pfalsum

theorem quote_row_freeFalsum : (⌜Semiformula.lMap emb freeFalsumB⌝ : V) = impChain LAct row_freeFalsum_as row_freeFalsum_c := by
  unfold freeFalsumB row_freeFalsum_as row_freeFalsum_c Pfalsum PfreeG
  all_goals row_shape

lemma isSemiformula_freeFalsum_as : ∀ A ∈ row_freeFalsum_as, IsSemiformula LAct ((2 : ℕ) : V) A := by
  unfold row_freeFalsum_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩)
lemma isSemiformula_freeFalsum_c : IsSemiformula LAct ((2 : ℕ) : V) row_freeFalsum_c := by
  unfold row_freeFalsum_c
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entries)

/-- `freeFalsum` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeFalsum {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeFalsum_as.map (instOuter LAct [wr, wy]) = [falsumFact wr, freeFact wy wr] ∧
    instOuter LAct [wr, wy] row_freeFalsum_c = falsumFact wy := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_freeFalsum_as row_freeFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `freeAnd` — `“y r q p n. …”`, `m = 5` -/

noncomputable def row_freeAnd_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Pand, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeAnd_body : V := subst LAct (listToVec [bv 1, bv 5]) PfreeG ^⋏ (subst LAct (listToVec [bv 0, bv 4]) PfreeG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Pand)
noncomputable def row_freeAnd_R : V := ^∃ row_freeAnd_body
noncomputable def row_freeAnd_c : V := ^∃ row_freeAnd_R

theorem quote_row_freeAnd : (⌜Semiformula.lMap emb freeAndB⌝ : V) = impChain LAct row_freeAnd_as row_freeAnd_c := by
  unfold freeAndB row_freeAnd_as row_freeAnd_c row_freeAnd_R row_freeAnd_body Pand PfreeG Ppi
  all_goals row_shape

lemma isSemiformula_freeAnd_as : ∀ A ∈ row_freeAnd_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_freeAnd_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_freeAnd_c : IsSemiformula LAct ((5 : ℕ) : V) row_freeAnd_c := by
  unfold row_freeAnd_c row_freeAnd_R row_freeAnd_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_freeAnd_R : IsSemiformula LAct ((6 : ℕ) : V) row_freeAnd_R := by
  unfold row_freeAnd_R row_freeAnd_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_freeAnd_body : IsSemiformula LAct ((7 : ℕ) : V) row_freeAnd_body := by
  unfold row_freeAnd_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩⟩
lemma row_freeAnd_R_eq : (row_freeAnd_R : V) = exsIter 1 row_freeAnd_body := rfl

/-- `freeAnd` at the witnesses `[wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeAnd {wn wp wq wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeAnd_as.map (instOuter LAct [wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, freeFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wq, wr, wy] row_freeAnd_body) = freeFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (freeFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] wq) ^⋏ (andFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_freeAnd_as row_freeAnd_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Pand (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PfreeG shift_PfreeG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PfreeG shift_PfreeG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Pand shift_Pand (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `freeOr` — `“y r q p n. …”`, `m = 5` -/

noncomputable def row_freeOr_as : List V := [subst LAct (listToVec [bv 4, bv 3]) Ppi, subst LAct (listToVec [bv 4, bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 3, bv 2]) Por, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeOr_body : V := subst LAct (listToVec [bv 1, bv 5]) PfreeG ^⋏ (subst LAct (listToVec [bv 0, bv 4]) PfreeG ^⋏ subst LAct (listToVec [bv 2, bv 1, bv 0]) Por)
noncomputable def row_freeOr_R : V := ^∃ row_freeOr_body
noncomputable def row_freeOr_c : V := ^∃ row_freeOr_R

theorem quote_row_freeOr : (⌜Semiformula.lMap emb freeOrB⌝ : V) = impChain LAct row_freeOr_as row_freeOr_c := by
  unfold freeOrB row_freeOr_as row_freeOr_c row_freeOr_R row_freeOr_body PfreeG Por Ppi
  all_goals row_shape

lemma isSemiformula_freeOr_as : ∀ A ∈ row_freeOr_as, IsSemiformula LAct ((5 : ℕ) : V) A := by
  unfold row_freeOr_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩⟩)
lemma isSemiformula_freeOr_c : IsSemiformula LAct ((5 : ℕ) : V) row_freeOr_c := by
  unfold row_freeOr_c row_freeOr_R row_freeOr_body
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩))
lemma isSemiformula_freeOr_R : IsSemiformula LAct ((6 : ℕ) : V) row_freeOr_R := by
  unfold row_freeOr_R row_freeOr_body
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩)
lemma isSemiformula_freeOr_body : IsSemiformula LAct ((7 : ℕ) : V) row_freeOr_body := by
  unfold row_freeOr_body
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩⟩
lemma row_freeOr_R_eq : (row_freeOr_R : V) = exsIter 1 row_freeOr_body := rfl

/-- `freeOr` at the witnesses `[wn, wp, wq, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeOr {wn wp wq wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeOr_as.map (instOuter LAct [wn, wp, wq, wr, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, freeFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wq, wr, wy] row_freeOr_body) = freeFact (^&((1 : ℕ) : V)) ((termShift LAct)^[2] wp) ^⋏ (freeFact (^&((0 : ℕ) : V)) ((termShift LAct)^[2] wq) ^⋏ (orFact ((termShift LAct)^[2] wy) (^&((1 : ℕ) : V)) (^&((0 : ℕ) : V)))) := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_freeOr_as row_freeOr_body
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Por (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 2 _ isSemiformula_PfreeG shift_PfreeG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_PfreeG shift_PfreeG (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Por shift_Por (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 hwp 2, freeIterT_closed 0 hwq 2, freeIterT_closed 0 hwy 2]
    try rfl

/-! ### `freeAll` — `“y r p n. …”`, `m = 4` -/

noncomputable def row_freeAll_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pall, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeAll_inner : V := subst LAct (listToVec [bv 2, bv 3]) PqVecG ^⋏ (subst LAct (listToVec [bv 1, bv 7]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG ^⋏ subst LAct (listToVec [bv 5, bv 0]) Pall))
noncomputable def row_freeAll_body : V := subst LAct (listToVec [bv 1, (𝟎 : V)]) Pfvar ^⋏ (subst LAct (listToVec [bv 0, bv 1, (𝟎 : V)]) Padjoin ^⋏ (^∃ ^∃ ^∃ row_freeAll_inner))
noncomputable def row_freeAll_R : V := ^∃ row_freeAll_body
noncomputable def row_freeAll_c : V := ^∃ row_freeAll_R

theorem quote_row_freeAll : (⌜Semiformula.lMap emb freeAllB⌝ : V) = impChain LAct row_freeAll_as row_freeAll_c := by
  unfold freeAllB row_freeAll_as row_freeAll_c row_freeAll_R row_freeAll_body row_freeAll_inner Padjoin Pall PfreeG Pfvar Ppi PqVecG PshiftG PsubstsG
  all_goals row_shape

lemma isSemiformula_freeAll_as : ∀ A ∈ row_freeAll_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_freeAll_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_freeAll_c : IsSemiformula LAct ((4 : ℕ) : V) row_freeAll_c := by
  unfold row_freeAll_c row_freeAll_R row_freeAll_body row_freeAll_inner
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))⟩⟩))
lemma isSemiformula_freeAll_R : IsSemiformula LAct ((5 : ℕ) : V) row_freeAll_R := by
  unfold row_freeAll_R row_freeAll_body row_freeAll_inner
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))⟩⟩)
lemma isSemiformula_freeAll_body : IsSemiformula LAct ((6 : ℕ) : V) row_freeAll_body := by
  unfold row_freeAll_body row_freeAll_inner
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))⟩⟩
lemma row_freeAll_R_eq : (row_freeAll_R : V) = exsIter 1 row_freeAll_body := rfl

/-- `freeAll` at the witnesses `[wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeAll {wn wp wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeAll_as.map (instOuter LAct [wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, freeFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wr, wy] row_freeAll_body) = fvarFact (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (adjFact (^&((0 : ℕ) : V)) (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (^∃ ^∃ ^∃ (freeIterAt 3 2 (subst LAct (listToVec [bv 2, bv 3]) PqVecG ^⋏ (subst LAct (listToVec [bv 1, wp]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG ^⋏ subst LAct (listToVec [wy, bv 0]) Pall)))))) ∧
    freeIter LAct 3 (freeIterAt 3 2 (subst LAct (listToVec [bv 2, bv 3]) PqVecG ^⋏ (subst LAct (listToVec [bv 1, wp]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG ^⋏ subst LAct (listToVec [wy, bv 0]) Pall)))) = qVecFact (^&((2 : ℕ) : V)) (^&((3 : ℕ) : V)) ^⋏ (shiftFact (^&((1 : ℕ) : V)) ((termShift LAct)^[5] wp) ^⋏ (substFact (^&((0 : ℕ) : V)) (^&((2 : ℕ) : V)) (^&((1 : ℕ) : V)) ^⋏ (allFact ((termShift LAct)^[5] wy) (^&((0 : ℕ) : V))))) := by
  have hes : ∀ e ∈ ([wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_freeAll_as row_freeAll_body row_freeAll_inner
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_, ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))) hes, instOuterAt_exs 2 _ (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩))) hes, instOuterAt_exs 3 _ (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)) hes, instOuterAt_exs 4 _ (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩) hes, instOuterAt_and 5 _ (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩) hes, instOuterAt_and 5 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 5 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_Pfvar (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_PqVecG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_Pall (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩)))), freeIter_exs3 2 (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩⟩), freeIter_subst_listToVec' 2 _ isSemiformula_Pfvar shift_Pfvar (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Padjoin shift_Padjoin (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 (isSemiterm_qqZero_LAct 0) 2, iterate_termShift_qqZero 2]
    try rfl
  · rw [freeIterAt_and 3 2 (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩), freeIterAt_and 3 2 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩), freeIterAt_and 3 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)), freeIterAt_subst_listToVec 3 2 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries), freeIterAt_subst_listToVec 3 2 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIterAt_subst_listToVec 3 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIterAt_subst_listToVec 3 2 _ isSemiformula_Pall shift_Pall (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv_lt 3 2 0 (by norm_num), freeIterT_bv_lt 3 2 1 (by norm_num), freeIterT_bv_lt 3 2 2 (by norm_num), freeIterT_bv_ge 3 2 3 (by norm_num) (by norm_num), freeIterT_closed 3 hwp 2, freeIterT_closed 3 hwy 2]
    try simp only [Nat.reduceSub]
    rw [freeIter_and 3 (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩⟩), freeIter_and 3 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)⟩), freeIter_and 3 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 3 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries), freeIter_subst_listToVec' 3 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 3 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 3 _ isSemiformula_Pall shift_Pall (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 3 0 (by norm_num), freeIterT_bv0 3 1 (by norm_num), freeIterT_bv0 3 2 (by norm_num), freeIterT_closed 0 (t := ^&((0 : ℕ) : V)) (by simp) 3, freeIterT_closed 0 (isSemiterm_iterate_termShift hwp 2) 3, freeIterT_closed 0 (isSemiterm_iterate_termShift hwy 2) 3]
    try simp only [termShift_iterate_fvar, ← Function.iterate_add_apply, ← Nat.cast_add, Nat.reduceAdd]
    try rfl

/-! ### `freeExs` — `“y r p n. …”`, `m = 4` -/

noncomputable def row_freeExs_as : List V := [subst LAct (listToVec [bv 3 ^+ (𝟏 : V), bv 2]) Ppi, subst LAct (listToVec [bv 1, bv 2]) Pexs, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_freeExs_inner : V := subst LAct (listToVec [bv 2, bv 3]) PqVecG ^⋏ (subst LAct (listToVec [bv 1, bv 7]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG ^⋏ subst LAct (listToVec [bv 5, bv 0]) Pexs))
noncomputable def row_freeExs_body : V := subst LAct (listToVec [bv 1, (𝟎 : V)]) Pfvar ^⋏ (subst LAct (listToVec [bv 0, bv 1, (𝟎 : V)]) Padjoin ^⋏ (^∃ ^∃ ^∃ row_freeExs_inner))
noncomputable def row_freeExs_R : V := ^∃ row_freeExs_body
noncomputable def row_freeExs_c : V := ^∃ row_freeExs_R

theorem quote_row_freeExs : (⌜Semiformula.lMap emb freeExsB⌝ : V) = impChain LAct row_freeExs_as row_freeExs_c := by
  unfold freeExsB row_freeExs_as row_freeExs_c row_freeExs_R row_freeExs_body row_freeExs_inner Padjoin Pexs PfreeG Pfvar Ppi PqVecG PshiftG PsubstsG
  all_goals row_shape

lemma isSemiformula_freeExs_as : ∀ A ∈ row_freeExs_as, IsSemiformula LAct ((4 : ℕ) : V) A := by
  unfold row_freeExs_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Ppi _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries), List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entries), List.forall_mem_nil _⟩⟩⟩)
lemma isSemiformula_freeExs_c : IsSemiformula LAct ((4 : ℕ) : V) row_freeExs_c := by
  unfold row_freeExs_c row_freeExs_R row_freeExs_body row_freeExs_inner
  exact isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))⟩⟩))
lemma isSemiformula_freeExs_R : IsSemiformula LAct ((5 : ℕ) : V) row_freeExs_R := by
  unfold row_freeExs_R row_freeExs_body row_freeExs_inner
  exact isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))⟩⟩)
lemma isSemiformula_freeExs_body : IsSemiformula LAct ((6 : ℕ) : V) row_freeExs_body := by
  unfold row_freeExs_body row_freeExs_inner
  exact IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))⟩⟩
lemma row_freeExs_R_eq : (row_freeExs_R : V) = exsIter 1 row_freeExs_body := rfl

/-- `freeExs` at the witnesses `[wn, wp, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_freeExs {wn wp wr wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_freeExs_as.map (instOuter LAct [wn, wp, wr, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, freeFact wy wr] ∧
    freeIter LAct 2 (instOuterAt LAct 2 [wn, wp, wr, wy] row_freeExs_body) = fvarFact (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (adjFact (^&((0 : ℕ) : V)) (^&((1 : ℕ) : V)) (𝟎 : V) ^⋏ (^∃ ^∃ ^∃ (freeIterAt 3 2 (subst LAct (listToVec [bv 2, bv 3]) PqVecG ^⋏ (subst LAct (listToVec [bv 1, wp]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG ^⋏ subst LAct (listToVec [wy, bv 0]) Pexs)))))) ∧
    freeIter LAct 3 (freeIterAt 3 2 (subst LAct (listToVec [bv 2, bv 3]) PqVecG ^⋏ (subst LAct (listToVec [bv 1, wp]) PshiftG ^⋏ (subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG ^⋏ subst LAct (listToVec [wy, bv 0]) Pexs)))) = qVecFact (^&((2 : ℕ) : V)) (^&((3 : ℕ) : V)) ^⋏ (shiftFact (^&((1 : ℕ) : V)) ((termShift LAct)^[5] wp) ^⋏ (substFact (^&((0 : ℕ) : V)) (^&((2 : ℕ) : V)) (^&((1 : ℕ) : V)) ^⋏ (exsFact ((termShift LAct)^[5] wy) (^&((0 : ℕ) : V))))) := by
  have hes : ∀ e ∈ ([wn, wp, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_freeExs_as row_freeExs_body row_freeExs_inner
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries)]
  refine ⟨by ((try row_entries_simp); row_finish), ?_, ?_⟩
  · rw [instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))⟩) hes, instOuterAt_and 2 _ (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))) hes, instOuterAt_exs 2 _ (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩))) hes, instOuterAt_exs 3 _ (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)) hes, instOuterAt_exs 4 _ (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩) hes, instOuterAt_and 5 _ (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩) hes, instOuterAt_and 5 _ (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩) hes, instOuterAt_and 5 _ (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)) hes, instOuterAt_subst_listToVec 2 _ isSemiformula_Pfvar (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 2 _ isSemiformula_Padjoin (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_PqVecG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_PshiftG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entries), instOuterAt_subst_listToVec 5 _ isSemiformula_Pexs (by rfl) _ hes (by row_entries)]
    row_entries_simp
    rw [freeIter_and 2 (isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries), isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))⟩), freeIter_and 2 (isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entries)) (isSemiformula_exs_cast (isSemiformula_exs_cast (isSemiformula_exs_cast (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩)))), freeIter_exs3 2 (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩⟩), freeIter_subst_listToVec' 2 _ isSemiformula_Pfvar shift_Pfvar (by rfl) (by row_entries), freeIter_subst_listToVec' 2 _ isSemiformula_Padjoin shift_Padjoin (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 2 0 (by norm_num), freeIterT_bv0 2 1 (by norm_num), freeIterT_closed 0 (isSemiterm_qqZero_LAct 0) 2, iterate_termShift_qqZero 2]
    try rfl
  · rw [freeIterAt_and 3 2 (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩), freeIterAt_and 3 2 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩), freeIterAt_and 3 2 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)), freeIterAt_subst_listToVec 3 2 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries), freeIterAt_subst_listToVec 3 2 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIterAt_subst_listToVec 3 2 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIterAt_subst_listToVec 3 2 _ isSemiformula_Pexs shift_Pexs (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv_lt 3 2 0 (by norm_num), freeIterT_bv_lt 3 2 1 (by norm_num), freeIterT_bv_lt 3 2 2 (by norm_num), freeIterT_bv_ge 3 2 3 (by norm_num) (by norm_num), freeIterT_closed 3 hwp 2, freeIterT_closed 3 hwy 2]
    try simp only [Nat.reduceSub]
    rw [freeIter_and 3 (isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries), IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩⟩), freeIter_and 3 (isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entries)) (IsSemiformula.and.mpr ⟨isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries), isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)⟩), freeIter_and 3 (isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entries)) (isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entries)), freeIter_subst_listToVec' 3 _ isSemiformula_PqVecG shift_PqVecG (by rfl) (by row_entries), freeIter_subst_listToVec' 3 _ isSemiformula_PshiftG shift_PshiftG (by rfl) (by row_entries), freeIter_subst_listToVec' 3 _ isSemiformula_PsubstsG shift_PsubstsG (by rfl) (by row_entries), freeIter_subst_listToVec' 3 _ isSemiformula_Pexs shift_Pexs (by rfl) (by row_entries)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 3 0 (by norm_num), freeIterT_bv0 3 1 (by norm_num), freeIterT_bv0 3 2 (by norm_num), freeIterT_closed 0 (t := ^&((0 : ℕ) : V)) (by simp) 3, freeIterT_closed 0 (isSemiterm_iterate_termShift hwp 2) 3, freeIterT_closed 0 (isSemiterm_iterate_termShift hwy 2) 3]
    try simp only [termShift_iterate_fvar, ← Function.iterate_add_apply, ← Nat.cast_add, Nat.reduceAdd]
    try rfl

end rows

end ArithS
