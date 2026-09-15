import ArithS.Necessitation.Top

/-!
# ArithS.Necessitation.NumId — numeral identification: `eqFact &x (numeral ⌜φ⌝)` from a dossier

`DESIGN_fragments.md` §4.10 (i) / §7.1 step 3 (`pinSteps`): the object proof knows a code only
through the EIGENVARIABLES of its walk dossier (`Cert.DossF`), but the target sentence of the top
(`Top.lean`: `instB ⌜Box_g χ⌝ k = boxFact (qNum χ) (bnum k)`, `qNum χ = numeral ⌜χ⌝`) names the
UNARY NUMERAL of the closed code. This file derives, for a STANDARD code — the quote `⌜φ⌝` of a
meta-level (Lean) formula `φ` — the object fact `eqFact (^&i) (numeral ⌜φ⌝)` from the dossier of
`⌜φ⌝` at `&i`, bottom-up over the dossier.

## The route (chosen; the alternatives and why not)

Per node ONE closed shape fact and ONE identification row:

* the closed shape fact of the node's numerals, e.g. `andFact (numeral ⌜φ ⋏ ψ⌝) (numeral ⌜φ⌝)
  (numeral ⌜ψ⌝)`, enters as an `sLemma` (tag 7) whose derivation is a `Lib` constant: the fact is
  the META sentence `qqAndDef ⇜ ![↑⌜φ⋏ψ⌝, ↑⌜φ⌝, ↑⌜ψ⌝]` (§0 `cfact`), TRUE in `ℕ` by the quote
  equations (`⌜φ ⋏ ψ⌝ = ⌜φ⌝ ^⋏ ⌜ψ⌝`, `rfl`), hence true in every model by `𝚺₀`-absoluteness
  (Foundation's `shigmaZero_absolute`), hence a library sentence (`Lib.of_models`: completeness gives
  a `𝗣𝗔`-proof, transported to `TAct` with a STANDARD length `N`). Its code is the fact code at the
  numerals (`quote_lMap_emb_subst` + `empty_typed_quote_numeral_eq_numeral`) — no closed quote of a
  big sentence is ever unfolded: every identity is stated for the VARIABLE code `x` first (§1) and
  instantiated at `((⌜φ⌝ : ℕ) : V)` at the end (§2).
* the identification row `eqOf<Kind>` of `Layout` (`eqOfAnd : !qqAndDef x p q → !qqAndDef y p' q' →
  p = p' → q = q' → x = y`, …, `eqOfAdj`; `eqRefl` for the empty vector), instantiated at the
  eigenvariables and the numerals — witnesses are closed terms, so the list is SHIFT-FREE
  (`shiftsV = 0`): offsets never move.

NOT taken: a `Σ₁` producer of the closed facts' derivations for a VARIABLE code `c` (the brief's
`numIdSteps W c i`). It would need, uniformly in `c`, derivation CODES of closed `𝚫₀` facts about
unary numerals (`qqAnd (numeral p) (numeral q) = numeral c` through the pairing's arithmetic —
`NumSteps`/`NumMul`-style provers for unary numerals and the quadratic pairing, thousands of lines),
or Foundation's internal `𝚺₁`-completeness (`bold_sigma_one_complete`, over `𝗣𝗔` in `ℒₒᵣ`) bridged
to `TAct`-derivations plus an absoluteness argument for the resulting constant. Both far exceed the
budget, and NEITHER consumer needs the uniformity: `PinKit χ` is per `χ` (`∃ P`, no `Σ₁` function
required) and `axm`(i) is per STANDARD axiom `σ` — both are quotes of Lean-level sentences, exactly
what `numId_formula` takes. The constants are per-`φ` naturals (`BoundedInnerNec` allows `∃ C` per
`χ`), obtained by `Lib` and by the `𝚺₁`-absoluteness of `formulaLen` (`formulaLen LAct ⌜φ⌝` is the
cast of its `ℕ`-value, `flN`).

## Contents

* §0 closed facts: `cfact P ts := P ⇜ ts`, its truth (`models_cfact`) and code (`quote_cfact`,
  `semitermVec_val_quote`); numerals (`quote_natT`, `natT_val`) and chain terms (`cTT_val`);
  `lib_cfact_of_nat` (truth in `ℕ` ⇒ `Lib`) and `ClosedDer` — a closed fact with a standard-length
  derivation in every model (`closedDer_of_lib`); `flN`, the `ℕ`-value of `formulaLen` (`flN_cast`).
* §1 the node steps for VARIABLE codes with an ORACLE derivation of the closed fact: the two-step
  lists `sLemma A dA ∷ ?[eqOf<Kind> at the witnesses]` (`lemmaThenHorn_ok`), one lemma per kind.
* §2 the meta induction: `numId_term` (`SyntacticSemiterm`), the vector invariant over `takeLast`,
  `numId_formula` (`Semiproposition`), and the sentence form `numId_sentence` (`Semisentence LAct n`):
  `∃ C : ℕ, ∀ V, DossF walkPieces Γ n ⌜φ⌝ i → C + i ≤ E → ∃ P, ListOK tbl E 9 Γ P ∧ NoDrop' P ∧
  shiftsV P = 0 ∧ len P ≤ C ∧ SizeOK C C P ∧ neg (eqFact (^&i) (numeral ⌜φ⌝)) ∈ finalCtx Γ P`, with
  `costSum_numId_le` (`Frag1.costSum_le_of_sizeOK`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 0. Closed facts at standard numerals -/

section closedFacts

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A closed instance of an `ℒₒᵣ`-semisentence at closed terms: `P ⇜ ts`. -/
noncomputable def cfact {k : ℕ} (P : ArithmeticSemisentence k) (ts : Fin k → ClosedSemiterm ℒₒᵣ 0) :
    ArithmeticSentence := P ⇜ ts

lemma models_cfact {k : ℕ} (P : ArithmeticSemisentence k) (ts : Fin k → ClosedSemiterm ℒₒᵣ 0) :
    V↓[ℒₒᵣ] ⊧ cfact P ts ↔ V ⊧/(fun i ↦ Semiterm.valb ![] (ts i)) P := by
  simp [cfact, models_iff]
  rfl

/-- The `LAct`-code of the closed term `lMap emb t` read through the typed quote is the code of `t`. -/
lemma val_quote_emb_lMap (t : ClosedSemiterm ℒₒᵣ 0) :
    ((⌜(↑(Semiterm.lMap emb t) : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm V LAct 0)).val = (⌜t⌝ : V) := by
  rw [Diag.typed_val_emb, Semiterm.empty_quote_def, Diag.term_emb_lMap_emb, quote_term_lMap_emb,
    ← Semiterm.empty_quote_def]

lemma semitermVec_val_quote {k : ℕ} (ts : Fin k → ClosedSemiterm ℒₒᵣ 0) :
    SemitermVec.val (fun i ↦ (⌜(↑(Semiterm.lMap emb (ts i)) : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm V LAct 0)) =
      matrixToVec (fun i ↦ (⌜ts i⌝ : V)) := by
  unfold SemitermVec.val
  exact matrixToVec_congr (fun i ↦ val_quote_emb_lMap _)

/-- **The code of a closed fact**: the predicate's code at the codes of the terms. -/
lemma quote_cfact {k : ℕ} (P : ArithmeticSemisentence k) (ts : Fin k → ClosedSemiterm ℒₒᵣ 0) :
    (⌜Semiformula.lMap emb (cfact P ts)⌝ : V) =
      subst LAct (matrixToVec (fun i ↦ (⌜ts i⌝ : V))) ⌜Semiformula.lMap emb P⌝ := by
  rw [cfact, quote_lMap_emb_subst, semitermVec_val_quote]

/-- The numeral term `↑n : ClosedSemiterm ℒₒᵣ 0` has the code `numeral n`. -/
lemma quote_natT (n : ℕ) : (⌜(↑n : ClosedSemiterm ℒₒᵣ 0)⌝ : V) = numeral (n : V) := by
  change ((⌜(↑n : ClosedSemiterm ℒₒᵣ 0)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 0)).val = _
  rw [Semiterm.empty_typed_quote_numeral_eq_numeral]
  rfl

lemma natT_val (n : ℕ) : Semiterm.valb ![] (↑n : ClosedSemiterm ℒₒᵣ 0) = (n : V) := by
  simp [numeral_eq_natCast]

lemma cTT_val (n : ℕ) : Semiterm.valb ![] (cTT n) = (n : V) := by
  induction n with
  | zero => simp [cTT_zero]
  | succ n ih => simp [cTT_succ, ih]

/-- **Truth in `ℕ` gives a library sentence**: a `𝚺₀` predicate true in `ℕ` at the values `w` of the
closed terms `ts` is true in every model at the casts (`shigmaZero_absolute`), hence `Lib`. -/
theorem lib_cfact_of_nat {k : ℕ} (P : 𝚺₀.Semisentence k) (ts : Fin k → ClosedSemiterm ℒₒᵣ 0) (w : Fin k → ℕ)
    (hv : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], ∀ i, Semiterm.valb (M := V) ![] (ts i) = (w i : V))
    (h : ℕ ⊧/w P.val) : Lib (cfact P.val ts) :=
  Lib.of_models fun V _ _ ↦ (models_cfact _ _).mpr (by
    rw [show (fun i ↦ Semiterm.valb (M := V) ![] (ts i)) = (Nat.cast : ℕ → V) ∘ w from funext (hv V)]
    exact (Arithmetic.shigmaZero_absolute V P w).mp h)

/-- **A closed fact with a standard-length derivation in every model** — what `Lib.code` delivers,
in the `sing`/`DerivationOf` form the `sLemma` step consumes (`lemmaOK_of`). -/
def ClosedDer (A : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V) : Prop :=
  ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ d : V, DerivationOf TAct d (sing (A V)) ∧ dlen TAct d ≤ (N : V)

lemma proof_sing {d A : V} (h : Proof TAct d A) : DerivationOf TAct d (sing A) := by
  unfold Proof at h
  rwa [singleton_eq_insert, emptyset_def] at h

theorem closedDer_of_lib {σ : ArithmeticSentence} (h : Lib σ) :
    ClosedDer (fun V _ _ ↦ (⌜Semiformula.lMap emb σ⌝ : V)) := by
  obtain ⟨N, hN⟩ := h.code
  exact ⟨N, fun V _ _ ↦ by obtain ⟨d, hd, hl⟩ := hN V; exact ⟨d, proof_sing hd, hl⟩⟩

/-- The `ℕ`-value of `formulaLen LAct` at a standard code. -/
noncomputable def flN (p : ℕ) : ℕ := formulaLen LAct p

/-- **`formulaLen` is absolute** (`𝚺₁`-definable by the fixed blueprint `formulaLenGraph`): at a
standard code its value is the cast of the `ℕ`-value. -/
lemma flN_cast (p : ℕ) : formulaLen LAct (p : V) = (flN p : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (formulaLen.defined (V := ℕ) (L := LAct))
    (formulaLen.defined (V := V) (L := LAct)) ![p]
  simpa [flN, Function.comp_def] using this.symm

/-! ### The per-kind closed shape facts (`Lib` + code), for STANDARD codes -/

/-- `⋏`: `!qqAndDef x p q` at the numerals. -/
noncomputable def cfAnd (x p q : ℕ) : ArithmeticSentence := cfact qqAndDef.val ![↑x, ↑p, ↑q]
lemma lib_cfAnd {x p q : ℕ} (h : x = qqAnd p q) : Lib (cfAnd x p q) :=
  lib_cfact_of_nat qqAndDef _ ![x, p, q] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfAnd (x p q : ℕ) :
    (⌜Semiformula.lMap emb (cfAnd x p q)⌝ : V) = andFact (numeral (x : V)) (numeral (p : V)) (numeral (q : V)) := by
  rw [cfAnd, quote_cfact, matrixToVec_fin3]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑p : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑q : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_natT, quote_natT]
  rfl

/-- `⋎`. -/
noncomputable def cfOr (x p q : ℕ) : ArithmeticSentence := cfact qqOrDef.val ![↑x, ↑p, ↑q]
lemma lib_cfOr {x p q : ℕ} (h : x = qqOr p q) : Lib (cfOr x p q) :=
  lib_cfact_of_nat qqOrDef _ ![x, p, q] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfOr (x p q : ℕ) :
    (⌜Semiformula.lMap emb (cfOr x p q)⌝ : V) = orFact (numeral (x : V)) (numeral (p : V)) (numeral (q : V)) := by
  rw [cfOr, quote_cfact, matrixToVec_fin3]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑p : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑q : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_natT, quote_natT]
  rfl

/-- `∀`. -/
noncomputable def cfAll (x p : ℕ) : ArithmeticSentence := cfact qqAllDef.val ![↑x, ↑p]
lemma lib_cfAll {x p : ℕ} (h : x = qqAll p) : Lib (cfAll x p) :=
  lib_cfact_of_nat qqAllDef _ ![x, p] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfAll (x p : ℕ) :
    (⌜Semiformula.lMap emb (cfAll x p)⌝ : V) = allFact (numeral (x : V)) (numeral (p : V)) := by
  rw [cfAll, quote_cfact, matrixToVec_fin2]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑p : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_natT]
  rfl

/-- `∃`. -/
noncomputable def cfExs (x p : ℕ) : ArithmeticSentence := cfact qqExsDef.val ![↑x, ↑p]
lemma lib_cfExs {x p : ℕ} (h : x = qqExs p) : Lib (cfExs x p) :=
  lib_cfact_of_nat qqExsDef _ ![x, p] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfExs (x p : ℕ) :
    (⌜Semiformula.lMap emb (cfExs x p)⌝ : V) = exsFact (numeral (x : V)) (numeral (p : V)) := by
  rw [cfExs, quote_cfact, matrixToVec_fin2]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑p : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_natT]
  rfl

/-- `⊤`. -/
noncomputable def cfVerum (x : ℕ) : ArithmeticSentence := cfact qqVerumDef.val ![↑x]
lemma lib_cfVerum {x : ℕ} (h : x = qqVerum) : Lib (cfVerum x) :=
  lib_cfact_of_nat qqVerumDef _ ![x] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfVerum (x : ℕ) :
    (⌜Semiformula.lMap emb (cfVerum x)⌝ : V) = verumFact (numeral (x : V)) := by
  rw [cfVerum, quote_cfact, matrixToVec_fin1]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT]
  rfl

/-- `⊥`. -/
noncomputable def cfFalsum (x : ℕ) : ArithmeticSentence := cfact qqFalsumDef.val ![↑x]
lemma lib_cfFalsum {x : ℕ} (h : x = qqFalsum) : Lib (cfFalsum x) :=
  lib_cfact_of_nat qqFalsumDef _ ![x] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfFalsum (x : ℕ) :
    (⌜Semiformula.lMap emb (cfFalsum x)⌝ : V) = falsumFact (numeral (x : V)) := by
  rw [cfFalsum, quote_cfact, matrixToVec_fin1]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT]
  rfl

/-- `rel` — the arity and the symbol as CHAIN terms (`cTT`), as the walk writes them. -/
noncomputable def cfRel (x k R v : ℕ) : ArithmeticSentence := cfact qqRelDef.val ![↑x, cTT k, cTT R, ↑v]
lemma lib_cfRel {x k R v : ℕ} (h : x = qqRel k R v) : Lib (cfRel x k R v) :=
  lib_cfact_of_nat qqRelDef _ ![x, k, R, v] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, cTT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfRel (x k R v : ℕ) :
    (⌜Semiformula.lMap emb (cfRel x k R v)⌝ : V) = relFact (numeral (x : V)) (cT k) (cT R) (numeral (v : V)) := by
  rw [cfRel, quote_cfact, matrixToVec_fin4]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT k : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT R : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑v : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_cTT, quote_cTT, quote_natT]
  rfl

/-- `nrel`. -/
noncomputable def cfNRel (x k R v : ℕ) : ArithmeticSentence := cfact qqNRelDef.val ![↑x, cTT k, cTT R, ↑v]
lemma lib_cfNRel {x k R v : ℕ} (h : x = qqNRel k R v) : Lib (cfNRel x k R v) :=
  lib_cfact_of_nat qqNRelDef _ ![x, k, R, v] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, cTT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfNRel (x k R v : ℕ) :
    (⌜Semiformula.lMap emb (cfNRel x k R v)⌝ : V) = nrelFact (numeral (x : V)) (cT k) (cT R) (numeral (v : V)) := by
  rw [cfNRel, quote_cfact, matrixToVec_fin4]
  change subst LAct (listToVec [(⌜(↑x : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT k : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT R : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑v : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_cTT, quote_cTT, quote_natT]
  rfl

/-- `func`. -/
noncomputable def cfFunc (t k f v : ℕ) : ArithmeticSentence := cfact qqFuncDef.val ![↑t, cTT k, cTT f, ↑v]
lemma lib_cfFunc {t k f v : ℕ} (h : t = qqFunc k f v) : Lib (cfFunc t k f v) :=
  lib_cfact_of_nat qqFuncDef _ ![t, k, f, v] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, cTT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfFunc (t k f v : ℕ) :
    (⌜Semiformula.lMap emb (cfFunc t k f v)⌝ : V) = funcFact (numeral (t : V)) (cT k) (cT f) (numeral (v : V)) := by
  rw [cfFunc, quote_cfact, matrixToVec_fin4]
  change subst LAct (listToVec [(⌜(↑t : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT k : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT f : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑v : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_cTT, quote_cTT, quote_natT]
  rfl

/-- `#z`. -/
noncomputable def cfBvar (t z : ℕ) : ArithmeticSentence := cfact qqBvarDef.val ![↑t, cTT z]
lemma lib_cfBvar {t z : ℕ} (h : t = qqBvar z) : Lib (cfBvar t z) :=
  lib_cfact_of_nat qqBvarDef _ ![t, z] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, cTT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfBvar (t z : ℕ) :
    (⌜Semiformula.lMap emb (cfBvar t z)⌝ : V) = bvarFact (numeral (t : V)) (cT z) := by
  rw [cfBvar, quote_cfact, matrixToVec_fin2]
  change subst LAct (listToVec [(⌜(↑t : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT z : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_cTT]
  rfl

/-- `&x`. -/
noncomputable def cfFvar (t z : ℕ) : ArithmeticSentence := cfact qqFvarDef.val ![↑t, cTT z]
lemma lib_cfFvar {t z : ℕ} (h : t = qqFvar z) : Lib (cfFvar t z) :=
  lib_cfact_of_nat qqFvarDef _ ![t, z] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, cTT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfFvar (t z : ℕ) :
    (⌜Semiformula.lMap emb (cfFvar t z)⌝ : V) = fvarFact (numeral (t : V)) (cT z) := by
  rw [cfFvar, quote_cfact, matrixToVec_fin2]
  change subst LAct (listToVec [(⌜(↑t : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(cTT z : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_cTT]
  rfl

/-- `adjoin`: `w = t ∷ v`. -/
noncomputable def cfAdj (w t v : ℕ) : ArithmeticSentence := cfact adjoinDef.val ![↑w, ↑t, ↑v]
lemma lib_cfAdj {w t v : ℕ} (h : w = t ∷ v) : Lib (cfAdj w t v) :=
  lib_cfact_of_nat adjoinDef _ ![w, t, v] (fun V _ _ i ↦ by fin_cases i <;> simp [natT_val, numeral_eq_natCast]) (by simp [h])
lemma code_cfAdj (w t v : ℕ) :
    (⌜Semiformula.lMap emb (cfAdj w t v)⌝ : V) = adjFact (numeral (w : V)) (numeral (t : V)) (numeral (v : V)) := by
  rw [cfAdj, quote_cfact, matrixToVec_fin3]
  change subst LAct (listToVec [(⌜(↑w : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑t : ClosedSemiterm ℒₒᵣ 0)⌝ : V), (⌜(↑v : ClosedSemiterm ℒₒᵣ 0)⌝ : V)]) _ = _
  rw [quote_natT, quote_natT, quote_natT]
  rfl

end closedFacts

/-! ## 1. The node steps: a lemma cut followed by one Horn step, shift-free -/

section nodeSteps

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **A closed lemma then one Horn step.** `A` is a closed fact with a derivation `dA` (length `≤ D`,
size `≤ Q`); `s` is a tag-0 step applicable once `neg A` is in the context, adding `neg F`. The two-step
list is applicable at cap `9`, cut-admitting, shift-free, of length `2`, `SizeOK Q D`, and leaves `neg F`. -/
theorem lemmaThenHorn_ok {tbl N E Γ A dA s F Q D : V} (htbl : TableOK tbl N) (hΓ : IsFormulaSet LAct Γ)
    (hA : IsFormula LAct A) (hd : DerivationOf TAct dA (sing A)) (hQ : formulaLen LAct A ≤ Q) (hD : dlen TAct dA ≤ D)
    (hs : IsFormulaSet LAct (insert (neg LAct A) Γ) →
      StepOK tbl E ((9 : ℕ) : V) (insert (neg LAct A) Γ) s ∧ sTag s = 0 ∧
      ctxAfter (insert (neg LAct A) Γ) s = insert (neg LAct F) (insert (neg LAct A) Γ)) :
    ListOK tbl E ((9 : ℕ) : V) Γ ?[sLemma A dA, s] ∧ NoDrop' (?[sLemma A dA, s] : V) ∧
    shiftsV (?[sLemma A dA, s] : V) = 0 ∧ len (?[sLemma A dA, s] : V) = 2 ∧ SizeOK Q D (?[sLemma A dA, s] : V) ∧
    neg LAct F ∈ finalCtx Γ ?[sLemma A dA, s] := by
  have h1 : StepOK tbl E ((9 : ℕ) : V) Γ (sLemma A dA) := stepOK_sLemma hΓ (lemmaOK_of hA hd)
  have hΓ' : IsFormulaSet LAct (insert (neg LAct A) Γ) := by
    have := isFormulaSet_ctxAfter 9 htbl h1
    rwa [ctxAfter_sLemma] at this
  obtain ⟨h2, htag, hctx⟩ := hs hΓ'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine listOK_cons h1 ?_
    rw [ctxAfter_sLemma]
    exact listOK_single h2
  · exact noDrop'_cons (by simp) (noDrop'_single (Or.inl htag))
  · rw [shiftsV_cons_sLemma, shiftsV_single_tag0 htag]
  · simp [one_add_one_eq_two]
  · refine sizeOK_cons ?_ (sizeOK_single (Or.inl htag))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, by simpa using hQ, by simpa using hD⟩)))))
  · rw [finalCtx_cons, finalCtx_single, ctxAfter_sLemma, hctx]
    exact mem_insert_self'

end nodeSteps

/-! ## 2. The meta induction -/

section metaInduction

/-! ### 2.1 The invariants, and the absoluteness helpers -/

/-- The `ℕ`-value of `termLen LAct` at a standard code. -/
noncomputable def tlN (t : ℕ) : ℕ := termLen LAct t

/-- The quote vector of a meta vector of terms, in a model `V`. -/
noncomputable def vv (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) : V :=
  SemitermVec.val (fun m ↦ (⌜v m⌝ : Bootstrapping.Semiterm V LAct n))

/-- **The invariant of a numeral-identification list** `P` at `Γ` with the constant `C`: applicable at
cap `9`, cut-admitting, SHIFT-FREE, of length `≤ C`, `SizeOK C C`, leaving `neg F` in its final context. -/
def NumInv {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tbl E Γ : V) (C : ℕ) (P F : V) : Prop :=
  ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ shiftsV P = 0 ∧ len P ≤ (C : V) ∧
    SizeOK (C : V) (C : V) P ∧ neg LAct F ∈ finalCtx Γ P

/-- **The term invariant** for a meta term `t`: for some standard `C`, in every model, from the dossier of
`⌜t⌝` at `&i` a list `NumInv … C` (under `C + i ≤ E`) leaving `eqFact (^&i) (numeral ⌜t⌝)`. -/
def TermId {n : ℕ} (t : SyntacticSemiterm LAct n) : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i : V},
    TableOK tbl N → LayoutTable tbl → IsFormulaSet LAct Γ →
    DossT walkPieces Γ n (⌜t⌝ : V) i → (C : V) + i ≤ E →
    ∃ P : V, NumInv tbl E Γ C P (eqFact (^&i) (numeral (⌜t⌝ : V)))

/-- **The vector invariant** for the last `j` entries of a meta vector `v`: the walked suffix
`takeLast (vv v) j` is identified at its reference `vRef i j`. -/
def VecId {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) (j : ℕ) : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i : V},
    TableOK tbl N → LayoutTable tbl → IsFormulaSet LAct Γ →
    DossV walkPieces Γ n k (vv V v) j i → (C : V) + i ≤ E →
    ∃ P : V, NumInv tbl E Γ C P (eqFact (vRef i j) (numeral (takeLast (vv V v) j)))

/-- **The formula invariant** for a meta formula `φ`. -/
def FormId {n : ℕ} (φ : Semiproposition LAct n) : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i : V},
    TableOK tbl N → LayoutTable tbl → IsFormulaSet LAct Γ →
    DossF walkPieces Γ n (⌜φ⌝ : V) i → (C : V) + i ≤ E →
    ∃ P : V, NumInv tbl E Γ C P (eqFact (^&i) (numeral (⌜φ⌝ : V)))

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma tlN_cast (t : ℕ) : termLen LAct (t : V) = (tlN t : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (termLen.defined (V := ℕ) (L := LAct))
    (termLen.defined (V := V) (L := LAct)) ![t]
  simpa [tlN, Function.comp_def] using this.symm

lemma takeLast_cast (a b : ℕ) : ((takeLast a b : ℕ) : V) = takeLast (a : V) (b : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (takeLast_defined (V := ℕ)) (takeLast_defined (V := V)) ![a, b]
  simpa [Function.comp_def] using this

lemma vv_cast {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) : ((vv ℕ v : ℕ) : V) = vv V v := by
  unfold vv
  rw [Semiterm.quote_eq_encode', Semiterm.quote_eq_encode']
  simp

lemma isSemitermVec_vv {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) : IsSemitermVec LAct (k : V) (n : V) (vv V v) :=
  SemitermVec.isSemitermVec _

lemma len_vv {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) : len (vv V v) = k :=
  SemitermVec.len_eq _

lemma nth_vv {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) (m : Fin k) : (vv V v).[((m : ℕ) : V)] = ⌜v m⌝ :=
  SemitermVec.val_nth_eq _ m

lemma isSemiterm_numeral_LAct (x : V) : IsSemiterm LAct 0 (numeral x) :=
  InstV.isSemiterm_LAct_of_LOR (numeral_semiterm 0 _)

lemma termLen_numeral_le' {x E : V} (h : 2 * x + 1 ≤ E) : termLen LAct (numeral x) ≤ E :=
  le_trans (termLen_numeral_le x) h

/-- The `E`-cap arithmetic: `(a : ℕ) + i ≤ E` from `(b : ℕ) + i ≤ E` and `a ≤ b`. -/
lemma cap_mono {a b : ℕ} {i E : V} (hab : a ≤ b) (h : (b : V) + i ≤ E) : (a : V) + i ≤ E :=
  le_trans (add_le_add ((Nat.cast_le (α := V)).mpr hab) (le_refl i)) h

lemma cap_le {a b : ℕ} {i E : V} (hab : a ≤ b) (h : (b : V) + i ≤ E) : (a : V) ≤ E :=
  le_trans (le_trans ((Nat.cast_le (α := V)).mpr hab) le_self_add) h

lemma cap_fvar {a b : ℕ} {i E : V} (hab : a + 1 ≤ b) (h : (b : V) + i ≤ E) : i + 1 ≤ E := by
  calc i + 1 = ((1 : ℕ) : V) + i := by push_cast; ring
    _ ≤ (b : V) + i := add_le_add ((Nat.cast_le (α := V)).mpr (by omega : 1 ≤ b)) (le_refl i)
    _ ≤ E := h

/-- Repackaging a two-step result under the invariant's single constant. -/
lemma pack2 {tbl E Γ S F Q D : V} {C : ℕ}
    (h : ListOK tbl E ((9 : ℕ) : V) Γ S ∧ NoDrop' S ∧ shiftsV S = 0 ∧ len S = 2 ∧ SizeOK Q D S ∧ neg LAct F ∈ finalCtx Γ S)
    (hQ : Q ≤ (C : V)) (hD : D ≤ (C : V)) (h2 : 2 ≤ C) : NumInv tbl E Γ C S F := by
  obtain ⟨h1, h2', h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2', h3, ?_, h5.mono hQ hD, h6⟩
  rw [h4]; exact_mod_cast h2

/-- The `E`-cap for a sub-list at an offset moved by an eigenvariable count `c + 1 ≤ 2d`. -/
lemma cap_shift {a b d : ℕ} {c i E : V} (hc : c + 1 ≤ 2 * (d : V)) (hab : a + 2 * d ≤ b) (h : (b : V) + i ≤ E) :
    (a : V) + (i + 1 + c) ≤ E := by
  calc (a : V) + (i + 1 + c) = (a : V) + (c + 1) + i := by ring
    _ ≤ (a : V) + 2 * (d : V) + i := add_le_add (add_le_add (le_refl _) hc) (le_refl i)
    _ = ((a + 2 * d : ℕ) : V) + i := by push_cast; ring
    _ ≤ (b : V) + i := add_le_add ((Nat.cast_le (α := V)).mpr hab) (le_refl i)
    _ ≤ E := h

lemma NumInv.mono {tbl E Γ P F : V} {C C' : ℕ} (hC : C ≤ C') (h : NumInv tbl E Γ C P F) : NumInv tbl E Γ C' P F := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc : (C : V) ≤ (C' : V) := by exact_mod_cast hC
  exact ⟨h1, h2, h3, le_trans h4 hc, h5.mono hc hc, h6⟩

lemma NumInv.isFormulaSet {tbl N E Γ P F : V} {C : ℕ} (htbl : TableOK tbl N) (hΓ : IsFormulaSet LAct Γ)
    (h : NumInv tbl E Γ C P F) : IsFormulaSet LAct (finalCtx Γ P) :=
  finalCtx_isFormulaSet 9 htbl hΓ h.1

/-- A fact survives a shift-free cut-admitting list unchanged. -/
lemma mem_final0 {Γ S x : V} (hS : NoDrop' S) (h0 : shiftsV S = 0) (hx : x ∈ Γ) : x ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS hx
  rwa [h0, shiftIterV_zero] at this

lemma NumInv.mem {tbl E Γ P F x : V} {C : ℕ} (h : NumInv tbl E Γ C P F) (hx : x ∈ Γ) : x ∈ finalCtx Γ P :=
  mem_final0 h.2.1 h.2.2.1 hx

lemma NumInv.dossT {tbl E Γ P F W n t i : V} {C : ℕ} (h : NumInv tbl E Γ C P F) (hD : DossT W Γ n t i) :
    DossT W (finalCtx Γ P) n t i := by
  have := dossT_transport' h.2.1 hD
  rwa [h.2.2.1, add_zero] at this

lemma NumInv.dossV {tbl E Γ P F W n k v j i : V} {C : ℕ} (h : NumInv tbl E Γ C P F) (hD : DossV W Γ n k v j i) :
    DossV W (finalCtx Γ P) n k v j i := by
  have := dossV_transport' h.2.1 hD
  rwa [h.2.2.1, add_zero] at this

lemma NumInv.dossF {tbl E Γ P F W n r i : V} {C : ℕ} (h : NumInv tbl E Γ C P F) (hD : DossF W Γ n r i) :
    DossF W (finalCtx Γ P) n r i := by
  have := dossF_transport' h.2.1 hD
  rwa [h.2.2.1, add_zero] at this

/-- **Appending two invariant lists** (the second at the first's final context). -/
lemma NumInv.append {tbl E Γ P₁ P₂ F₁ F₂ : V} {C₁ C₂ C : ℕ} (h₁ : NumInv tbl E Γ C₁ P₁ F₁)
    (h₂ : NumInv tbl E (finalCtx Γ P₁) C₂ P₂ F₂) (hC : C₁ + C₂ ≤ C) : NumInv tbl E Γ C (appendV P₁ P₂) F₂ := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h₂
  have hc1 : (C₁ : V) ≤ (C : V) := by exact_mod_cast (by omega : C₁ ≤ C)
  have hc2 : (C₂ : V) ≤ (C : V) := by exact_mod_cast (by omega : C₂ ≤ C)
  refine ⟨listOK_appendV a1 b1, noDrop'_appendV a2 b2, by rw [shiftsV_appendV, a3, b3, add_zero], ?_,
    sizeOK_appendV (a5.mono hc1 hc1) (b5.mono hc2 hc2), by rw [finalCtx_appendV]; exact b6⟩
  rw [len_appendV]
  calc len P₁ + len P₂ ≤ (C₁ : V) + (C₂ : V) := add_le_add a4 b4
    _ = ((C₁ + C₂ : ℕ) : V) := by push_cast; ring
    _ ≤ (C : V) := by exact_mod_cast hC

lemma isSemiterm_quote {n : ℕ} (t : SyntacticSemiterm LAct n) : IsSemiterm LAct (n : V) (⌜t⌝ : V) :=
  (⌜t⌝ : Bootstrapping.Semiterm V LAct n).isSemiterm

/-- The walked suffix grows by the entry `v.[a]`, `a + (j + 1) = k` (stated generically so that its `ℕ`
instance carries the model's own `Sub` instance — `Nat.sub` and Foundation's `Sub ℕ` are NOT
syntactically the same). -/
lemma takeLast_vv_succ {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) (j a : ℕ) (ha : a + (j + 1) = k) :
    takeLast (vv V v) ((j : V) + 1) = ⌜v ⟨a, by omega⟩⌝ ∷ takeLast (vv V v) (j : V) := by
  have hjk : (j : V) < len (vv V v) := by rw [len_vv]; exact_mod_cast (by omega : j < k)
  rw [takeLast_succ_of_lt hjk, len_vv]
  have hidx : ((k : V) - ((j : V) + 1)) = (a : V) := by
    have hk : (k : V) = (a : V) + ((j : V) + 1) := by rw [← ha]; push_cast; ring
    rw [hk, add_tsub_cancel_right]
  have hnth : (vv V v).[(a : V)] = ⌜v ⟨a, by omega⟩⌝ := nth_vv v ⟨a, by omega⟩
  rw [hidx, hnth]

/-- The code of a predicate is the cast of its `ℕ`-code (a `Semisentence` quote). -/
lemma quote_semisentence_cast {L : Language} [L.Encodable] [L.LORDefinable] {m : ℕ} (σ : Semisentence L m) :
    (⌜σ⌝ : V) = ((⌜σ⌝ : ℕ) : V) := (Sentence.coe_quote_eq_quote σ).symm

/-! ### 2.2 Terms and vectors -/

/-- The code of a predicate constant is `formulaLen`-absolute: `formulaLen LAct P = flN P`. -/
lemma flN_pred {L : Language} [L.Encodable] [L.LORDefinable] {m : ℕ} (σ : Semisentence L m) :
    formulaLen LAct (⌜σ⌝ : V) = (flN (⌜σ⌝ : ℕ) : V) := by
  rw [quote_semisentence_cast]; exact flN_cast _

/-- `#z`: the closed fact `bvarFact (numeral ⌜#z⌝) (cT z)` and `eqOfBvar`. -/
theorem termId_bvar {n : ℕ} (z : Fin n) : TermId (#z : SyntacticSemiterm LAct n) := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜(#z : SyntacticSemiterm LAct n)⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqBvar (z : ℕ) := by rw [hx, Semiterm.quote_bvar]; simp
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfBvar hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pbvar : ℕ) * (2 * x + 1 + (2 * (z : ℕ) + 1)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = 2 * x + 1 + (2 * (z : ℕ) + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfBvar] at hdA
  have hxV : ((x : ℕ) : V) = ⌜(#z : SyntacticSemiterm LAct n)⌝ := by rw [hx]; exact Semiterm.coe_quote_eq_quote _
  rw [Semiterm.quote_bvar] at hD
  obtain ⟨h0, _⟩ := dossT_bvar htbl hL.walkTable rfl hD
  have hcz : cTV ((z : ℕ) : V) = cT (z : ℕ) := rfl
  rw [hcz] at h0
  have hnum : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hcT : IsSemiterm LAct 0 (cT (z : ℕ) : V) := cT_semiterm_LAct 0 _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2z : ((2 * (z : ℕ) + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * (z : ℕ) + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEz : termLen LAct (cT (z : ℕ) : V) ≤ E := by rw [termLen_cT]; push_cast at h2z; exact h2z
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hA : IsFormula LAct (bvarFact (numeral (x : V)) (cT (z : ℕ))) := isFormula_bvarFact hnum hcT
  have hP : formulaLen LAct (Pbvar : V) = (flN (Pbvar : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (bvarFact (numeral (x : V)) (cT (z : ℕ))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * (z : ℕ) + 1) : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * (z : ℕ) + 1))
    refine le_trans (formulaLen_bvarFact_le hB hnum hcT ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_self_add)
    · rw [termLen_cT]; push_cast; exact le_add_self
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok (s := mkStep layoutPieces 72 ?[cT (z : ℕ), ^&i, numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfBvar htbl hL rfl hΓ' hcT hEz (by simp) (termLen_fvar_le hEi) hnum hEx
        (mem_insert_of_mem' h0) mem_insert_self'
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have := pack2 (C := C) hres (by exact_mod_cast (by omega : Q ≤ C)) (by exact_mod_cast (by omega : Nd ≤ C)) (by omega)
  rw [hxV] at this
  exact ⟨_, this⟩

/-- `&x`: the closed fact `fvarFact (numeral ⌜&x⌝) (cT x)` and `eqOfFvar`. -/
theorem termId_fvar {n : ℕ} (z : ℕ) : TermId (&z : SyntacticSemiterm LAct n) := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜(&z : SyntacticSemiterm LAct n)⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqFvar z := by rw [hx, Semiterm.quote_fvar]; simp
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfFvar hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pfvar : ℕ) * (2 * x + 1 + (2 * z + 1)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = 2 * x + 1 + (2 * z + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfFvar] at hdA
  have hxV : ((x : ℕ) : V) = ⌜(&z : SyntacticSemiterm LAct n)⌝ := by rw [hx]; exact Semiterm.coe_quote_eq_quote _
  rw [Semiterm.quote_fvar] at hD
  obtain ⟨h0, _⟩ := dossT_fvar htbl hL.walkTable rfl hD
  have hcz : cTV ((z : ℕ) : V) = cT z := rfl
  rw [hcz] at h0
  have hnum : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hcT : IsSemiterm LAct 0 (cT z : V) := cT_semiterm_LAct 0 _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2z : ((2 * z + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * z + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEz : termLen LAct (cT z : V) ≤ E := by rw [termLen_cT]; push_cast at h2z; exact h2z
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hA : IsFormula LAct (fvarFact (numeral (x : V)) (cT z)) := isFormula_fvarFact hnum hcT
  have hP : formulaLen LAct (Pfvar : V) = (flN (Pfvar : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (fvarFact (numeral (x : V)) (cT z)) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * z + 1) : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * z + 1))
    refine le_trans (formulaLen_fvarFact_le hB hnum hcT ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_self_add)
    · rw [termLen_cT]; push_cast; exact le_add_self
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok (s := mkStep layoutPieces 73 ?[cT z, ^&i, numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfFvar htbl hL rfl hΓ' hcT hEz (by simp) (termLen_fvar_le hEi) hnum hEx
        (mem_insert_of_mem' h0) mem_insert_self'
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have := pack2 (C := C) hres (by exact_mod_cast (by omega : Q ≤ C)) (by exact_mod_cast (by omega : Nd ≤ C)) (by omega)
  rw [hxV] at this
  exact ⟨_, this⟩

/-- The empty suffix: `vRef i 0 = 𝟎 = numeral 0`, by `eqRefl` at `cT 0`. -/
theorem vecId_zero {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) : VecId v 0 := by
  refine ⟨4, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  have hE1 : termLen LAct (cT 0 : V) ≤ E := by
    rw [termLen_cT]; push_cast
    have : ((1 : ℕ) : V) ≤ E := cap_le (a := 1) (by omega) hE
    simpa using this
  obtain ⟨hok, htag, hctx⟩ := lok_eqRefl htbl hL rfl hΓ (cT_semiterm_LAct 0 0) hE1
  refine ⟨?[mkStep layoutPieces 41 ?[cT 0]], listOK_single (hok.mono (by exact_mod_cast (by decide : 8 ≤ 9))),
    noDrop'_single (Or.inl htag), shiftsV_single_tag0 htag, ?_, sizeOK_single (Or.inl htag), ?_⟩
  · simp
  · rw [finalCtx_single, hctx, Nat.cast_zero, vRef_zero, takeLast_zero, numeral_zero, cT_zero]
    exact mem_insert_self'

lemma cap_succ {a b : ℕ} {i E : V} (hab : a + 1 ≤ b) (h : (b : V) + i ≤ E) : (a : V) + (i + 1) ≤ E := by
  calc (a : V) + (i + 1) = ((a + 1 : ℕ) : V) + i := by push_cast; ring
    _ ≤ (b : V) + i := add_le_add ((Nat.cast_le (α := V)).mpr hab) (le_refl i)
    _ ≤ E := h

lemma cap_fvar2 {a b : ℕ} {i E : V} (hab : a + 2 ≤ b) (h : (b : V) + i ≤ E) : i + 1 + 1 ≤ E := by
  calc i + 1 + 1 = ((2 : ℕ) : V) + i := by push_cast; ring
    _ ≤ (b : V) + i := add_le_add ((Nat.cast_le (α := V)).mpr (by omega : 2 ≤ b)) (le_refl i)
    _ ≤ E := h

lemma cap_vRef {b d : ℕ} {c i E : V} (hc : c + 1 ≤ 2 * (d : V)) (hab : 1 + 2 * d ≤ b) (h : (b : V) + i ≤ E) :
    i + 1 + c + 1 ≤ E := by
  have := cap_shift (a := 1) hc hab h
  calc i + 1 + c + 1 = ((1 : ℕ) : V) + (i + 1 + c) := by push_cast; ring
    _ ≤ E := this

lemma one_add_ne_zero (j : V) : j + 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)

lemma le_nat_cast_of_le {a b : ℕ} (h : a ≤ b) : (a : V) ≤ (b : V) := (Nat.cast_le (α := V)).mpr h

/-- The step of the vector invariant: the entry `v.[a]` (`a + (j+1) = k`) at `&(i+1)` (the term
invariant), the shorter suffix at `&(i+1+ct)` (the vector invariant), the closed fact
`adjFact (numeral w) (numeral t) (numeral s)` with `w = t ∷ s`, and `eqOfAdj`. The index is carried as an
OPAQUE `a` with `a + (j + 1) = k` — never `k - (j + 1)`, which the unifier whnf-s into a timeout. -/
theorem vecId_succ {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) (j a : ℕ) (ha : a + (j + 1) = k)
    (ihv : VecId v j) (iht : TermId (v ⟨a, by omega⟩)) : VecId v (j + 1) := by
  obtain ⟨Cj, hCj⟩ := ihv
  obtain ⟨Cm, hCm⟩ := iht
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (⌜v ⟨a, by omega⟩⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = takeLast (vv ℕ v) (j + 1) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = takeLast (vv ℕ v) j := ⟨_, rfl⟩
  have hws : w = t ∷ s := by
    rw [hw, hs, ht]
    simpa using takeLast_vv_succ (V := ℕ) v j a ha
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfAdj hws)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Padjoin : ℕ) * (2 * w + 1 + (2 * t + 1) + (2 * s + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * w + 1 + (2 * t + 1) + (2 * s + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cm + Cj + 2 * tlN t + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfAdj] at hdA
  have htV : ((t : ℕ) : V) = ⌜v ⟨a, by omega⟩⌝ := by rw [ht]; exact Semiterm.coe_quote_eq_quote _
  have hwV : ((w : ℕ) : V) = takeLast (vv V v) ((j : V) + 1) := by rw [hw, takeLast_cast, vv_cast]; push_cast; rfl
  have hsV : ((s : ℕ) : V) = takeLast (vv V v) (j : V) := by rw [hs, takeLast_cast, vv_cast]
  -- the dossier
  have hvv : IsSemitermVec LAct (k : V) (n : V) (vv V v) := isSemitermVec_vv v
  have hjk : (j : V) + 1 ≤ (k : V) := by exact_mod_cast (by omega : j + 1 ≤ k)
  rw [Nat.cast_succ] at hD
  obtain ⟨h0, _, hDt, hDv⟩ := dossV_succ htbl hL.walkTable rfl hvv hjk hD
  have hidx : ((k : V) - ((j : V) + 1)) = (a : V) := by
    have hk : (k : V) = (a : V) + ((j : V) + 1) := by rw [← ha]; push_cast; ring
    rw [hk, add_tsub_cancel_right]
  have hnth : (vv V v).[(a : V)] = ⌜v ⟨a, by omega⟩⌝ := nth_vv v ⟨a, by omega⟩
  rw [hidx, hnth] at h0 hDt hDv
  obtain ⟨ct, hct⟩ : ∃ ct : V, ct = descCountT walkPieces (n : V) (⌜v ⟨a, by omega⟩⌝ : V) := ⟨_, rfl⟩
  rw [← hct] at h0 hDv
  have hctle : ct + 1 ≤ 2 * (tlN t : V) := by
    have := descCountT_walk_le htbl hL.walkTable rfl (isSemiterm_quote (v ⟨a, by omega⟩))
    rwa [← hct, ← htV, tlN_cast] at this
  -- the term list, then the vector list
  obtain ⟨Pt, hPt⟩ := hCm V htbl hL hΓ hDt (cap_succ (by omega) hE)
  have hΓ₁ := hPt.isFormulaSet htbl hΓ
  obtain ⟨Pv, hPv⟩ := hCj V htbl hL hΓ₁ (hPt.dossV hDv) (cap_shift hctle (by omega) hE)
  have hΓ₂ := hPv.isFormulaSet htbl hΓ₁
  have h0' := hPv.mem (hPt.mem h0)
  have ht' := hPv.mem hPt.2.2.2.2.2
  have hv' := hPv.2.2.2.2.2
  rw [← htV] at ht'
  rw [← hsV] at hv'
  -- witnesses
  have hnw : IsSemiterm LAct 0 (numeral (w : V)) := isSemiterm_numeral_LAct _
  have hnt : IsSemiterm LAct 0 (numeral (t : V)) := isSemiterm_numeral_LAct _
  have hns : IsSemiterm LAct 0 (numeral (s : V)) := isSemiterm_numeral_LAct _
  have h2w : ((2 * w + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * w + 1) (by omega) hE
  have h2t : ((2 * t + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * t + 1) (by omega) hE
  have h2s : ((2 * s + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * s + 1) (by omega) hE
  have hEw : termLen LAct (numeral (w : V)) ≤ E := termLen_numeral_le' (by push_cast at h2w; exact h2w)
  have hEt : termLen LAct (numeral (t : V)) ≤ E := termLen_numeral_le' (by push_cast at h2t; exact h2t)
  have hEs : termLen LAct (numeral (s : V)) ≤ E := termLen_numeral_le' (by push_cast at h2s; exact h2s)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hEr : termLen LAct (vRef (i + 1 + ct) (j : V)) ≤ E := termLen_vRef_le (cap_vRef hctle (by omega) hE)
  have hA : IsFormula LAct (adjFact (numeral (w : V)) (numeral (t : V)) (numeral (s : V))) := isFormula_adjFact hnw hnt hns
  have hP : formulaLen LAct (Padjoin : V) = (flN (Padjoin : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (adjFact (numeral (w : V)) (numeral (t : V)) (numeral (s : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * w + 1 + (2 * t + 1) + (2 * s + 1) : ℕ) : V) := by
      exact_mod_cast (by omega : 1 ≤ 2 * w + 1 + (2 * t + 1) + (2 * s + 1))
    refine le_trans (formulaLen_adjFact_le hB hnw hnt hns ?_ ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_self_add le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_add_self le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 74 ?[^&(i + 1), vRef (i + 1 + ct) (j : V), ^&i, numeral (t : V), numeral (s : V), numeral (w : V)])
    (F := eqFactB (^&i) (numeral (w : V))) htbl hΓ₂ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfAdj htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi1) (isSemiterm_vRef _ _) hEr
        (by simp) (termLen_fvar_le hEi) hnt hEt hns hEs hnw hEw
        (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' ht') (mem_insert_of_mem' hv')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  rw [← finalCtx_appendV] at hnode
  have hall := (hPt.append hPv (C := Cm + Cj) le_rfl).append hnode (C := C) (by omega)
  rw [hwV] at hall
  rw [Nat.cast_succ, vRef_of_ne (one_add_ne_zero _)]
  exact ⟨_, hall⟩

/-- The whole vector from the entries' term invariants. -/
theorem vecId_of_terms {n k : ℕ} (v : Fin k → SyntacticSemiterm LAct n) (ih : ∀ m, TermId (v m)) : VecId v k := by
  have : ∀ j ≤ k, VecId v j := by
    intro j
    induction j with
    | zero => intro _; exact vecId_zero v
    | succ j ihj =>
      intro hj
      exact vecId_succ v j (k - (j + 1)) (by omega) (ihj (by omega)) (ih _)
  exact this k le_rfl

/-- `func f v`: the vector invariant at `&(i+1)`, the closed fact `funcFact (numeral ⌜func f v⌝) (cT k)
(cT ⌜f⌝) (numeral ⌜v⌝)` and `eqOfFunc`. -/
theorem termId_func {n k : ℕ} (f : LAct.Func k) (v : Fin k → SyntacticSemiterm LAct n) (ih : ∀ m, TermId (v m)) :
    TermId (Semiterm.func f v) := by
  obtain ⟨Cv, hCv⟩ := vecId_of_terms v ih
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (⌜Semiterm.func f v⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = vv ℕ v := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = Encodable.encode f := ⟨_, rfl⟩
  have hf : (⌜f⌝ : ℕ) = Encodable.encode f := by simp [GödelQuote.quote]
  have htq : t = qqFunc k g u := by
    rw [ht, hu, hg, Semiterm.quote_func, hf]; simp [vv]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfFunc htq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pfunc : ℕ) * (2 * t + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * t + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cv + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfFunc] at hdA
  have htV : ((t : ℕ) : V) = ⌜Semiterm.func f v⌝ := by rw [ht]; exact Semiterm.coe_quote_eq_quote _
  have huV : ((u : ℕ) : V) = vv V v := by rw [hu, vv_cast]
  have hgV : cT g = cTV (⌜f⌝ : V) := by rw [hg]; rfl
  -- the dossier
  have hkf : LAct.IsFunc (k : V) (⌜f⌝ : V) := isFunc_quote_quote.mpr ⟨f, rfl⟩
  have hq : (⌜Semiterm.func f v⌝ : V) = ^func (k : V) ⌜f⌝ (vv V v) := rfl
  rw [hq] at hD
  obtain ⟨h0, _, _, hDv⟩ := dossT_func htbl hL.walkTable rfl hkf (isSemitermVec_vv v) hD
  rw [← hgV] at h0
  have hck : cTV (k : V) = cT k := rfl
  rw [hck] at h0
  obtain ⟨Pv, hPv⟩ := hCv V htbl hL hΓ hDv (cap_succ (by omega) hE)
  have hΓ₁ := hPv.isFormulaSet htbl hΓ
  have h0' := hPv.mem h0
  have hv' := hPv.2.2.2.2.2
  rw [show takeLast (vv V v) (k : V) = vv V v by rw [← len_vv (V := V) v, takeLast_len_self], ← huV] at hv'
  -- witnesses
  have hnt : IsSemiterm LAct 0 (numeral (t : V)) := isSemiterm_numeral_LAct _
  have hnu : IsSemiterm LAct 0 (numeral (u : V)) := isSemiterm_numeral_LAct _
  have hck' : IsSemiterm LAct 0 (cT k : V) := cT_semiterm_LAct 0 _
  have hcg : IsSemiterm LAct 0 (cT g : V) := cT_semiterm_LAct 0 _
  have h2t : ((2 * t + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * t + 1) (by omega) hE
  have h2u : ((2 * u + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * u + 1) (by omega) hE
  have h2k : ((2 * k + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * k + 1) (by omega) hE
  have h2g : ((2 * g + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * g + 1) (by omega) hE
  have hEt : termLen LAct (numeral (t : V)) ≤ E := termLen_numeral_le' (by push_cast at h2t; exact h2t)
  have hEu : termLen LAct (numeral (u : V)) ≤ E := termLen_numeral_le' (by push_cast at h2u; exact h2u)
  have hEk : termLen LAct (cT k : V) ≤ E := by rw [termLen_cT]; push_cast at h2k; exact h2k
  have hEg : termLen LAct (cT g : V) ≤ E := by rw [termLen_cT]; push_cast at h2g; exact h2g
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hEr : termLen LAct (vRef (i + 1) (k : V)) ≤ E := termLen_vRef_le hEi1
  have hA : IsFormula LAct (funcFact (numeral (t : V)) (cT k) (cT g) (numeral (u : V))) := isFormula_funcFact hnt hck' hcg hnu
  have hP : formulaLen LAct (Pfunc : V) = (flN (Pfunc : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (funcFact (numeral (t : V)) (cT k) (cT g) (numeral (u : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * t + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1) : ℕ) : V) := by
      exact_mod_cast (by omega : 1 ≤ 2 * t + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1))
    refine le_trans (formulaLen_funcFact_le hB hnt hck' hcg hnu ?_ ?_ ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_self_add (le_trans le_self_add le_self_add))
    · rw [termLen_cT]; push_cast; exact le_trans le_add_self (le_trans le_self_add le_self_add)
    · rw [termLen_cT]; push_cast; exact le_trans le_add_self le_self_add
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 71 ?[^&i, cT k, cT g, vRef (i + 1) (k : V), numeral (u : V), numeral (t : V)])
    (F := eqFactB (^&i) (numeral (t : V))) htbl hΓ₁ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfFunc htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) hck' hEk hcg hEg
        (isSemiterm_vRef _ _) hEr hnu hEu hnt hEt
        (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hv')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  have hall := hPv.append hnode (C := C) (by omega)
  rw [htV] at hall
  exact ⟨_, hall⟩

/-- **Every meta term has the numeral-identification invariant.** -/
theorem numId_term {n : ℕ} : ∀ t : SyntacticSemiterm LAct n, TermId t
  | FirstOrder.Semiterm.bvar z => termId_bvar z
  | FirstOrder.Semiterm.fvar x => termId_fvar x
  | FirstOrder.Semiterm.func f v => termId_func f v (fun m ↦ numId_term (v m))

/-! ### 2.3 Formulas -/

/-- `⊤`: the closed fact `verumFact (numeral ⌜⊤⌝)` and `eqOfVerum`. -/
theorem formId_verum {n : ℕ} : FormId (⊤ : Semiproposition LAct n) := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜(⊤ : Semiproposition LAct n)⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqVerum := by rw [hx, Semiformula.quote_verum]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfVerum hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pverum : ℕ) * (2 * x + 1) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = 2 * x + 1 + Q + Nd + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfVerum] at hdA
  have hxV : ((x : ℕ) : V) = ⌜(⊤ : Semiproposition LAct n)⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  rw [Semiformula.quote_verum] at hD
  obtain ⟨h0, _⟩ := dossF_verum htbl hL.walkTable rfl hD
  have hnum : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hA : IsFormula LAct (verumFact (numeral (x : V))) := isFormula_verumFact hnum
  have hP : formulaLen LAct (Pverum : V) = (flN (Pverum : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (verumFact (numeral (x : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1)
    refine le_trans (formulaLen_verumFact_le hB hnum ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_refl _)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok (s := mkStep layoutPieces 69 ?[^&i, numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfVerum htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) hnum hEx
        (mem_insert_of_mem' h0) mem_insert_self'
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have := pack2 (C := C) hres (by exact_mod_cast (by omega : Q ≤ C)) (by exact_mod_cast (by omega : Nd ≤ C)) (by omega)
  rw [hxV] at this
  exact ⟨_, this⟩

/-- `⊥`. -/
theorem formId_falsum {n : ℕ} : FormId (⊥ : Semiproposition LAct n) := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜(⊥ : Semiproposition LAct n)⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqFalsum := by rw [hx, Semiformula.quote_falsum]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfFalsum hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pfalsum : ℕ) * (2 * x + 1) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = 2 * x + 1 + Q + Nd + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfFalsum] at hdA
  have hxV : ((x : ℕ) : V) = ⌜(⊥ : Semiproposition LAct n)⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  rw [Semiformula.quote_falsum] at hD
  obtain ⟨h0, _⟩ := dossF_falsum htbl hL.walkTable rfl hD
  have hnum : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hA : IsFormula LAct (falsumFact (numeral (x : V))) := isFormula_falsumFact hnum
  have hP : formulaLen LAct (Pfalsum : V) = (flN (Pfalsum : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (falsumFact (numeral (x : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1)
    refine le_trans (formulaLen_falsumFact_le hB hnum ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_refl _)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok (s := mkStep layoutPieces 70 ?[^&i, numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfFalsum htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) hnum hEx
        (mem_insert_of_mem' h0) mem_insert_self'
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have := pack2 (C := C) hres (by exact_mod_cast (by omega : Q ≤ C)) (by exact_mod_cast (by omega : Nd ≤ C)) (by omega)
  rw [hxV] at this
  exact ⟨_, this⟩

/-- The walk's eigenvariable count of a quoted formula is bounded by twice its (absolute) length. -/
lemma descCountF_quote_le {tbl N : V} (htbl : TableOK tbl N) (hL : LayoutTable tbl) {n : ℕ}
    (ψ : Semiproposition LAct n) {q : ℕ} (hq : q = (⌜ψ⌝ : ℕ)) :
    descCountF walkPieces (n : V) (⌜ψ⌝ : V) + 1 ≤ 2 * (flN q : V) := by
  have := descCountF_walk_le htbl hL.walkTable rfl (Semiformula.quote_isSemiformula (V := V) ψ)
  have hl : formulaLen LAct (⌜ψ⌝ : V) = (flN q : V) := by
    rw [hq, ← Semiformula.coe_quote_eq_quote (V := V) ψ, flN_cast]
  rwa [hl] at this

/-- `⋏`: `ψ` at `&(i+1)`, `φ` at `&(i+cq+1)`, the closed fact and `eqOfAnd`. -/
theorem formId_and {n : ℕ} (φ ψ : Semiproposition LAct n) (ihφ : FormId φ) (ihψ : FormId ψ) : FormId (φ ⋏ ψ) := by
  obtain ⟨Cφ, hCφ⟩ := ihφ
  obtain ⟨Cψ, hCψ⟩ := ihψ
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜φ ⋏ ψ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (⌜φ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = (⌜ψ⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqAnd p q := by rw [hx, hp, hq, Semiformula.quote_and]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfAnd hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pand : ℕ) * (2 * x + 1 + (2 * p + 1) + (2 * q + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + (2 * p + 1) + (2 * q + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cφ + Cψ + 2 * flN q + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfAnd] at hdA
  have hxV : ((x : ℕ) : V) = ⌜φ ⋏ ψ⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  have hpV : ((p : ℕ) : V) = ⌜φ⌝ := by rw [hp]; exact Semiformula.coe_quote_eq_quote _
  have hqV : ((q : ℕ) : V) = ⌜ψ⌝ := by rw [hq]; exact Semiformula.coe_quote_eq_quote _
  rw [Semiformula.quote_and] at hD
  obtain ⟨h0, _, hDq, hDp⟩ := dossF_and htbl hL.walkTable rfl (Semiformula.quote_isSemiformula φ)
    (Semiformula.quote_isSemiformula ψ) hD
  obtain ⟨cq, hcq⟩ : ∃ cq : V, cq = descCountF walkPieces (n : V) (⌜ψ⌝ : V) := ⟨_, rfl⟩
  rw [← hcq] at h0 hDp
  have hcqle : cq + 1 ≤ 2 * (flN q : V) := by rw [hcq]; exact descCountF_quote_le htbl hL ψ hq
  -- ψ at i + 1, then φ at i + cq + 1
  obtain ⟨Pq, hPq⟩ := hCψ V htbl hL hΓ hDq (cap_succ (by omega) hE)
  have hΓ₁ := hPq.isFormulaSet htbl hΓ
  have hEp : (Cφ : V) + (i + cq + 1) ≤ E := by
    have := cap_shift (a := Cφ) hcqle (by omega) hE
    rwa [show i + 1 + cq = i + cq + 1 by ring] at this
  obtain ⟨Pp, hPp⟩ := hCφ V htbl hL hΓ₁ (hPq.dossF hDp) hEp
  have hΓ₂ := hPp.isFormulaSet htbl hΓ₁
  have h0' := hPp.mem (hPq.mem h0)
  have hq' := hPp.mem hPq.2.2.2.2.2
  have hp' := hPp.2.2.2.2.2
  rw [← hqV] at hq'
  rw [← hpV] at hp'
  -- witnesses
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hnp : IsSemiterm LAct 0 (numeral (p : V)) := isSemiterm_numeral_LAct _
  have hnq : IsSemiterm LAct 0 (numeral (q : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2p : ((2 * p + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * p + 1) (by omega) hE
  have h2q : ((2 * q + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * q + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEp' : termLen LAct (numeral (p : V)) ≤ E := termLen_numeral_le' (by push_cast at h2p; exact h2p)
  have hEq' : termLen LAct (numeral (q : V)) ≤ E := termLen_numeral_le' (by push_cast at h2q; exact h2q)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hEic : i + cq + 1 + 1 ≤ E := by
    have := cap_vRef hcqle (by omega) hE
    rwa [show i + 1 + cq + 1 = i + cq + 1 + 1 by ring] at this
  have hA : IsFormula LAct (andFact (numeral (x : V)) (numeral (p : V)) (numeral (q : V))) := isFormula_andFact hnx hnp hnq
  have hP : formulaLen LAct (Pand : V) = (flN (Pand : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (andFact (numeral (x : V)) (numeral (p : V)) (numeral (q : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * p + 1) + (2 * q + 1) : ℕ) : V) := by
      exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * p + 1) + (2 * q + 1))
    refine le_trans (formulaLen_andFact_le hB hnx hnp hnq ?_ ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_self_add le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_add_self le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 63 ?[^&i, ^&(i + cq + 1), ^&(i + 1), numeral (p : V), numeral (q : V), numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ₂ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfAnd htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) (by simp) (termLen_fvar_le hEic)
        (by simp) (termLen_fvar_le hEi1) hnp hEp' hnq hEq' hnx hEx
        (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hp') (mem_insert_of_mem' hq')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  rw [← finalCtx_appendV] at hnode
  have hall := (hPq.append hPp (C := Cψ + Cφ) le_rfl).append hnode (C := C) (by omega)
  rw [hxV] at hall
  exact ⟨_, hall⟩

/-- `⋎`. -/
theorem formId_or {n : ℕ} (φ ψ : Semiproposition LAct n) (ihφ : FormId φ) (ihψ : FormId ψ) : FormId (φ ⋎ ψ) := by
  obtain ⟨Cφ, hCφ⟩ := ihφ
  obtain ⟨Cψ, hCψ⟩ := ihψ
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜φ ⋎ ψ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (⌜φ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = (⌜ψ⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqOr p q := by rw [hx, hp, hq, Semiformula.quote_or]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfOr hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Por : ℕ) * (2 * x + 1 + (2 * p + 1) + (2 * q + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + (2 * p + 1) + (2 * q + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cφ + Cψ + 2 * flN q + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfOr] at hdA
  have hxV : ((x : ℕ) : V) = ⌜φ ⋎ ψ⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  have hpV : ((p : ℕ) : V) = ⌜φ⌝ := by rw [hp]; exact Semiformula.coe_quote_eq_quote _
  have hqV : ((q : ℕ) : V) = ⌜ψ⌝ := by rw [hq]; exact Semiformula.coe_quote_eq_quote _
  rw [Semiformula.quote_or] at hD
  obtain ⟨h0, _, hDq, hDp⟩ := dossF_or htbl hL.walkTable rfl (Semiformula.quote_isSemiformula φ)
    (Semiformula.quote_isSemiformula ψ) hD
  obtain ⟨cq, hcq⟩ : ∃ cq : V, cq = descCountF walkPieces (n : V) (⌜ψ⌝ : V) := ⟨_, rfl⟩
  rw [← hcq] at h0 hDp
  have hcqle : cq + 1 ≤ 2 * (flN q : V) := by rw [hcq]; exact descCountF_quote_le htbl hL ψ hq
  obtain ⟨Pq, hPq⟩ := hCψ V htbl hL hΓ hDq (cap_succ (by omega) hE)
  have hΓ₁ := hPq.isFormulaSet htbl hΓ
  have hEp : (Cφ : V) + (i + cq + 1) ≤ E := by
    have := cap_shift (a := Cφ) hcqle (by omega) hE
    rwa [show i + 1 + cq = i + cq + 1 by ring] at this
  obtain ⟨Pp, hPp⟩ := hCφ V htbl hL hΓ₁ (hPq.dossF hDp) hEp
  have hΓ₂ := hPp.isFormulaSet htbl hΓ₁
  have h0' := hPp.mem (hPq.mem h0)
  have hq' := hPp.mem hPq.2.2.2.2.2
  have hp' := hPp.2.2.2.2.2
  rw [← hqV] at hq'
  rw [← hpV] at hp'
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hnp : IsSemiterm LAct 0 (numeral (p : V)) := isSemiterm_numeral_LAct _
  have hnq : IsSemiterm LAct 0 (numeral (q : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2p : ((2 * p + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * p + 1) (by omega) hE
  have h2q : ((2 * q + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * q + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEp' : termLen LAct (numeral (p : V)) ≤ E := termLen_numeral_le' (by push_cast at h2p; exact h2p)
  have hEq' : termLen LAct (numeral (q : V)) ≤ E := termLen_numeral_le' (by push_cast at h2q; exact h2q)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hEic : i + cq + 1 + 1 ≤ E := by
    have := cap_vRef hcqle (by omega) hE
    rwa [show i + 1 + cq + 1 = i + cq + 1 + 1 by ring] at this
  have hA : IsFormula LAct (orFact (numeral (x : V)) (numeral (p : V)) (numeral (q : V))) := isFormula_orFact hnx hnp hnq
  have hP : formulaLen LAct (Por : V) = (flN (Por : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (orFact (numeral (x : V)) (numeral (p : V)) (numeral (q : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * p + 1) + (2 * q + 1) : ℕ) : V) := by
      exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * p + 1) + (2 * q + 1))
    refine le_trans (formulaLen_orFact_le hB hnx hnp hnq ?_ ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_self_add le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_add_self le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 64 ?[^&i, ^&(i + cq + 1), ^&(i + 1), numeral (p : V), numeral (q : V), numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ₂ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfOr htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) (by simp) (termLen_fvar_le hEic)
        (by simp) (termLen_fvar_le hEi1) hnp hEp' hnq hEq' hnx hEx
        (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hp') (mem_insert_of_mem' hq')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  rw [← finalCtx_appendV] at hnode
  have hall := (hPq.append hPp (C := Cψ + Cφ) le_rfl).append hnode (C := C) (by omega)
  rw [hxV] at hall
  exact ⟨_, hall⟩

/-- `∀`: the body at `&(i+1)` (arity `n + 1`), the closed fact and `eqOfAll`. -/
theorem formId_all {n : ℕ} (φ : Semiproposition LAct (n + 1)) (ih : FormId φ) : FormId (∀¹ φ) := by
  obtain ⟨Cφ, hCφ⟩ := ih
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜∀¹ φ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (⌜φ⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqAll p := by rw [hx, hp, Semiformula.quote_all]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfAll hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pall : ℕ) * (2 * x + 1 + (2 * p + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + (2 * p + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cφ + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfAll] at hdA
  have hxV : ((x : ℕ) : V) = ⌜∀¹ φ⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  have hpV : ((p : ℕ) : V) = ⌜φ⌝ := by rw [hp]; exact Semiformula.coe_quote_eq_quote _
  rw [Semiformula.quote_all] at hD
  have hφ : IsSemiformula LAct ((n : V) + 1) (⌜φ⌝ : V) := by
    have := Semiformula.quote_isSemiformula (V := V) φ; rwa [Nat.cast_succ] at this
  obtain ⟨h0, _, hDp⟩ := dossF_all htbl hL.walkTable rfl hφ hD
  rw [← Nat.cast_succ] at hDp
  obtain ⟨Pp, hPp⟩ := hCφ V htbl hL hΓ hDp (cap_succ (by omega) hE)
  have hΓ₁ := hPp.isFormulaSet htbl hΓ
  have h0' := hPp.mem h0
  have hp' := hPp.2.2.2.2.2
  rw [← hpV] at hp'
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hnp : IsSemiterm LAct 0 (numeral (p : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2p : ((2 * p + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * p + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEp' : termLen LAct (numeral (p : V)) ≤ E := termLen_numeral_le' (by push_cast at h2p; exact h2p)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hA : IsFormula LAct (allFact (numeral (x : V)) (numeral (p : V))) := isFormula_allFact hnx hnp
  have hP : formulaLen LAct (Pall : V) = (flN (Pall : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (allFact (numeral (x : V)) (numeral (p : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * p + 1) : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * p + 1))
    refine le_trans (formulaLen_allFact_le hB hnx hnp ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 65 ?[^&i, ^&(i + 1), numeral (p : V), numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ₁ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfAll htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) (by simp) (termLen_fvar_le hEi1)
        hnp hEp' hnx hEx (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hp')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  have hall := hPp.append hnode (C := C) (by omega)
  rw [hxV] at hall
  exact ⟨_, hall⟩

/-- `∃`. -/
theorem formId_ex {n : ℕ} (φ : Semiproposition LAct (n + 1)) (ih : FormId φ) : FormId (∃¹ φ) := by
  obtain ⟨Cφ, hCφ⟩ := ih
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜∃¹ φ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (⌜φ⌝ : ℕ) := ⟨_, rfl⟩
  have hxq : x = qqExs p := by rw [hx, hp, Semiformula.quote_ex]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfExs hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pexs : ℕ) * (2 * x + 1 + (2 * p + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + (2 * p + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cφ + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfExs] at hdA
  have hxV : ((x : ℕ) : V) = ⌜∃¹ φ⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  have hpV : ((p : ℕ) : V) = ⌜φ⌝ := by rw [hp]; exact Semiformula.coe_quote_eq_quote _
  rw [Semiformula.quote_ex] at hD
  have hφ : IsSemiformula LAct ((n : V) + 1) (⌜φ⌝ : V) := by
    have := Semiformula.quote_isSemiformula (V := V) φ; rwa [Nat.cast_succ] at this
  obtain ⟨h0, _, hDp⟩ := dossF_exs htbl hL.walkTable rfl hφ hD
  rw [← Nat.cast_succ] at hDp
  obtain ⟨Pp, hPp⟩ := hCφ V htbl hL hΓ hDp (cap_succ (by omega) hE)
  have hΓ₁ := hPp.isFormulaSet htbl hΓ
  have h0' := hPp.mem h0
  have hp' := hPp.2.2.2.2.2
  rw [← hpV] at hp'
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hnp : IsSemiterm LAct 0 (numeral (p : V)) := isSemiterm_numeral_LAct _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2p : ((2 * p + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * p + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEp' : termLen LAct (numeral (p : V)) ≤ E := termLen_numeral_le' (by push_cast at h2p; exact h2p)
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hA : IsFormula LAct (exsFact (numeral (x : V)) (numeral (p : V))) := isFormula_exsFact hnx hnp
  have hP : formulaLen LAct (Pexs : V) = (flN (Pexs : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (exsFact (numeral (x : V)) (numeral (p : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * p + 1) : ℕ) : V) := by exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * p + 1))
    refine le_trans (formulaLen_exsFact_le hB hnx hnp ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_self_add)
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 66 ?[^&i, ^&(i + 1), numeral (p : V), numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ₁ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfExs htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) (by simp) (termLen_fvar_le hEi1)
        hnp hEp' hnx hEx (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hp')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  have hall := hPp.append hnode (C := C) (by omega)
  rw [hxV] at hall
  exact ⟨_, hall⟩

/-- `rel R v`: the vector invariant at `&(i+1)`, the closed fact `relFact (numeral ⌜rel R v⌝) (cT k)
(cT ⌜R⌝) (numeral ⌜v⌝)` and `eqOfRel`. -/
theorem formId_rel {n k : ℕ} (R : LAct.Rel k) (v : Fin k → SyntacticSemiterm LAct n) : FormId (Semiformula.rel R v) := by
  obtain ⟨Cv, hCv⟩ := vecId_of_terms v (fun m ↦ numId_term (v m))
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜Semiformula.rel R v⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = vv ℕ v := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = Encodable.encode R := ⟨_, rfl⟩
  have hR : (⌜R⌝ : ℕ) = Encodable.encode R := by simp [GödelQuote.quote]
  have hxq : x = qqRel k g u := by
    rw [hx, hu, hg, Semiformula.quote_rel, hR]; simp [vv]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfRel hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Prel : ℕ) * (2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cv + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfRel] at hdA
  have hxV : ((x : ℕ) : V) = ⌜Semiformula.rel R v⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  have huV : ((u : ℕ) : V) = vv V v := by rw [hu, vv_cast]
  have hgV : cT g = cTV (⌜R⌝ : V) := by rw [hg]; rfl
  have hkR : LAct.IsRel (k : V) (⌜R⌝ : V) := isRel_quote_quote.mpr ⟨R, rfl⟩
  have hq : (⌜Semiformula.rel R v⌝ : V) = ^rel (k : V) ⌜R⌝ (vv V v) := rfl
  rw [hq] at hD
  obtain ⟨h0, _, _, hDv⟩ := dossF_rel htbl hL.walkTable rfl hkR (isSemitermVec_vv v) hD
  rw [← hgV] at h0
  have hck : cTV (k : V) = cT k := rfl
  rw [hck] at h0
  obtain ⟨Pv, hPv⟩ := hCv V htbl hL hΓ hDv (cap_succ (by omega) hE)
  have hΓ₁ := hPv.isFormulaSet htbl hΓ
  have h0' := hPv.mem h0
  have hv' := hPv.2.2.2.2.2
  rw [show takeLast (vv V v) (k : V) = vv V v by rw [← len_vv (V := V) v, takeLast_len_self], ← huV] at hv'
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hnu : IsSemiterm LAct 0 (numeral (u : V)) := isSemiterm_numeral_LAct _
  have hck' : IsSemiterm LAct 0 (cT k : V) := cT_semiterm_LAct 0 _
  have hcg : IsSemiterm LAct 0 (cT g : V) := cT_semiterm_LAct 0 _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2u : ((2 * u + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * u + 1) (by omega) hE
  have h2k : ((2 * k + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * k + 1) (by omega) hE
  have h2g : ((2 * g + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * g + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEu : termLen LAct (numeral (u : V)) ≤ E := termLen_numeral_le' (by push_cast at h2u; exact h2u)
  have hEk : termLen LAct (cT k : V) ≤ E := by rw [termLen_cT]; push_cast at h2k; exact h2k
  have hEg : termLen LAct (cT g : V) ≤ E := by rw [termLen_cT]; push_cast at h2g; exact h2g
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hEr : termLen LAct (vRef (i + 1) (k : V)) ≤ E := termLen_vRef_le hEi1
  have hA : IsFormula LAct (relFact (numeral (x : V)) (cT k) (cT g) (numeral (u : V))) := isFormula_relFact hnx hck' hcg hnu
  have hP : formulaLen LAct (Prel : V) = (flN (Prel : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (relFact (numeral (x : V)) (cT k) (cT g) (numeral (u : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1) : ℕ) : V) := by
      exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1))
    refine le_trans (formulaLen_relFact_le hB hnx hck' hcg hnu ?_ ?_ ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_self_add (le_trans le_self_add le_self_add))
    · rw [termLen_cT]; push_cast; exact le_trans le_add_self (le_trans le_self_add le_self_add)
    · rw [termLen_cT]; push_cast; exact le_trans le_add_self le_self_add
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 67 ?[^&i, cT k, cT g, vRef (i + 1) (k : V), numeral (u : V), numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ₁ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfRel htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) hck' hEk hcg hEg
        (isSemiterm_vRef _ _) hEr hnu hEu hnx hEx
        (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hv')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  have hall := hPv.append hnode (C := C) (by omega)
  rw [hxV] at hall
  exact ⟨_, hall⟩

/-- `nrel R v`. -/
theorem formId_nrel {n k : ℕ} (R : LAct.Rel k) (v : Fin k → SyntacticSemiterm LAct n) : FormId (Semiformula.nrel R v) := by
  obtain ⟨Cv, hCv⟩ := vecId_of_terms v (fun m ↦ numId_term (v m))
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (⌜Semiformula.nrel R v⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = vv ℕ v := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = Encodable.encode R := ⟨_, rfl⟩
  have hR : (⌜R⌝ : ℕ) = Encodable.encode R := by simp [GödelQuote.quote]
  have hxq : x = qqNRel k g u := by
    rw [hx, hu, hg, Semiformula.quote_nrel, hR]; simp [vv]
  obtain ⟨Nd, hNd⟩ := closedDer_of_lib (lib_cfNRel hxq)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = flN (Pnrel : ℕ) * (2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1)) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1) + Q + Nd + 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = Cv + Cn + 4 := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  intro V _ _ tbl N E Γ i htbl hL hΓ hD hE
  obtain ⟨dA, hdA, hdl⟩ := hNd V
  simp only at hdA hdl
  rw [code_cfNRel] at hdA
  have hxV : ((x : ℕ) : V) = ⌜Semiformula.nrel R v⌝ := by rw [hx]; exact Semiformula.coe_quote_eq_quote _
  have huV : ((u : ℕ) : V) = vv V v := by rw [hu, vv_cast]
  have hgV : cT g = cTV (⌜R⌝ : V) := by rw [hg]; rfl
  have hkR : LAct.IsRel (k : V) (⌜R⌝ : V) := isRel_quote_quote.mpr ⟨R, rfl⟩
  have hq : (⌜Semiformula.nrel R v⌝ : V) = ^nrel (k : V) ⌜R⌝ (vv V v) := rfl
  rw [hq] at hD
  obtain ⟨h0, _, _, hDv⟩ := dossF_nrel htbl hL.walkTable rfl hkR (isSemitermVec_vv v) hD
  rw [← hgV] at h0
  have hck : cTV (k : V) = cT k := rfl
  rw [hck] at h0
  obtain ⟨Pv, hPv⟩ := hCv V htbl hL hΓ hDv (cap_succ (by omega) hE)
  have hΓ₁ := hPv.isFormulaSet htbl hΓ
  have h0' := hPv.mem h0
  have hv' := hPv.2.2.2.2.2
  rw [show takeLast (vv V v) (k : V) = vv V v by rw [← len_vv (V := V) v, takeLast_len_self], ← huV] at hv'
  have hnx : IsSemiterm LAct 0 (numeral (x : V)) := isSemiterm_numeral_LAct _
  have hnu : IsSemiterm LAct 0 (numeral (u : V)) := isSemiterm_numeral_LAct _
  have hck' : IsSemiterm LAct 0 (cT k : V) := cT_semiterm_LAct 0 _
  have hcg : IsSemiterm LAct 0 (cT g : V) := cT_semiterm_LAct 0 _
  have h2x : ((2 * x + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * x + 1) (by omega) hE
  have h2u : ((2 * u + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * u + 1) (by omega) hE
  have h2k : ((2 * k + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * k + 1) (by omega) hE
  have h2g : ((2 * g + 1 : ℕ) : V) ≤ E := cap_le (a := 2 * g + 1) (by omega) hE
  have hEx : termLen LAct (numeral (x : V)) ≤ E := termLen_numeral_le' (by push_cast at h2x; exact h2x)
  have hEu : termLen LAct (numeral (u : V)) ≤ E := termLen_numeral_le' (by push_cast at h2u; exact h2u)
  have hEk : termLen LAct (cT k : V) ≤ E := by rw [termLen_cT]; push_cast at h2k; exact h2k
  have hEg : termLen LAct (cT g : V) ≤ E := by rw [termLen_cT]; push_cast at h2g; exact h2g
  have hEi : i + 1 ≤ E := cap_fvar (a := 0) (by omega) hE
  have hEi1 : i + 1 + 1 ≤ E := cap_fvar2 (a := 0) (by omega) hE
  have hEr : termLen LAct (vRef (i + 1) (k : V)) ≤ E := termLen_vRef_le hEi1
  have hA : IsFormula LAct (nrelFact (numeral (x : V)) (cT k) (cT g) (numeral (u : V))) := isFormula_nrelFact hnx hck' hcg hnu
  have hP : formulaLen LAct (Pnrel : V) = (flN (Pnrel : ℕ) : V) := flN_pred _
  have hQ' : formulaLen LAct (nrelFact (numeral (x : V)) (cT k) (cT g) (numeral (u : V))) ≤ (Q : V) := by
    have hB : (1 : V) ≤ ((2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1) : ℕ) : V) := by
      exact_mod_cast (by omega : 1 ≤ 2 * x + 1 + (2 * k + 1) + (2 * g + 1) + (2 * u + 1))
    refine le_trans (formulaLen_nrelFact_le hB hnx hck' hcg hnu ?_ ?_ ?_ ?_) ?_
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_trans le_self_add (le_trans le_self_add le_self_add))
    · rw [termLen_cT]; push_cast; exact le_trans le_add_self (le_trans le_self_add le_self_add)
    · rw [termLen_cT]; push_cast; exact le_trans le_add_self le_self_add
    · exact le_trans (termLen_numeral_le _) (by push_cast; exact le_add_self)
    · rw [hP, hQ]; push_cast; exact le_refl _
  have hres := lemmaThenHorn_ok
    (s := mkStep layoutPieces 68 ?[^&i, cT k, cT g, vRef (i + 1) (k : V), numeral (u : V), numeral (x : V)])
    (F := eqFactB (^&i) (numeral (x : V))) htbl hΓ₁ hA hdA hQ' hdl (fun hΓ' ↦ by
      obtain ⟨hok, htag, hctx⟩ := lok_eqOfNRel htbl hL rfl hΓ' (by simp) (termLen_fvar_le hEi) hck' hEk hcg hEg
        (isSemiterm_vRef _ _) hEr hnu hEu hnx hEx
        (mem_insert_of_mem' h0') mem_insert_self' (mem_insert_of_mem' hv')
      exact ⟨hok.mono (by exact_mod_cast (by decide : 8 ≤ 9)), htag, hctx⟩)
  have hnode := pack2 (C := Cn) hres (by exact_mod_cast (by omega : Q ≤ Cn)) (by exact_mod_cast (by omega : Nd ≤ Cn)) (by omega)
  have hall := hPv.append hnode (C := C) (by omega)
  rw [hxV] at hall
  exact ⟨_, hall⟩

/-- **Every meta formula has the numeral-identification invariant.** -/
theorem numId_formula {n : ℕ} : ∀ φ : Semiproposition LAct n, FormId φ
  | FirstOrder.Semiformula.verum => formId_verum
  | FirstOrder.Semiformula.falsum => formId_falsum
  | FirstOrder.Semiformula.rel R v => formId_rel R v
  | FirstOrder.Semiformula.nrel R v => formId_nrel R v
  | FirstOrder.Semiformula.and φ ψ => formId_and φ ψ (numId_formula φ) (numId_formula ψ)
  | FirstOrder.Semiformula.or φ ψ => formId_or φ ψ (numId_formula φ) (numId_formula ψ)
  | FirstOrder.Semiformula.all φ => formId_all φ (numId_formula φ)
  | FirstOrder.Semiformula.exs φ => formId_ex φ (numId_formula φ)

/-! ### 2.4 Sentences, and the cost -/

/-- **The numeral identification of a meta semisentence** `χ : Semisentence LAct n` (the form the pin
uses at `χ : Semisentence LAct 1`): for some standard `C`, in every model, from the walk dossier of `⌜χ⌝`
at `&i` a shift-free list applicable at cap `9` under `C + i ≤ E`, of length `≤ C`, `SizeOK C C`, leaving
`eqFact (^&i) (numeral ⌜χ⌝)`. -/
theorem numId_sentence {n : ℕ} (χ : Semisentence LAct n) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i : V},
      TableOK tbl N → LayoutTable tbl → IsFormulaSet LAct Γ →
      DossF walkPieces Γ n (⌜χ⌝ : V) i → (C : V) + i ≤ E →
      ∃ P : V, NumInv tbl E Γ C P (eqFact (^&i) (numeral (⌜χ⌝ : V))) := by
  obtain ⟨C, hC⟩ := numId_formula (Rewriting.emb χ : Semiproposition LAct n)
  exact ⟨C, fun V _ _ tbl N E Γ i htbl hL hΓ hD hE ↦ by
    rw [Sentence.quote_def] at hD ⊢
    exact hC V htbl hL hΓ hD hE⟩

lemma ctxBoundG_mono {G Γ L L' : V} (h : L ≤ L') : ctxBoundG G Γ L ≤ ctxBoundG G Γ L' := by
  unfold ctxBoundG
  exact add_le_add (add_le_add (le_refl _) (mul_le_mul h (le_refl _) (by simp) (by simp)))
    (mul_le_mul (add_le_add (mul_le_mul h h (by simp) (by simp)) h) (le_refl _) (by simp) (by simp))

/-- **The cost of an invariant list** (`Frag1.costSum_le_of_sizeOK` at cap `9`, `len ≤ C`): LINEAR in
`N`, `E`, `setLen Γ` and `fvOccS Γ` for a standard `C` and a standard row-body bound `B`. -/
theorem numInv_cost {tbl N E B Γ P F : V} {C : ℕ} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (h : NumInv tbl E Γ C P F) :
    costSum N E Γ P ≤ (C : V) * (costK N E B ((9 : ℕ) : V) (C : V) (C : V) +
      38 * (ctxBoundG (growK B E (C : V)) Γ (C : V) + (fvOccS LAct Γ + (C : V) * growK B E (C : V)))) := by
  obtain ⟨h1, _, _, h4, h5, _⟩ := h
  have := costSum_le_of_sizeOK 9 hE htbl hBt h1 h5
  refine le_trans this ?_
  have h38 : (3 * ((9 : ℕ) : V) + 11) = 38 := by push_cast; norm_num
  rw [h38]
  refine mul_le_mul h4 ?_ (by simp) (by simp)
  refine add_le_add (le_refl _) (mul_le_mul (le_refl _) ?_ (by simp) (by simp))
  exact add_le_add (ctxBoundG_mono h4) (add_le_add (le_refl _) (mul_le_mul h4 (le_refl _) (by simp) (by simp)))

end metaInduction

end ArithS
