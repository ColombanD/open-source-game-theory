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

end ArithS
