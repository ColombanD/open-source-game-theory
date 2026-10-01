import ArithS.Tau.Quine
import ArithS.Agents.FitBox
import ArithS.Bridge.Neg

/-!
# ArithS.Tau.NeverFits — a `.self`-guard that freezes a budget-carrying instance never fits its budget (Phase 3b)

**The finding.** τ(CIMCIC)'s and τ(DIMCID)'s instances at a hypothesis `T` whose instance seeing them carries the
budget — `tftSim ebot obot dbot cupodTroll` (`inst T .cimcic` contains `inst cimcic coop = .search k …`, or is itself
`.search k (.eq C D) …`) — search for a guard `.impl (.plays .self (.bot X_k) a) ψ` whose antecedent names the
searcher ITSELF (`.self`). The sentence the evaluator consults therefore writes the searcher's own canonical
description, `codeTermMeta (canonical (progCode (.bot I_k)))`, whose leaf is the binary numeral of the STORED
TEMPLATE `⌜template (.impl (.plays .self (.bot X_k) a) ψ)⌝` — and that template writes `X_k` by the closed
description `cl (canonicalMeta (progCode (.bot X_k)))`, a term containing `binNumeralMeta k`, whose Cantor-pair
CODE is `≥ 2^(k+1)` (`FitBox.two_pow_succ_le_binNumeral`). So the stored template's code has more than `k` bits,
its numeral has more than `k` symbols, the guard sentence is longer than `k`, and no `TAct`-proof of length `≤ k`
exists (`formulaLenMeta_le_of_lenBoxNat`): **the guard is never found, at every budget**, and the instance plays
its ELSE branch — D for CIMCIC, C for DIMCID. This is `FitBox.box_guard_never_fits` (the budget inside a `□_k`)
one level down: the budget inside a FROZEN INSTANCE, read through a `.self` antecedent. It is also the exact
reason `Assembly/Family.family_found` cannot apply: the instance's own description is not a `binNumeral k`-tower
(`ROUTE_B_SCOPE.md` §7).

Consequences for the Phase-3 table (`SPRIME_SOURCE_OF_TRUTH.md` §3): `cimcic × tftSim` is **D** (a FLIP of the
engine's C the table does not record), and `dimcid × {tftSim, ebot, obot, dbot, cupodTroll}` are **C** — the
ENGINE's values; the base flips (`dimcid_vs_closed`) do not transfer to these tau bits, because the base
opponents (`TitForTatBot`, `EBot`, …) are budget-free while the tau hypotheses' instances are not. `coop` and
`defect` keep the table's values (their instances `inst coop dimcid`/`inst defect dimcid` are constants).

* §1 `TOccC`/`FOccC` — a CLOSED term occurs in a term/formula (the closed-term twin of `FitBox.TOcc`/`FOcc`);
  rewriters preserve it (`FOccC_rew`), negation preserves it (`FOccC_neg`), and it bounds the code
  (`le_quote_sentence_of_FOccC`: codes are monotone along the syntax tree);
* §2 `FOccC_template_plays_bot` — the template of `.plays p (.bot X) a` writes `cl (canonicalMeta …)`;
  `goodCode_template_selfBot` — hence `GoodCode` (the pair `.impl` needs) for the `.self` atom;
* §3 `HasSearchP k`/`HasSearchC k` — a program/code carries a `.search k` leaf (a path; whatever else the program
  contains, a `.sys` system included, is opaque); `binNumeral_le_codeTerm_of_hasSearchC` — its structural term is
  `≥ binNumeral k`, and so is its code-level transposition's (`revalue` keeps the leaf) and its canonical code's;
* §4 `binNumeral_le_templateCode_selfBot` — the stored template and its transposition are `≥ binNumeral k`
  (`swap` pushed through the occurrence; the canonical numeral is `swap`-fixed) — no fragment condition, so it
  applies to τ(EBot)'s instance, whose third watch is an entangled `.sys`;
* §5 `size_canonical_le_formulaLenMeta_sentenceAt_self` — a `.plays .self q a` translation writes `me`'s numeral
  (`Bridge/Neg.size_canonical_le_formulaLenMeta_sentenceAt`'s me-side twin, four `bShift`s);
* §6 `selfBot_guard_never_fits` / `selfBot_guard_not_found` — the obstruction; `cimcic_selfBot_D`,
  `dimcid_selfBot_C` — the tau slots.

**Status after route (c) made generic (Phase 2c, 2026-10-01).** The obstruction is a property of a searcher that
stores the UNABSTRACTED template `templateCode φ` with the frozen instance's budget numeral inside it. Since
2026-10-01 `progCode (.search k φ p q)` stores `templateCodeAt φ k` — the closed program's budget written as the
slot `#6`, a CONSTANT code (`Agents/CodeTermAbs.lean`, `Agents/Code.lean`) — so the engine's compiled
instances no longer have this shape and the obstruction does not apply to them. The statements below are kept as
theorems about the explicit code `pBot (pSearch k' (templateCode φ) p q)` (the pre-2026-10-01 searcher) on the
code-level sentence `sentenceAtC`; the two tau-slot corollaries carry the hypothesis `instCode k A T = pSearch k
(templateCode …) …`, which no compiled instance satisfies any more (the slots they decided — `cimcic × tftSim`,
`dimcid × {tftSim, obot, dbot, cupodTroll}` — are re-proved with the table's values in Phase 3e,
`Tau/ClosedWatch.lean`/`Tau/ClosedWatch2.lean`; `dimcid × ebot` is NOT: τ(EBot)'s instance freezes a closed SYSTEM,
which budget abstraction does not enter, and the obstruction survives one level down — `Tau/NeverFitsSys.lean`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. A closed term occurring in a formula bounds the formula's code -/

section occurs

/-- The closed term `u` occurs in the term (as `cl u`, at any arity). -/
inductive TOccC (u : ClosedSemiterm LAct 0) : {n : ℕ} → Semiterm LAct Empty n → Prop
  | here {n : ℕ} : TOccC u (cl u : Semiterm LAct Empty n)
  | func {n k : ℕ} (f : LAct.Func k) (v : Fin k → Semiterm LAct Empty n) (j : Fin k) :
      TOccC u (v j) → TOccC u (Semiterm.func f v)

/-- The closed term `u` occurs in the formula. -/
inductive FOccC (u : ClosedSemiterm LAct 0) : {n : ℕ} → Semiformula LAct Empty n → Prop
  | rel {n k : ℕ} (R : LAct.Rel k) (v : Fin k → Semiterm LAct Empty n) (j : Fin k) :
      TOccC u (v j) → FOccC u (Semiformula.rel R v)
  | nrel {n k : ℕ} (R : LAct.Rel k) (v : Fin k → Semiterm LAct Empty n) (j : Fin k) :
      TOccC u (v j) → FOccC u (Semiformula.nrel R v)
  | andL {n : ℕ} {φ : Semiformula LAct Empty n} (ψ : Semiformula LAct Empty n) : FOccC u φ → FOccC u (φ ⋏ ψ)
  | andR {n : ℕ} (φ : Semiformula LAct Empty n) {ψ : Semiformula LAct Empty n} : FOccC u ψ → FOccC u (φ ⋏ ψ)
  | orL {n : ℕ} {φ : Semiformula LAct Empty n} (ψ : Semiformula LAct Empty n) : FOccC u φ → FOccC u (φ ⋎ ψ)
  | orR {n : ℕ} (φ : Semiformula LAct Empty n) {ψ : Semiformula LAct Empty n} : FOccC u ψ → FOccC u (φ ⋎ ψ)
  | all {n : ℕ} {φ : Semiformula LAct Empty (n + 1)} : FOccC u φ → FOccC u (∀¹ φ)
  | exs {n : ℕ} {φ : Semiformula LAct Empty (n + 1)} : FOccC u φ → FOccC u (∃¹ φ)

/-- Rewriters fix closed terms, so an occurrence survives them. -/
theorem TOccC_rew {u : ClosedSemiterm LAct 0} {n : ℕ} {t : Semiterm LAct Empty n} (h : TOccC u t) :
    ∀ {m : ℕ} (ω : Rew LAct Empty n Empty m), TOccC u (ω t) := by
  induction h with
  | here => intro m ω; rw [rew_cl]; exact .here
  | func f v j _ ih => intro m ω; rw [Rew.func]; exact .func f _ j (ih ω)

theorem FOccC_rew {u : ClosedSemiterm LAct 0} {n : ℕ} {φ : Semiformula LAct Empty n} (h : FOccC u φ) :
    ∀ {m : ℕ} (ω : Rew LAct Empty n Empty m), FOccC u (ω ▹ φ) := by
  induction h with
  | rel R v j h => intro m ω; rw [Semiformula.rew_rel]; exact .rel R _ j (TOccC_rew h ω)
  | nrel R v j h => intro m ω; rw [Semiformula.rew_nrel]; exact .nrel R _ j (TOccC_rew h ω)
  | andL ψ _ ih => intro m ω; rw [LogicalConnective.HomClass.map_and]; exact .andL _ (ih ω)
  | andR φ _ ih => intro m ω; rw [LogicalConnective.HomClass.map_and]; exact .andR _ (ih ω)
  | orL ψ _ ih => intro m ω; rw [LogicalConnective.HomClass.map_or]; exact .orL _ (ih ω)
  | orR φ _ ih => intro m ω; rw [LogicalConnective.HomClass.map_or]; exact .orR _ (ih ω)
  | all _ ih => intro m ω; rw [Rewriting.app_all]; exact .all (ih ω.q)
  | exs _ ih => intro m ω; rw [Rewriting.app_exs]; exact .exs (ih ω.q)

/-- Negation (pushed through the connectives) preserves an occurrence. -/
theorem FOccC_neg {u : ClosedSemiterm LAct 0} {n : ℕ} {φ : Semiformula LAct Empty n} (h : FOccC u φ) :
    FOccC u (∼φ) := by
  induction h with
  | rel R v j h => rw [Semiformula.neg_rel]; exact .nrel R v j h
  | nrel R v j h => rw [Semiformula.neg_nrel]; exact .rel R v j h
  | andL ψ _ ih => rw [LogicalConnective.DeMorgan.and]; exact .orL _ ih
  | andR φ _ ih => rw [LogicalConnective.DeMorgan.and]; exact .orR _ ih
  | orL ψ _ ih => rw [LogicalConnective.DeMorgan.or]; exact .andL _ ih
  | orR φ _ ih => rw [LogicalConnective.DeMorgan.or]; exact .andR _ ih
  | all _ ih => rw [Semiformula.neg_all]; exact .exs ih
  | exs _ ih => rw [Semiformula.neg_ex]; exact .all ih

/-- An occurring closed term's code is below the term's code (codes are monotone along `func`). -/
theorem le_quote_emb_term {u : ClosedSemiterm LAct 0} {n : ℕ} {t : Semiterm LAct Empty n} (h : TOccC u t) :
    (⌜(Rew.emb u : SyntacticSemiterm LAct 0)⌝ : ℕ) ≤ ⌜(Rew.emb t : SyntacticSemiterm LAct n)⌝ := by
  induction h with
  | here => rw [quote_emb_cl]
  | func f v j _ ih => rw [Rew.func]; exact le_trans ih (quote_le_quote_func f (⇑Rew.emb ∘ v) j)

/-- …and below the code of any formula it occurs in. -/
theorem le_quote_emb_formula {u : ClosedSemiterm LAct 0} {n : ℕ} {φ : Semiformula LAct Empty n} (h : FOccC u φ) :
    (⌜(Rew.emb u : SyntacticSemiterm LAct 0)⌝ : ℕ) ≤ ⌜(Rewriting.emb φ : Semiproposition LAct n)⌝ := by
  induction h with
  | rel R v j h =>
    show _ ≤ ⌜(Rew.emb ▹ Semiformula.rel R v : Semiproposition LAct _)⌝
    rw [Semiformula.rew_rel, Semiformula.quote_rel]
    exact le_trans (le_quote_emb_term h)
      (le_trans (le_semitermVec_val (fun i ↦ (⌜Rew.emb (v i)⌝ : Bootstrapping.Semiterm ℕ LAct _)) j) (le_qqRel _ _ _))
  | nrel R v j h =>
    show _ ≤ ⌜(Rew.emb ▹ Semiformula.nrel R v : Semiproposition LAct _)⌝
    rw [Semiformula.rew_nrel, Semiformula.quote_nrel]
    exact le_trans (le_quote_emb_term h)
      (le_trans (le_semitermVec_val (fun i ↦ (⌜Rew.emb (v i)⌝ : Bootstrapping.Semiterm ℕ LAct _)) j) (le_qqNRel _ _ _))
  | andL ψ _ ih =>
    show _ ≤ ⌜(Rew.emb ▹ (_ ⋏ ψ) : Semiproposition LAct _)⌝
    rw [LogicalConnective.HomClass.map_and, Semiformula.quote_and]
    exact le_trans ih (le_qqAnd_left _ _)
  | andR φ _ ih =>
    show _ ≤ ⌜(Rew.emb ▹ (φ ⋏ _) : Semiproposition LAct _)⌝
    rw [LogicalConnective.HomClass.map_and, Semiformula.quote_and]
    exact le_trans ih (le_qqAnd_right _ _)
  | orL ψ _ ih =>
    show _ ≤ ⌜(Rew.emb ▹ (_ ⋎ ψ) : Semiproposition LAct _)⌝
    rw [LogicalConnective.HomClass.map_or, Semiformula.quote_or]
    exact le_trans ih (le_qqOr_left _ _)
  | orR φ _ ih =>
    show _ ≤ ⌜(Rew.emb ▹ (φ ⋎ _) : Semiproposition LAct _)⌝
    rw [LogicalConnective.HomClass.map_or, Semiformula.quote_or]
    exact le_trans ih (le_qqOr_right _ _)
  | all _ ih =>
    show _ ≤ ⌜(Rew.emb ▹ (∀¹ _) : Semiproposition LAct _)⌝
    rw [Rewriting.app_all, Rew.q_emb, Semiformula.quote_all]
    exact le_trans ih (le_qqAll _)
  | exs _ ih =>
    show _ ≤ ⌜(Rew.emb ▹ (∃¹ _) : Semiproposition LAct _)⌝
    rw [Rewriting.app_exs, Rew.q_emb, Semiformula.quote_ex]
    exact le_trans ih (le_qqExs _)

theorem le_quote_sentence_of_FOccC {u : ClosedSemiterm LAct 0} {n : ℕ} {σ : Semisentence LAct n} (h : FOccC u σ) :
    (⌜(Rew.emb u : SyntacticSemiterm LAct 0)⌝ : ℕ) ≤ (⌜σ⌝ : ℕ) := by
  rw [Sentence.quote_def]; exact le_quote_emb_formula h

end occurs

/-! ### 2. The template of `.plays p (.bot X) a` writes the canonical numeral of `.bot X` -/

section templateOcc

/-- `descF X (cl u) U W` writes `u`. -/
lemma FOccC_descF_T {n : ℕ} (X U W : Semiterm LAct Empty (n + 1)) (u : ClosedSemiterm LAct 0) :
    FOccC u (descF X (cl u) U W) := by
  unfold descF
  exact .exs (.andL _ (.rel _ _ 1 .here))

/-- The template of `.plays p (.bot X) a` writes the closed description of `.bot X`. -/
theorem FOccC_template_plays_bot (p X : PD.Prog) (a : PD.Action) :
    FOccC (canonicalMeta (progCode (.bot X))) (template (.plays p (.bot X) a)) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_of_ne (p := .bot X) (by simp) (by simp)]
  refine .exs (.exs (.exs (.andR _ (.andL _ ?_))))
  unfold closedDesc Rewriting.subst
  exact FOccC_rew (FOccC_descF_T _ _ _ _) _

/-- `GoodCode` for the `.self` atom over a frozen `X`, from a bound on the code of `X`'s canonical numeral. -/
theorem goodCode_template_selfBot (X : PD.Prog) (a : PD.Action) {c : ℕ}
    (hc : c ≤ (⌜(Rew.emb (canonicalMeta (progCode (.bot X))) : SyntacticSemiterm LAct 0)⌝ : ℕ)) :
    GoodCode c (template (.plays .self (.bot X) a)) :=
  ⟨le_trans hc (le_quote_sentence_of_FOccC (FOccC_template_plays_bot _ _ _)),
   le_trans hc (le_quote_sentence_of_FOccC (FOccC_neg (FOccC_template_plays_bot _ _ _)))⟩

end templateOcc

/-! ### 3. The numeral inside the structural term of a program with a `.search k` leaf -/

section hasSearch

/-- The program carries a `.search k` node (at the root or inside `bot`/`sim`/`ite`/`search` branches). -/
inductive HasSearchP (k : ℕ) : PD.Prog → Prop
  | search (φ : PD.Formula) (p q : PD.Prog) : HasSearchP k (.search k φ p q)
  | bot {p : PD.Prog} : HasSearchP k p → HasSearchP k (.bot p)
  | simL {p : PD.Prog} (q : PD.Prog) : HasSearchP k p → HasSearchP k (.sim p q)
  | simR (p : PD.Prog) {q : PD.Prog} : HasSearchP k q → HasSearchP k (.sim p q)
  | iteB {b : PD.Prog} (a : PD.Action) (p q : PD.Prog) : HasSearchP k b → HasSearchP k (.ite b a p q)
  | iteP (b : PD.Prog) (a : PD.Action) {p : PD.Prog} (q : PD.Prog) : HasSearchP k p → HasSearchP k (.ite b a p q)
  | iteQ (b : PD.Prog) (a : PD.Action) (p : PD.Prog) {q : PD.Prog} : HasSearchP k q → HasSearchP k (.ite b a p q)
  | searchP (k' : ℕ) (φ : PD.Formula) {p : PD.Prog} (q : PD.Prog) : HasSearchP k p → HasSearchP k (.search k' φ p q)
  | searchQ (k' : ℕ) (φ : PD.Formula) (p : PD.Prog) {q : PD.Prog} : HasSearchP k q → HasSearchP k (.search k' φ p q)

/-- The same on CODES (the path to the `pSearch k` leaf; whatever else the code contains — a `pSys`, a
`pTvote` — is opaque to it, so no fragment condition is ever needed). -/
inductive HasSearchC (k : ℕ) : ℕ → Prop
  | search (g p q : ℕ) : HasSearchC k (pSearch k g p q)
  | bot {p : ℕ} : HasSearchC k p → HasSearchC k (pBot p)
  | simL {p : ℕ} (q : ℕ) : HasSearchC k p → HasSearchC k (pSim p q)
  | simR (p : ℕ) {q : ℕ} : HasSearchC k q → HasSearchC k (pSim p q)
  | iteB {b : ℕ} (a p q : ℕ) : HasSearchC k b → HasSearchC k (pIte b a p q)
  | iteP (b a : ℕ) {p : ℕ} (q : ℕ) : HasSearchC k p → HasSearchC k (pIte b a p q)
  | iteQ (b a p : ℕ) {q : ℕ} : HasSearchC k q → HasSearchC k (pIte b a p q)
  | searchP (k' g : ℕ) {p : ℕ} (q : ℕ) : HasSearchC k p → HasSearchC k (pSearch k' g p q)
  | searchQ (k' g p : ℕ) {q : ℕ} : HasSearchC k q → HasSearchC k (pSearch k' g p q)

theorem HasSearchP.code {k : ℕ} {p : PD.Prog} (h : HasSearchP k p) : HasSearchC k (progCode p) := by
  induction h with
  | search φ p q => rw [progCode_search]; exact .search _ _ _
  | bot _ ih => rw [progCode_bot]; exact .bot ih
  | simL q _ ih => rw [progCode_sim]; exact .simL _ ih
  | simR p _ ih => rw [progCode_sim]; exact .simR _ ih
  | iteB a p q _ ih => rw [progCode_ite]; exact .iteB _ _ _ ih
  | iteP b a q _ ih => rw [progCode_ite]; exact .iteP _ _ _ ih
  | iteQ b a p _ ih => rw [progCode_ite]; exact .iteQ _ _ _ ih
  | searchP k' φ q _ ih => rw [progCode_search]; exact .searchP _ _ _ ih
  | searchQ k' φ p _ ih => rw [progCode_search]; exact .searchQ _ _ _ ih

/-- τ on codes (`revalue`) keeps the budget leaf. -/
theorem HasSearchC.revalue {k : ℕ} (u w : ℕ) {y : ℕ} (h : HasSearchC k y) : HasSearchC k (revalue u w y) := by
  induction h with
  | search g p q => rw [revalue_search]; exact .search _ _ _
  | bot _ ih => rw [revalue_bot]; exact .bot ih
  | simL q _ ih => rw [revalue_sim]; exact .simL _ ih
  | simR p _ ih => rw [revalue_sim]; exact .simR _ ih
  | iteB a p q _ ih => rw [revalue_ite]; exact .iteB _ _ _ ih
  | iteP b a q _ ih => rw [revalue_ite]; exact .iteP _ _ _ ih
  | iteQ b a p _ ih => rw [revalue_ite]; exact .iteQ _ _ _ ih
  | searchP k' g q _ ih => rw [revalue_search]; exact .searchP _ _ _ ih
  | searchQ k' g p _ ih => rw [revalue_search]; exact .searchQ _ _ _ ih

lemma le_qqAdd_right (x y : ℕ) : y ≤ x ^+ y := by
  unfold qqAdd qqFunc
  show y ≤ ⟪2, 2, addIndex, x ∷ y ∷ 0⟫ + 1
  have h1 : y ≤ x ∷ y ∷ 0 := by
    rw [adjoin_def]
    have h2 : y ≤ y ∷ 0 := by rw [adjoin_def]; have := npair_le_left y 0; omega
    have := npair_le_right x (y ∷ 0)
    omega
  exact le_trans h1 (le_trans (npair_le_right _ _)
    (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))))

lemma le_qqMul_left (x y : ℕ) : x ≤ x ^* y := by
  unfold qqMul qqFunc
  show x ≤ ⟪2, 2, mulIndex, x ∷ y ∷ 0⟫ + 1
  have h1 : x ≤ x ∷ y ∷ 0 := by
    rw [adjoin_def]
    have := npair_le_left x (y ∷ 0)
    omega
  exact le_trans h1 (le_trans (npair_le_right _ _)
    (le_trans (npair_le_right _ _) (le_trans (npair_le_right _ _) (Nat.le_succ _))))

lemma le_ppairTerm_left (s t : ℕ) : s ≤ ppairTerm s t :=
  le_trans (le_qqAdd_left s t) (le_trans (le_qqMul_left _ _) (le_qqAdd_left _ _))

lemma le_ppairTerm_right (s t : ℕ) : t ≤ ppairTerm s t := le_qqAdd_right _ _

/-- **The structural term of a code with a `pSearch k` leaf is `≥ binNumeral k`.** -/
theorem binNumeral_le_codeTerm_of_hasSearchC {k : ℕ} {y : ℕ} (h : HasSearchC k y) :
    binNumeral k ≤ codeTerm y := by
  induction h with
  | search g p q =>
    rw [codeTerm_search]
    exact le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _))
  | bot _ ih =>
    rw [codeTerm_bot]
    exact le_trans ih (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _))
  | simL q _ ih =>
    rw [codeTerm_sim]
    exact le_trans ih (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))
  | simR p _ ih =>
    rw [codeTerm_sim]
    exact le_trans ih (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))
  | iteB a p q _ ih =>
    rw [codeTerm_ite]
    exact le_trans ih (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))
  | iteP b a q _ ih =>
    rw [codeTerm_ite]
    exact le_trans ih (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _)
      (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))))
  | iteQ b a p _ ih =>
    rw [codeTerm_ite]
    exact le_trans ih (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _)
      (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))))
  | searchP k' g q _ ih =>
    rw [codeTerm_search]
    exact le_trans ih (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _)
      (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))))
  | searchQ k' g p _ ih =>
    rw [codeTerm_search]
    exact le_trans ih (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _)
      (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))))

/-- …and so is the structural term of the CANONICAL code of `.bot X` (the `min` with the transposition, which
keeps the leaf: `HasSearchC.revalue`). No fragment condition: the rest of `X` may contain `.sys` systems. -/
theorem binNumeral_le_codeTerm_canonical_bot {k : ℕ} {X : PD.Prog} (h : HasSearchP k X) :
    binNumeral k ≤ codeTerm (canonical (progCode (.bot X))) := by
  rw [progCode_bot, canonical_pBot, codeTerm_bot]
  refine le_trans ?_ (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _))
  unfold canonical
  split_ifs
  · exact binNumeral_le_codeTerm_of_hasSearchC h.code
  · exact binNumeral_le_codeTerm_of_hasSearchC (h.code.revalue 1 0)

/-- The code of the canonical numeral term of `.bot X`, as a syntactic term, is `≥ binNumeral k`. -/
theorem binNumeral_le_quote_emb_canonicalMeta_bot {k : ℕ} {X : PD.Prog} (h : HasSearchP k X) :
    binNumeral k ≤ (⌜(Rew.emb (canonicalMeta (progCode (.bot X))) : SyntacticSemiterm LAct 0)⌝ : ℕ) := by
  unfold canonicalMeta
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_codeTermMeta_nat]
  exact binNumeral_le_codeTerm_canonical_bot h

end hasSearch

/-! ### 4. The stored template of the `.self`-guard, and its transposition -/

section storedTemplate

/-- `swap` pushed through an occurrence (the occurring term becomes its swap). -/
theorem TOccC_lMap_swap {u : ClosedSemiterm LAct 0} {n : ℕ} {t : Semiterm LAct Empty n} (h : TOccC u t) :
    TOccC (Semiterm.lMap swap u) (Semiterm.lMap swap t) := by
  induction h with
  | here => rw [lMap_swap_cl]; exact .here
  | func f v j _ ih => rw [Semiterm.lMap_func]; exact .func _ _ j ih

theorem FOccC_lMap_swap {u : ClosedSemiterm LAct 0} {n : ℕ} {φ : Semiformula LAct Empty n} (h : FOccC u φ) :
    FOccC (Semiterm.lMap swap u) (Semiformula.lMap swap φ) := by
  induction h with
  | rel R v j h => rw [Semiformula.lMap_rel]; exact .rel _ _ j (TOccC_lMap_swap h)
  | nrel R v j h => rw [Semiformula.lMap_nrel]; exact .nrel _ _ j (TOccC_lMap_swap h)
  | andL ψ _ ih => rw [LogicalConnective.HomClass.map_and]; exact .andL _ ih
  | andR φ _ ih => rw [LogicalConnective.HomClass.map_and]; exact .andR _ ih
  | orL ψ _ ih => rw [LogicalConnective.HomClass.map_or]; exact .orL _ ih
  | orR φ _ ih => rw [LogicalConnective.HomClass.map_or]; exact .orR _ ih
  | all _ ih => rw [Semiformula.lMap_all]; exact .all ih
  | exs _ ih => rw [Semiformula.lMap_exs]; exact .exs ih

/-- **The stored template of a `.self`-guard over a budget-carrying `X` has code `≥ binNumeral k`, and so does its
code-level transposition** (the canonical numeral is `swap`-fixed, `lMap_swap_canonicalMeta'`). Only the
`noSelfIdx` side condition of the template-code bridge is needed. -/
theorem binNumeral_le_templateCode_selfBot {k : ℕ} {X : PD.Prog} (h : HasSearchP k X) (a : PD.Action)
    {ψ : PD.Formula} (hns : noSelfIdxF (.impl (.plays .self (.bot X) a) ψ) = true) :
    binNumeral k ≤ templateCode (.impl (.plays .self (.bot X) a) ψ) ∧
    binNumeral k ≤ revalueTemplate 1 0 (templateCode (.impl (.plays .self (.bot X) a) ψ)) := by
  have hb := binNumeral_le_quote_emb_canonicalMeta_bot h
  have hO := FOccC_template_plays_bot .self X a
  have hO' := FOccC_lMap_swap hO
  rw [lMap_swap_canonicalMeta'] at hO'
  constructor
  · rw [templateCode_eq_quote_template _ hns, template_impl]
    exact ((goodCode_template_selfBot X a hb).impl_left (template ψ)).1
  · rw [templateCode_eq_quote_template _ hns, revalueTemplate_quote_sentence, template_impl,
      LogicalConnective.HomClass.map_imply]
    have hG : GoodCode (binNumeral k) (Semiformula.lMap swap (template (.plays .self (.bot X) a))) :=
      ⟨le_trans hb (le_quote_sentence_of_FOccC hO'), le_trans hb (le_quote_sentence_of_FOccC (FOccC_neg hO'))⟩
    exact (hG.impl_left _).1

end storedTemplate

/-! ### 5. A `.plays .self q a` translation writes the description of `me` -/

section selfLength

lemma termLenMeta_emb_bShift4_canonicalMeta (x : ℕ) :
    termLenMeta (Rew.emb (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (canonicalMeta x))))) : SyntacticSemiterm LAct 4) =
    termLenMeta (Rew.emb (canonicalMeta x) : SyntacticSemiterm LAct 0) := by
  rw [emb_bShift, emb_bShift, emb_bShift, emb_bShift,
    termLenMeta_bShift_of_bvFree (bvFree_emb _).bShift.bShift.bShift,
    termLenMeta_bShift_of_bvFree (bvFree_emb _).bShift.bShift, termLenMeta_bShift_of_bvFree (bvFree_emb _).bShift,
    termLenMeta_bShift_of_bvFree (bvFree_emb _)]

/-- `sentenceAt` on CODES: the six-variable template filled with the descriptions of two codes (so that a statement
can name a searcher by its code rather than by an engine program). -/
noncomputable def sentenceAtC (me opp : ℕ) (φ : PD.Formula) : Sentence LAct :=
  template φ ⇜ descriptionTerms me opp

lemma sentenceAtC_progCode (me opp : PD.Prog) (φ : PD.Formula) :
    sentenceAtC (progCode me) (progCode opp) φ = sentenceAt me opp φ := rfl

/-- The code of `sentenceAtC` is the guard code (`quote_sentenceAt` on codes). -/
theorem quote_sentenceAtC (me opp : ℕ) (φ : PD.Formula) (h : noSelfIdxF φ = true := by noSelfIdx_tac) :
    (⌜sentenceAtC me opp φ⌝ : ℕ) = guardCode (templateCode φ) me opp := by
  rw [templateCode_eq_quote_template φ h]
  unfold sentenceAtC guardCode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descriptionTerms _ _

lemma formulaLenMeta_emb_sentenceAtC_impl (me opp : ℕ) (φ ψ : PD.Formula) :
    formulaLenMeta (Rewriting.emb (sentenceAtC me opp (.impl φ ψ)) : Proposition LAct) =
    formulaLenMeta (Rewriting.emb (sentenceAtC me opp φ) : Proposition LAct) +
      formulaLenMeta (Rewriting.emb (sentenceAtC me opp ψ) : Proposition LAct) + 1 := by
  unfold sentenceAtC
  rw [template_impl]
  simp only [Rewriting.subst, Rewriting.emb, LogicalConnective.HomClass.map_imply, formulaLenMeta_imply]

/-- **A `.self` atom writes the description of `me`**: `sentenceAtC me opp (.plays .self q a)` is longer than the
bit length of the canonical numeral of the code `me` (`Bridge/Neg.size_canonical_le_formulaLenMeta_sentenceAt`
for the me-slots: four `bShift`s, three binders plus the description's own). -/
theorem size_canonical_le_formulaLenMeta_sentenceAtC_self (me opp : ℕ) (q : PD.Prog) (a : PD.Action) :
    Nat.size (canonical me) + 1 ≤
      formulaLenMeta (Rewriting.emb (sentenceAtC me opp (.plays .self q a)) : Proposition LAct) := by
  unfold sentenceAtC
  rw [template_plays]
  unfold progGraph
  rw [progAux_self]
  simp only [Rewriting.subst, Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    rew_descF, formulaLenMeta_exs, formulaLenMeta_and]
  refine le_trans ?_ (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ 1)
    (le_trans (Nat.le_add_right _ 1) (le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ 1)))))
  refine le_trans ?_ (formulaLenMeta_emb_descF_ge _ _ _ _)
  show Nat.size (canonical me) + 1 ≤
    termLenMeta (Rew.emb (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (canonicalMeta me))))) :
      SyntacticSemiterm LAct 4) + 1
  rw [termLenMeta_emb_bShift4_canonicalMeta]
  unfold canonicalMeta
  rw [termLenMeta_emb_lMap_emb]
  exact Nat.succ_le_succ (size_le_termLenMeta_codeTermMeta _)

theorem size_canonical_le_formulaLenMeta_sentenceAt_self (me opp q : PD.Prog) (a : PD.Action) :
    Nat.size (canonical (progCode me)) + 1 ≤
      formulaLenMeta (Rewriting.emb (sentenceAt me opp (.plays .self q a)) : Proposition LAct) :=
  size_canonical_le_formulaLenMeta_sentenceAtC_self (progCode me) (progCode opp) q a

end selfLength

/-! ### 6. The obstruction, and the tau slots -/

section obstruction

/-- **The guard sentence of a `.self`-guard over a budget-carrying frozen `X`, consulted by the bot-wrapped
searcher that stores the UNABSTRACTED template, at ANY search budget, against ANY opponent code, is longer
than `k`.** -/
theorem selfBot_guard_never_fits {k : ℕ} {X : PD.Prog} (h : HasSearchP k X) (a : PD.Action) {ψ : PD.Formula}
    (hns : noSelfIdxF (.impl (.plays .self (.bot X) a) ψ) = true) (k' : ℕ) (p q opp : ℕ) :
    k < formulaLenMeta (Rewriting.emb (sentenceAtC (pBot (pSearch k' (templateCode (.impl (.plays .self (.bot X) a) ψ)) p q)) opp
      (.impl (.plays .self (.bot X) a) ψ)) : Proposition LAct) := by
  obtain ⟨h1, h2⟩ := binNumeral_le_templateCode_selfBot h a hns
  rw [formulaLenMeta_emb_sentenceAtC_impl]
  have hA := size_canonical_le_formulaLenMeta_sentenceAtC_self
    (pBot (pSearch k' (templateCode (.impl (.plays .self (.bot X) a) ψ)) p q)) opp (.bot X) a
  have hS : k + 2 ≤ Nat.size (canonical (pBot (pSearch k' (templateCode (.impl (.plays .self (.bot X) a) ψ)) p q))) := by
    rw [canonical_pBot]
    refine le_trans (size_binNumeral_ge k) (Nat.size_le_size ?_)
    refine le_trans ?_ (by unfold pBot; exact le_trans (nppair_le_right _ _) (Nat.le_succ _))
    unfold canonical
    split_ifs
    · exact le_trans h1 (le_pSearch _ _ _ _)
    · rw [transposeCode, revalue_search]; exact le_trans h2 (le_pSearch _ _ _ _)
  omega

/-- **Hence it is never found within `k`** (a `TAct`-proof is at least as long as its conclusion). -/
theorem selfBot_guard_not_found {k : ℕ} {X : PD.Prog} (h : HasSearchP k X) (a : PD.Action) {ψ : PD.Formula}
    (hns : noSelfIdxF (.impl (.plays .self (.bot X) a) ψ) = true) (k' : ℕ) (p q opp : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot X) a) ψ))
      (pBot (pSearch k' (templateCode (.impl (.plays .self (.bot X) a) ψ)) p q)) opp) := by
  intro hl
  rw [← quote_sentenceAtC _ _ _ hns, lenBox_nat] at hl
  have hle := formulaLenMeta_le_of_lenBoxNat hl
  have hlt := selfBot_guard_never_fits h a hns k' p q opp
  exact absurd (lt_of_lt_of_le hlt hle) (_root_.lt_irrefl _)

/-- **τ(CIMCIC) at a hypothesis whose instance seeing it carries the budget: D** — IF the instance stored the
unabstracted template (`hc`; no compiled instance does since 2026-10-01). -/
theorem cimcic_selfBot_D {k : ℕ} {T : Tmpl}
    (hc : instCode k .cimcic T = pSearch k (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) T .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) T .cimcic)) .self .C))) (pConst 0) (pConst 1))
    (h : HasSearchP k (inst (tauZoo k) T .cimcic))
    (hns : noSelfIdxF (.impl (.plays .self (.bot (inst (tauZoo k) T .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) T .cimcic)) .self .C)) = true) :
    bitPlays k .cimcic T .D := by
  have hn := selfBot_guard_not_found h .C hns k (pConst 0) (pConst 1) (pBot (instCode k .cimcic T))
  rw [hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else _ hn (const_play 0 _ _ _) hns⟩

/-- **τ(DIMCID) at a hypothesis whose instance seeing it carries the budget: C** — IF the instance stored the
unabstracted template (`hc`; no compiled instance does since 2026-10-01). -/
theorem dimcid_selfBot_C {k : ℕ} {T : Tmpl}
    (hc : instCode k .dimcid T = pSearch k (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) .C)
      (.plays (.bot (inst (tauZoo k) T .dimcid)) .self .D))) (pConst 1) (pConst 0))
    (h : HasSearchP k (inst (tauZoo k) T .dimcid))
    (hns : noSelfIdxF (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) .C)
      (.plays (.bot (inst (tauZoo k) T .dimcid)) .self .D)) = true) :
    bitPlays k .dimcid T .C := by
  have hn := selfBot_guard_not_found h .C hns k (pConst 1) (pConst 0) (pBot (instCode k .dimcid T))
  rw [hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else _ hn (const_play 0 _ _ _) hns⟩

end obstruction

end ArithS.Tau
