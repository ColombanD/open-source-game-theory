I have everything needed. Final report follows.

# ArithS package inventory (branch `colomban-arith-s`, `arith/`)

Root: `/Users/colomband/Library/CloudStorage/OneDrive-Personal/Documents/Studies/ETH/Master Thesis/workspace/open-source-game-theory/arith/`. Lakefile pins Foundation `rev = "58c76ac8b26cfda45d0d5430511750489d39b25a"`, single `lean_lib` `ArithS`, `defaultTargets = ["ArithS"]`. `.lake` is a symlink to `/Users/colomband/wt/arith-lake`.

## Import order (`arith/ArithS.lean`, 19 lines, verbatim)

```
import ArithS.Basic
import ArithS.Length
import ArithS.SequentLength
import ArithS.DerivationLength
import ArithS.Bew
import ArithS.MetaLength
import ArithS.Proper
import ArithS.LangAct
import ArithS.TheoryAct
import ArithS.Transpose
import ArithS.Sound
import ArithS.Symmetry
import ArithS.Prog
import ArithS.BewV
import ArithS.Guard
import ArithS.Eval
import ArithS.EvalN
import ArithS.Template
import ArithS.RedCell
```

Actual per-file import DAG (from each file's own `import` lines): Basic←Foundation; Length←Foundation; SequentLength←Length; DerivationLength←SequentLength; Bew←DerivationLength; MetaLength←Bew+Mathlib.BigOperators.Fin; LangAct←MetaLength; Proper←MetaLength+LangAct+Mathlib Ring/Linarith/Positivity; TheoryAct←LangAct+Foundation Incompleteness.Definability+Mathlib FinCases; Transpose←TheoryAct; Sound←MetaLength; Symmetry←Transpose+Sound+Proper; Prog←Symmetry; BewV←Proper; Guard←Prog+BewV; Eval←Guard; EvalN←Eval; Template←EvalN+Guard+Symmetry; RedCell←Template.

## `sorry` / `axiom` census

`grep -n -E "sorry|axiom|admit|native_decide" ArithS/*.lean ArithS.lean` — the only hits are the word "axiom(s)" in doc-comments (Transpose.lean:7,25; LangAct.lean:9; TheoryAct.lean:9,11,14,123,145,235). **Zero `sorry`, zero `axiom` declarations, zero `native_decide`.** Every declaration below is proved.

---

## 1. `ArithS/Basic.lean` (13 lines)

- L1 `import Foundation.FirstOrder.Incompleteness.RestrictedProvability`
- L10 `open FFL.FirstOrder`
- L12 `#check @Theory.RestrictedProvable`
- L13 `#check @Arithmetic.lower_bound_gödelNumber_proof_restrictedGödel`

No declarations (smoke test, M0).

## 2. `ArithS/Length.lean` (238 lines) — `namespace ArithS`

- L25 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`
- L27 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`

`namespace ListSum` (L31–43):
- L33 `def blueprint : VecRec.Blueprint 0 where nil := .mkSigma “y. y = 0”; adjoin := .mkSigma “y x xs ih. y = x + ih”`
- L37 `noncomputable def construction : VecRec.Construction V blueprint where nil _ := 0; adjoin _ x _ ih := x + ih; …`

- L45 `noncomputable def listSum (v : V) : V := ListSum.construction.result ![] v`
- L47 `@[simp] lemma listSum_nil : listSum (0 : V) = 0`
- L49 `@[simp] lemma listSum_adjoin (x v : V) : listSum (x ∷ v) = x + listSum v`
- L52 `def listSumDef : 𝚺₁.Semisentence 2 := ListSum.blueprint.resultDef`
- L54 `instance listSum_defined : 𝚺₁-Function₁ (listSum : V → V) via listSumDef`
- L57 `instance listSum_definable : 𝚺₁-Function₁ (listSum : V → V)`
- L59 `instance listSum_definable' (Γ m) : Γ-[m + 1]-Function₁ (listSum : V → V)`

`section term` L64–137, `variable {L : Language} [L.Encodable] [L.LORDefinable]`:
`namespace TermLen`:
- L70 `def blueprint : Language.TermRec.Blueprint 0 where bvar := .mkSigma “y z. y = z + 1”; fvar := .mkSigma “y x. y = x + 1”; func := .mkSigma “y k f v v'. ∃ s, !listSumDef s v' ∧ y = s + 1”`
- L75 `noncomputable def construction : Language.TermRec.Construction V blueprint where bvar (_ z) := z + 1; fvar (_ x) := x + 1; func (_ _ _ _ v') := listSum v' + 1; …`
- L85 `open TermLen`; L87 `variable (L)`
- L90 `noncomputable def termLen (t : V) : V := construction.result L ![] t` — doc: symbol counts 1, variable index `i` counts `i + 1`
- L92 `noncomputable def termLenVec (k v : V) : V := construction.resultVec L ![] k v`
- L94 `noncomputable def termLenGraph : 𝚺₁.Semisentence 2 := blueprint.result L`
- L96 `noncomputable def termLenVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L`
- L100 `@[simp] lemma termLen_bvar (z : V) : termLen L ^#z = z + 1`
- L102 `@[simp] lemma termLen_fvar (x : V) : termLen L ^&x = x + 1`
- L104 `@[simp] lemma termLen_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) : termLen L (^func k f v) = listSum (termLenVec L k v) + 1`
- L108 `@[simp] lemma len_termLenVec {k v : V} (hv : IsUTermVec L k v) : len (termLenVec L k v) = k`
- L111 `@[simp] lemma nth_termLenVec {k v : V} (hv : IsUTermVec L k v) {i} (hi : i < k) : (termLenVec L k v).[i] = termLen L v.[i]`
- L114 `@[simp] lemma termLenVec_nil : termLenVec L (0 : V) 0 = 0`
- L116 `lemma termLenVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) : termLenVec L (k + 1) (t ∷ ts) = termLen L t ∷ termLenVec L k ts`
- L120 `instance termLen.defined : 𝚺₁-Function₁ (termLen (V := V) L) via (termLenGraph L)`
- L123 `instance termLen.definable : 𝚺₁-Function₁ (termLen (V := V) L)`
- L125 `instance termLen.definable' : Γ-[k + 1]-Function₁ (termLen (V := V) L)`
- L128 `instance termLenVec.defined : 𝚺₁-Function₂ (termLenVec (V := V) L) via (termLenVecGraph L)`
- L131 `instance termLenVec.definable : 𝚺₁-Function₂ (termLenVec (V := V) L)`
- L134 `instance termLenVec.definable' : Γ-[i + 1]-Function₂ (termLenVec (V := V) L)`

`section formula` L141–236:
`namespace FormulaLen` (L145–183): L149 `noncomputable def blueprint : UformulaRec1.Blueprint` with `rel/nrel := .mkSigma “y param k R v. ∃ M, !(termLenVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s + 1”`, `verum/falsum := “y param. y = 1”`, `and/or := “y param p₁ p₂ y₁ y₂. y = y₁ + y₂ + 1”`, `all/exs := “y param p₁ y₁. y = y₁ + 1”`, `allChanges/exsChanges := “param' param. param' = 0”`; L176 `noncomputable def construction : UformulaRec1.Construction V (blueprint L)` (matching clauses).
- L190 `noncomputable def formulaLen (p : V) : V := (FormulaLen.construction L).result L 0 p`
- L192 `noncomputable def formulaLenGraph : 𝚺₁.Semisentence 2 := ((FormulaLen.blueprint L).result L).rew (Rew.subst ![#0, ‘0’, #1])`
- L197 `instance formulaLen.defined : 𝚺₁-Function₁ formulaLen (V := V) L via formulaLenGraph L`
- L201 `instance formulaLen.definable : 𝚺₁-Function₁ formulaLen (V := V) L`
- L203 `instance formulaLen.definable' : Γ-[m + 1]-Function₁ formulaLen (V := V) L`
- L206 `@[simp] lemma formulaLen_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) : formulaLen L (^rel k R v) = listSum (termLenVec L k v) + 1`
- L210 `@[simp] lemma formulaLen_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) : formulaLen L (^nrel k R v) = listSum (termLenVec L k v) + 1`
- L214 `@[simp] lemma formulaLen_verum : formulaLen L (^⊤ : V) = 1`
- L217 `@[simp] lemma formulaLen_falsum : formulaLen L (^⊥ : V) = 1`
- L220 `@[simp] lemma formulaLen_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) : formulaLen L (p ^⋏ q) = formulaLen L p + formulaLen L q + 1`
- L224 `@[simp] lemma formulaLen_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) : formulaLen L (p ^⋎ q) = formulaLen L p + formulaLen L q + 1`
- L228 `@[simp] lemma formulaLen_all {p : V} (hp : IsUFormula L p) : formulaLen L (^∀ p) = formulaLen L p + 1`
- L232 `@[simp] lemma formulaLen_exs {p : V} (hp : IsUFormula L p) : formulaLen L (^∃ p) = formulaLen L p + 1`

## 3. `ArithS/SequentLength.lean` (103 lines) — `namespace ArithS`

- L14 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L15 `open Classical`
- L17 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`; L18 `variable {L : Language} [L.Encodable] [L.LORDefinable]`

`namespace SetLen`:
- L25 `noncomputable def blueprint : PR.Blueprint 1 where zero := .mkSigma “y s. y = 0”; succ := .mkSigma “y ih i s. (i ∈ s → ∃ l, !(formulaLenGraph L) l i ∧ y = ih + l) ∧ (¬i ∈ s → y = ih)”`
- L29 `noncomputable def construction : PR.Construction V (blueprint L) where zero := fun _ ↦ 0; succ := fun v i ih ↦ if i ∈ v 0 then ih + formulaLen L i else ih; …`

- L47 `noncomputable def setLenAux (s i : V) : V := (SetLen.construction L).result ![s] i` — partial sum `Σ_{p ∈ s, p < i} formulaLen p`
- L50 `noncomputable def setLen (s : V) : V := setLenAux L s s` — `Σ_{p ∈ s} formulaLen p`
- L54 `@[simp] lemma setLenAux_zero (s : V) : setLenAux L s 0 = 0`
- L57 `lemma setLenAux_succ (s i : V) : setLenAux L s (i + 1) = if i ∈ s then setLenAux L s i + formulaLen L i else setLenAux L s i`
- L61 `@[simp] lemma setLenAux_succ_of_mem {s i : V} (h : i ∈ s) : setLenAux L s (i + 1) = setLenAux L s i + formulaLen L i`
- L64 `@[simp] lemma setLenAux_succ_of_not_mem {s i : V} (h : i ∉ s) : setLenAux L s (i + 1) = setLenAux L s i`
- L71 `noncomputable def setLenAuxDef : 𝚺₁.Semisentence 3 := (SetLen.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])`
- L76 `instance setLenAux_defined : 𝚺₁-Function₂[V] setLenAux L via setLenAuxDef L`
- L79 `instance setLenAux_definable : 𝚺₁-Function₂[V] setLenAux L`
- L81 `instance setLenAux_definable' (Γ m) : Γ-[m + 1]-Function₂ (setLenAux (V := V) L)`
- L89 `noncomputable def setLenDef : 𝚺₁.Semisentence 2 := (setLenAuxDef L).rew (Rew.subst ![#0, #1, #1])` — doc warns: NOT a `“ ”`-DSL wrapper (simp on the wrapper form runs away, 17 GB)
- L93 `instance setLen_defined : 𝚺₁-Function₁[V] setLen L via setLenDef L`
- L96 `instance setLen_definable : 𝚺₁-Function₁[V] setLen L`
- L98 `instance setLen_definable' (Γ m) : Γ-[m + 1]-Function₁ (setLen (V := V) L)`

## 4. `ArithS/DerivationLength.lean` (420 lines) — `namespace ArithS`

- L21 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L22 `open PeanoMinus ISigma0 ISigma1`
- L24 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`; L25 `variable {L : Language} [L.Encodable] [L.LORDefinable]`

`namespace DLen`:
- L32 `def Phi (C : Set V) (pr : V) : Prop :=` (verbatim, ten arms)
  ```
  (∃ s p, pr = ⟪axL s p, setLen L s + 1⟫) ∨
  (∃ s, pr = ⟪verumIntro s, setLen L s + 1⟫) ∨
  (∃ s p q dp dq np nq, ⟪dp, np⟫ ∈ C ∧ ⟪dq, nq⟫ ∈ C ∧ pr = ⟪andIntro s p q dp dq, setLen L s + np + nq + 1⟫) ∨
  (∃ s p q d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪orIntro s p q d, setLen L s + n' + 1⟫) ∨
  (∃ s p d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪allIntro s p d, setLen L s + n' + 1⟫) ∨
  (∃ s p t d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪exsIntro s p t d, setLen L s + termLen L t + n' + 1⟫) ∨
  (∃ s d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪wkRule s d, setLen L s + n' + 1⟫) ∨
  (∃ s d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪shiftRule s d, setLen L s + n' + 1⟫) ∨
  (∃ s p d₁ d₂ n₁ n₂, ⟪d₁, n₁⟫ ∈ C ∧ ⟪d₂, n₂⟫ ∈ C ∧ pr = ⟪cutRule s p d₁ d₂, setLen L s + n₁ + n₂ + 1⟫) ∨
  (∃ s p, pr = ⟪axm s p, setLen L s + 1⟫)
  ```
- L46 `noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta (.mkSigma “pr C. ∃ d <⁺ pr, ∃ n <⁺ pr, !pairDef pr d n ∧ (…ten arms using !axLGraph/!verumIntroGraph/!andIntroGraph/!orIntroGraph/!allIntroGraph/!exsIntroGraph/!wkRuleGraph/!shiftRuleGraph/!cutRuleGraph/!axmGraph, !(setLenDef L), !(termLenGraph L), :⟪·,·⟫:∈ C…)”) (.mkPi “…same with ∀ l, !(setLenDef L) l s → …”)⟩` (L46–90)
- L94–97 `private lemma le_sum₀ (a b : V) : b ≤ a + b + 1`; `le_sum₁ (a b c : V) : b ≤ a + b + c + 1`; `le_sum₂ (a b c : V) : c ≤ a + b + c + 1`
- L100 `private lemma phi_iff (C pr : V) : Phi L {x | x ∈ C} pr ↔ ∃ d ≤ pr, ∃ n ≤ pr, pr = ⟪d, n⟫ ∧ (…bounded form of the ten arms…)`
- L163 `noncomputable def construction : Fixpoint.Construction V (blueprint L) where Φ := fun _ ↦ Phi L; defined := …; monotone := …`
- L189 `instance : (construction L).StrongFinite V`

- L219 `def DlenGraph (d n : V) : Prop := (DLen.construction L).Fixpoint ![] ⟪d, n⟫`
- L221 `noncomputable def dlenGraphDef : 𝚫₁.Semisentence 2 := .mkDelta (.mkSigma “d n. ∃ pr <⁺ (d + n + 1)², !pairDef pr d n ∧ !(DLen.blueprint L).fixpointDefΔ₁.sigma pr”) (.mkPi “d n. ∀ pr <⁺ (d + n + 1)², !pairDef pr d n → !(DLen.blueprint L).fixpointDefΔ₁.pi pr”)`
- L229 `private lemma fixpoint_param_eq (p : Fin 0 → V) (x : V) : (DLen.construction L).Fixpoint p x = (DLen.construction L).Fixpoint ![] x`
- L233 `instance dlenGraph_defined : 𝚫₁-Relation[V] DlenGraph L via dlenGraphDef L`
- L245 `instance dlenGraph_definable : 𝚫₁-Relation[V] DlenGraph L`
- L247 `instance dlenGraph_definable' : Γ-[m + 1]-Relation[V] DlenGraph L`
- L253 `lemma DlenGraph.case_iff {d n : V} : DlenGraph L d n ↔ (∃ s p, d = axL s p ∧ n = setLen L s + 1) ∨ (∃ s, d = verumIntro s ∧ n = setLen L s + 1) ∨ (∃ s p q dp dq np nq, DlenGraph L dp np ∧ DlenGraph L dq nq ∧ d = andIntro s p q dp dq ∧ n = setLen L s + np + nq + 1) ∨ (∃ s p q d' n', DlenGraph L d' n' ∧ d = orIntro s p q d' ∧ n = setLen L s + n' + 1) ∨ (∃ s p d' n', DlenGraph L d' n' ∧ d = allIntro s p d' ∧ n = setLen L s + n' + 1) ∨ (∃ s p t d' n', DlenGraph L d' n' ∧ d = exsIntro s p t d' ∧ n = setLen L s + termLen L t + n' + 1) ∨ (∃ s d' n', DlenGraph L d' n' ∧ d = wkRule s d' ∧ n = setLen L s + n' + 1) ∨ (∃ s d' n', DlenGraph L d' n' ∧ d = shiftRule s d' ∧ n = setLen L s + n' + 1) ∨ (∃ s p d₁ d₂ n₁ n₂, DlenGraph L d₁ n₁ ∧ DlenGraph L d₂ n₂ ∧ d = cutRule s p d₁ d₂ ∧ n = setLen L s + n₁ + n₂ + 1) ∨ (∃ s p, d = axm s p ∧ n = setLen L s + 1)`
- L272 `attribute [local simp] axL verumIntro andIntro orIntro allIntro exsIntro wkRule shiftRule cutRule axm` (section inversion)
- L274 `lemma DlenGraph.axL_iff {s p n : V} : DlenGraph L (axL s p) n ↔ n = setLen L s + 1`
- L277 `lemma DlenGraph.verumIntro_iff {s n : V} : DlenGraph L (verumIntro s) n ↔ n = setLen L s + 1`
- L280 `lemma DlenGraph.axm_iff {s p n : V} : DlenGraph L (axm s p) n ↔ n = setLen L s + 1`
- L283 `lemma DlenGraph.andIntro_iff {s p q dp dq n : V} : DlenGraph L (andIntro s p q dp dq) n ↔ ∃ np nq, DlenGraph L dp np ∧ DlenGraph L dq nq ∧ n = setLen L s + np + nq + 1`
- L288 `lemma DlenGraph.orIntro_iff {s p q d' n : V} : DlenGraph L (orIntro s p q d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1`
- L292 `lemma DlenGraph.allIntro_iff {s p d' n : V} : DlenGraph L (allIntro s p d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1`
- L296 `lemma DlenGraph.exsIntro_iff {s p t d' n : V} : DlenGraph L (exsIntro s p t d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + termLen L t + n' + 1`
- L301 `lemma DlenGraph.wkRule_iff {s d' n : V} : DlenGraph L (wkRule s d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1`
- L305 `lemma DlenGraph.shiftRule_iff {s d' n : V} : DlenGraph L (shiftRule s d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1`
- L309 `lemma DlenGraph.cutRule_iff {s p d₁ d₂ n : V} : DlenGraph L (cutRule s p d₁ d₂) n ↔ ∃ n₁ n₂, DlenGraph L d₁ n₁ ∧ DlenGraph L d₂ n₂ ∧ n = setLen L s + n₁ + n₂ + 1`
- L320 `variable {T : Theory L} [T.Δ₁]`
- L322 `lemma dlenGraph_exists {d : V} (hd : Derivation T d) : ∃ n, DlenGraph L d n` (via `Derivation.induction1 𝚺`)
- L337 `lemma dlenGraph_unique {d : V} (hd : Derivation T d) : ∀ n₁ n₂, DlenGraph L d n₁ → DlenGraph L d n₂ → n₁ = n₂` (via `Derivation.induction1 𝚷`)
- L376 `lemma dlenGraph_existsUnique {d : V} (hd : Derivation T d) : ∃! n, DlenGraph L d n`
- L382 `lemma dlenGraph_existsUnique_total (d : V) : ∃! n, (Derivation T d → DlenGraph L d n) ∧ (¬Derivation T d → n = 0)` (explicit `(T)`)
- L389 `noncomputable def dlen (d : V) : V := Classical.choose! (dlenGraph_existsUnique_total (L := L) T d)` (explicit `(T)`; `0` on non-derivations)
- L393 `theorem dlen_graph {d : V} (hd : Derivation T d) : DlenGraph L d (dlen T d)`
- L396 `theorem dlen_of_not {d : V} (hd : ¬Derivation T d) : dlen T d = 0`
- L399 `lemma dlen_eq_of_graph {d n : V} (hd : Derivation T d) (h : DlenGraph L d n) : dlen T d = n`
- L404 `noncomputable def dlenDef : 𝚺₁.Semisentence 2 := .mkSigma “n d. (!(derivation T).pi d → !(dlenGraphDef L).sigma d n) ∧ (¬!(derivation T).sigma d → n = 0)”` (explicit `(T)`)
- L409 `instance dlen_defined : 𝚺₁-Function₁[V] dlen (L := L) T via dlenDef T`
- L414 `instance dlen_definable : 𝚺₁-Function₁[V] dlen (L := L) T`
- L416 `instance dlen_definable' : Γ-[m + 1]-Function₁[V] dlen (L := L) T`

## 5. `ArithS/Bew.lean` (179 lines)

`namespace ArithS` (L25–83): L27 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L28 `open PeanoMinus ISigma0 ISigma1`; L30 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`; L31 `variable {L : Language} [L.Encodable] [L.LORDefinable]`; L32 `variable {T : Theory L} [T.Δ₁]`.

- L35 `def LenProvable (f : V → V) (k : ℕ) (T : Theory L) [T.Δ₁] (φ : V) : Prop := ∃ d < f (ORingStructure.numeral k), Proof T d φ ∧ dlen T d ≤ ORingStructure.numeral k`
- L40 `noncomputable def lenProvable (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !fDef E !k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(dlenDef T) n d → n ≤ !k”` (explicit `(T)`)
- L44 `noncomputable abbrev lenProvabilityPred (fDef : 𝚺₁.Semisentence 2) (k : ℕ) (σ : Sentence L) : ArithmeticSentence := (lenProvable T fDef k).val/[⌜σ⌝]` (explicit `(T)`)
- L49 `instance LenProvable.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {k} : 𝚷₁-Predicate[V] (LenProvable f k T) via (lenProvable T fDef k)`
- L53 `lemma LenProvable.mono {f : V → V} (hf : Monotone f) {k k' : ℕ} (h : k ≤ k') {φ : V} : LenProvable f k T φ → LenProvable f k' T φ`
- L60 `lemma LenProvable.provable {f : V → V} {k : ℕ} {φ : V} : LenProvable f k T φ → Provable T φ`
- L70 `noncomputable abbrev lenGödel (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : ArithmeticSentence := fixedpoint (∼(lenProvable T fDef k))` (explicit `(T)`)
- L73 `private noncomputable abbrev lenGödel' (fDef : 𝚺₁.Semisentence 2) (k : ℕ) : ArithmeticSentence := ∼(lenProvable T fDef k).val/[⌜lenGödel T fDef k⌝]`
- L78 `private lemma lenGödel'_sigmaOne {fDef : 𝚺₁.Semisentence 2} {k : ℕ} : Hierarchy 𝚺 1 (lenGödel' T fDef k)`

`namespace ArithS.Arithmetic` (L85–179): L87 `open FFL FFL.FirstOrder Arithmetic Bootstrapping ArithS`; L88 `open PeanoMinus ISigma0 ISigma1`; L90 `variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`; L91 `variable {T U : ArithmeticTheory} [T.Δ₁]`; L92 `variable {fDef : 𝚺₁.Semisentence 2} {k : ℕ}`.
- L94 `lemma def_lenGödel [𝗜𝚺₁ ⪯ U] : U ⊢ lenGödel T fDef k 🡘 (∼(lenProvable T fDef k).val)/[⌜lenGödel T fDef k⌝]`
- L97 `private lemma def_lenGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ lenGödel' T fDef k 🡘 (∼(lenProvable T fDef k).val)/[⌜lenGödel T fDef k⌝]`
- L100 `private lemma provable_E_lenGödel_lenGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ lenGödel T fDef k 🡘 lenGödel' T fDef k`
- L105 `private lemma iff_provable_lenGödel_provable_lenGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ lenGödel T fDef k ↔ U ⊢ lenGödel' T fDef k`
- L109 `private lemma iff_true_lenGödel_true_lenGödel' : ℕ↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔ ℕ↓[ℒₒᵣ] ⊧ lenGödel' T fDef k`
- L115 `lemma models_lenGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] : V↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔ ∀ x : V, x < f (ORingStructure.numeral k) → ¬(Proof T x (⌜lenGödel T fDef k⌝) ∧ dlen T x ≤ ORingStructure.numeral k)`
- L122 `private lemma models_neg_lenGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] : ¬V↓[ℒₒᵣ] ⊧ lenGödel T fDef k ↔ ∃ x : V, x < f (ORingStructure.numeral k) ∧ Proof T x (⌜lenGödel T fDef k⌝) ∧ dlen T x ≤ ORingStructure.numeral k`
- L128 `variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`
- L131 `theorem true_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ℕ↓[ℒₒᵣ] ⊧ lenGödel T fDef k`
- L142 `theorem provable_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : T ⊢ lenGödel T fDef k`
- L148 `theorem lower_bound_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ∀ b : T ⊢! lenGödel T fDef k, f k ≤ ⌜b⌝ ∨ k < dlen T (⌜b⌝ : ℕ)`
- L164 `def Proper (f : ℕ → ℕ) (k : ℕ) (T : ArithmeticTheory) [T.Δ₁] : Prop := ∀ b : T ⊢! lenGödel T fDef k, dlen T (⌜b⌝ : ℕ) ≤ k → ⌜b⌝ < f k` (implicit `{fDef}` from the section variable)
- L170 `theorem lower_bound_dlen_proof_lenGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] (hf : Proper (fDef := fDef) f k T) : ∀ b : T ⊢! lenGödel T fDef k, k < dlen T (⌜b⌝ : ℕ)` — "the M1 gate"

## 6. `ArithS/MetaLength.lean` (253 lines) — `namespace ArithS`

- L17 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L18 `open PeanoMinus ISigma0 ISigma1`
- L20 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`; L21 `variable {L : Language} [L.Encodable] [L.LORDefinable]`
- L27 `def tlen {n : ℕ} : SyntacticSemiterm L n → ℕ | #x => x + 1 | &x => x + 1 | FirstOrder.Semiterm.func _ v => (∑ i, tlen (v i)) + 1`
- L32 `@[simp] lemma tlen_bvar {n : ℕ} (x : Fin n) : tlen (#x : SyntacticSemiterm L n) = x + 1`
- L34 `@[simp] lemma tlen_fvar {n : ℕ} (x : ℕ) : tlen (&x : SyntacticSemiterm L n) = x + 1`
- L36 `@[simp] lemma tlen_func {n k : ℕ} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) : tlen (FirstOrder.Semiterm.func f v) = (∑ i, tlen (v i)) + 1`
- L39 `lemma listSum_termLenVec {k n : ℕ} (w : SemitermVec V L k n) : listSum (termLenVec L ↑k w.val) = ∑ i, termLen L (w i).val`
- L51 `theorem termLen_quote {n : ℕ} (t : SyntacticSemiterm L n) : termLen L (⌜t⌝ : V) = ↑(tlen t)`
- L66 `def flen {n : ℕ} : Semiproposition L n → ℕ | .rel _ v => (∑ i, tlen (v i)) + 1 | .nrel _ v => (∑ i, tlen (v i)) + 1 | .verum => 1 | .falsum => 1 | .and φ ψ => flen φ + flen ψ + 1 | .or φ ψ => flen φ + flen ψ + 1 | .all φ => flen φ + 1 | .exs φ => flen φ + 1`
- L76 `theorem formulaLen_quote {n : ℕ} (φ : Semiproposition L n) : formulaLen L (⌜φ⌝ : V) = ↑(flen φ)`

`section sequent` (L114–170): L116 `variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`; L118 `open Classical`. (All at `V = ℕ`.)
- L121 `lemma setLenAux_eq_of_le {s i : ℕ} (h : s ≤ i) : setLenAux L s i = setLen L s`
- L133 `lemma setLenAux_insert_of_not_mem {x s : ℕ} (hx : x ∉ s) (i : ℕ) : setLenAux L (insert x s) i = setLenAux L s i + (if x < i then formulaLen L x else 0)`
- L151 `lemma setLen_insert_of_not_mem {x s : ℕ} (hx : x ∉ s) : setLen L (insert x s) = setLen L s + formulaLen L x`
- L161 `theorem setLen_quote (Γ : Finset (Proposition L)) : setLen L (⌜Γ⌝ : ℕ) = ∑ φ ∈ Γ, flen φ`

`section derivation` (L174–251): L176 `variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`; L177 `variable {T : Theory L} [T.Δ₁]`.
- L180 `abbrev sqlen (Γ : Finset (Proposition L)) : ℕ := ∑ φ ∈ Γ, flen φ`
- L184 `def mlen : {Γ : Finset (Proposition L)} → T ⟹₂ Γ → ℕ | Γ, .closed _ _ _ _ => sqlen Γ + 1 | Γ, .axm _ _ _ => sqlen Γ + 1 | Γ, .verum _ => sqlen Γ + 1 | Γ, .and _ d₁ d₂ => sqlen Γ + mlen d₁ + mlen d₂ + 1 | Γ, .or _ d => sqlen Γ + mlen d + 1 | Γ, .all _ d => sqlen Γ + mlen d + 1 | Γ, .exs _ t d => sqlen Γ + tlen t + mlen d + 1 | Γ, .wk d _ => sqlen Γ + mlen d + 1 | _, .shift (Γ := Γ) d => sqlen (Γ.image Rewriting.shift) + mlen d + 1 | Γ, .cut d₁ d₂ => sqlen Γ + mlen d₁ + mlen d₂ + 1`
- L197 `lemma derivation_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivation T (⌜d⌝ : ℕ)`
- L201 `theorem dlen_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : dlen T (⌜d⌝ : ℕ) = mlen d` — "the bridge"

## 7. `ArithS/Proper.lean` (646 lines) — `namespace ArithS`

- L24 `open FFL FFL.FirstOrder Arithmetic Bootstrapping` (no `variable V` at top; sections introduce their own).
- L28 `def E (s : ℕ) : ℕ := 2 ^ (2 ^ s)`
- L29 `def F (s : ℕ) : ℕ := 2 ^ (2 ^ (2 ^ s))`
- L31 `lemma E_pos (s : ℕ) : 0 < E s`; L32 `lemma two_le_E (s : ℕ) : 2 ≤ E s`; L36 `lemma E_mono {s t : ℕ} (h : s ≤ t) : E s ≤ E t`; L38 `lemma E_add_two (s : ℕ) : E (s + 2) = E s ^ 4`; L40 `lemma le_E (s : ℕ) : s ≤ E s`
- L44 `lemma F_pos (s : ℕ) : 0 < F s`; L45 `lemma two_le_F (s : ℕ) : 2 ≤ F s`; L49 `lemma F_mono {s t : ℕ} (h : s ≤ t) : F s ≤ F t`; L52 `lemma E_le_F (s : ℕ) : E s ≤ F s`; L54 `lemma F_add_two (s : ℕ) : F s ^ 4 ≤ F (s + 2)`
- L63 `private lemma sq_succ_succ_le_pow_four {x : ℕ} (hx : 2 ≤ x) : (x + 1) ^ 2 + 1 ≤ x ^ 4`
- L67 `lemma pair_E {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : Nat.pair a b + 1 ≤ E (s + 2)`
- L77 `lemma pair_F {a b s : ℕ} (ha : a ≤ F s) (hb : b ≤ F s) : Nat.pair a b + 1 ≤ F (s + 2)`
- L87 `lemma two_pow_E_succ_le_F (s : ℕ) : 2 ^ (E s + 1) ≤ F (s + 1)`
- `section terms` L98–126, `variable {L : Language} [L.Encodable] [L.LORDefinable]`:
  - L103 `lemma nat_pair_eq' (a b : ℕ) : (⟪a, b⟫ : ℕ) = Nat.pair a b`
  - L105 `lemma pair_E' {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : (⟪a, b⟫ : ℕ) + 1 ≤ E (s + 2)`
  - L108 `lemma pair_E_le {a b s : ℕ} (ha : a ≤ E s) (hb : b ≤ E s) : (⟪a, b⟫ : ℕ) ≤ E (s + 2)`
  - L112 `lemma vec_E {k : ℕ} {s : ℕ} (w : Fin k → ℕ) (hw : ∀ i, w i ≤ E s) : matrixToVec w ≤ E (s + 2 * k)`
- `section termBound` L130–213:
  - L135 `lemma sup_add_pred_card_le_sum {k : ℕ} (g : Fin (k + 1) → ℕ) (hg : ∀ i, 1 ≤ g i) : Finset.univ.sup g + k ≤ ∑ i, g i`
  - L146 `lemma tlen_pos {n : ℕ} (t : SyntacticSemiterm L n) : 1 ≤ tlen t`
  - L150 `def SmallCodes (L : Language) [L.Encodable] : Prop := ∀ {k : ℕ} (f : L.Func k), Encodable.encode f ≤ 8`
  - L153 `lemma eight_le_E {s : ℕ} (h : 2 ≤ s) : 8 ≤ E s`
  - L156 `lemma quote_bvar_eq {n : ℕ} (x : Fin n) : (⌜(#x : SyntacticSemiterm L n)⌝ : ℕ) = ⟪0, (x : ℕ)⟫ + 1`
  - L159 `lemma quote_fvar_eq {n : ℕ} (x : ℕ) : (⌜(&x : SyntacticSemiterm L n)⌝ : ℕ) = ⟪1, x⟫ + 1`
  - L161 `lemma quote_func_eq {n k : ℕ} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) : (⌜Semiterm.func f v⌝ : ℕ) = ⟪2, ⟪(k : ℕ), ⟪Encodable.encode f, matrixToVec fun i ↦ (⌜v i⌝ : ℕ)⟫⟫⟫ + 1`
  - L170 `theorem quote_term_le (hL : SmallCodes L) {n : ℕ} (t : SyntacticSemiterm L n) : (⌜t⌝ : ℕ) ≤ E (8 * tlen t)`
- `section formulaBound` L217–335:
  - L222 `def SmallRelCodes (L : Language) [L.Encodable] : Prop := ∀ {k : ℕ} (r : L.Rel k), Encodable.encode r ≤ 8`
  - L225 `lemma flen_pos {n : ℕ} (φ : Semiproposition L n) : 1 ≤ flen φ`
  - L228 `lemma quote_rel_eq {n k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) : (⌜Semiformula.rel R v⌝ : ℕ) = ⟪0, ⟪(k : ℕ), ⟪Encodable.encode R, matrixToVec fun i ↦ (⌜v i⌝ : ℕ)⟫⟫⟫ + 1`
  - L236 `lemma quote_nrel_eq … : (⌜Semiformula.nrel R v⌝ : ℕ) = ⟪1, ⟪(k : ℕ), ⟪Encodable.encode R, matrixToVec fun i ↦ (⌜v i⌝ : ℕ)⟫⟫⟫ + 1`
  - L245 `private lemma rel_chain {t k M S : ℕ} (ht : t ≤ 2) (hMS : M + k ≤ S) {r vec : ℕ} (hr : r ≤ 8) (hvec : vec ≤ E (8 * M + 2 * (k + 1))) : (⟪t, ⟪(k + 1 : ℕ), ⟪r, vec⟫⟫⟫ : ℕ) + 1 ≤ E (8 * (S + 1))`
  - L256 `private lemma rel_chain₀ {t : ℕ} (ht : t ≤ 2) {r : ℕ} (hr : r ≤ 8) : (⟪t, ⟪(0 : ℕ), ⟪r, (0 : ℕ)⟫⟫⟫ : ℕ) + 1 ≤ E 8`
  - L263 `theorem quote_formula_le (hL : SmallCodes L) (hR : SmallRelCodes L) {n : ℕ} (φ : Semiproposition L n) : (⌜φ⌝ : ℕ) ≤ E (8 * flen φ)`
- `section sequentBound` L339–359, `variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`:
  - L343 `lemma flen_le_sqlen {Γ : Finset (Proposition L)} {φ : Proposition L} (h : φ ∈ Γ) : flen φ ≤ sqlen Γ`
  - L347 `theorem quote_sequent_le (hL : SmallCodes L) (hR : SmallRelCodes L) (Γ : Finset (Proposition L)) : (⌜Γ⌝ : ℕ) ≤ F (8 * sqlen Γ + 1)`
- `section derivationBound` L363–572, `variable {T : Theory L} [T.Δ₁]`:
  - L368 `lemma pair_F' {a b s : ℕ} (ha : a ≤ F s) (hb : b ≤ F s) : (⟪a, b⟫ : ℕ) + 1 ≤ F (s + 2)`
  - L371 `lemma pair_F_le {a b s : ℕ} (ha : a ≤ F s) (hb : b ≤ F s) : (⟪a, b⟫ : ℕ) ≤ F (s + 2)`
  - L374 `lemma tag_le_F {t s : ℕ} (ht : t ≤ 9) (hs : 2 ≤ s) : t ≤ F s`
  - L377 `lemma quote_formula_le_F (hL : SmallCodes L) (hR : SmallRelCodes L) {n : ℕ} (φ : Semiproposition L n) : (⌜φ⌝ : ℕ) ≤ F (8 * flen φ)`
  - L381 `lemma quote_term_le_F (hL : SmallCodes L) {n : ℕ} (t : SyntacticSemiterm L n) : (⌜t⌝ : ℕ) ≤ F (8 * tlen t)`
  - L385 `lemma mlen_pos {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : 1 ≤ mlen d`
  - L388 `lemma sqlen_pos_of_mem {Γ : Finset (Proposition L)} {φ : Proposition L} (h : φ ∈ Γ) : 1 ≤ sqlen Γ`
  - L391 `lemma sqlen_le_mlen {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : sqlen Γ ≤ mlen d`
  - L395 `private lemma step {a b X : ℕ} (ha : a ≤ F X) (hb : b ≤ F X) : (⟪a, b⟫ : ℕ) ≤ F (X + 2)`
  - L399 `theorem quote_derivation_le (hL : SmallCodes L) (hR : SmallRelCodes L) {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : (⌜d⌝ : ℕ) ≤ F (12 * mlen d)`
- `section fbound` L576–595, `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`:
  - L581 `noncomputable def fbound (k : V) : V := Exp.exp (Exp.exp (Exp.exp (12 * k))) + 1`
  - L583 `def fboundDef : 𝚺₁.Semisentence 2 := .mkSigma “y k. ∃ a, !(expDef.ofZero 𝚺₁) a (12 * k) ∧ ∃ b, !(expDef.ofZero 𝚺₁) b a ∧ ∃ c, !(expDef.ofZero 𝚺₁) c b ∧ y = c + 1”`
  - L587 `instance fbound_defined : 𝚺₁-Function₁[V] fbound via fboundDef`
  - L590 `instance fbound_definable : 𝚺₁-Function₁[V] fbound`
  - L592 `lemma fbound_nat (k : ℕ) : fbound k = F (12 * k) + 1`
- `section properness` L597–611, `variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`, `variable {T : Theory L} [T.Δ₁]`:
  - L603 `theorem proper_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) {k : ℕ} {σ : Sentence L} (b : T ⊢! σ) (h : dlen T (⌜b⌝ : ℕ) ≤ k) : (⌜b⌝ : ℕ) < fbound k`
- L615 `lemma smallCodes_LOR : SmallCodes ℒₒᵣ`; L619 `lemma smallRelCodes_LOR : SmallRelCodes ℒₒᵣ`; L622 `lemma smallCodes_LAct : SmallCodes LAct`; L626 `lemma smallRelCodes_LAct : SmallRelCodes LAct`
- `namespace Arithmetic` L631–644: L633 `open ArithS.Arithmetic`; L635 `variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] {k : ℕ}`
  - L639 `theorem lower_bound_dlen_proof_lenGödel_fbound : ∀ b : T ⊢! lenGödel T fboundDef k, k < dlen T (⌜b⌝ : ℕ)` — the M1 gate, unconditional.

## 8. `ArithS/LangAct.lean` (219 lines) — `namespace ArithS`

- L17 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`
- L20 `inductive Act | C | D deriving DecidableEq, Inhabited, Repr`
- L26 `abbrev LAct : Language := ℒₒᵣ + Language.constant Act`

`namespace LAct` (L28–172):
- L31 `abbrev const (a : Act) : LAct.Func 0 := Sum.inr (Language.Constant.Func.const a)`
- L33 `instance decEqConst (k : ℕ) : DecidableEq (Language.Constant.Func Act k)`
- L36 `instance decEqFunc (k : ℕ) : DecidableEq (LAct.Func k)`; L39 `instance decEqRel (k : ℕ) : DecidableEq (LAct.Rel k)`; L42 `instance : LAct.DecidableEq := ⟨decEqFunc, decEqRel⟩`
- L47 `lemma ORing.encode_func_lt_two {k : ℕ} (f : Language.Func ℒₒᵣ k) : Encodable.encode f < 2`
- L52 `def encodeFunc {k : ℕ} : LAct.Func k → ℕ | Sum.inl f => Encodable.encode f | Sum.inr (Language.Constant.Func.const Act.C) => 2 | Sum.inr (Language.Constant.Func.const Act.D) => 3`
- L57 `def decodeFunc : (k : ℕ) → ℕ → Option (LAct.Func k)` (n<2 → ℒₒᵣ decode mapped `Sum.inl`; k=0: 2↦`const C`, 3↦`const D`; else none)
- L64 `@[instance_reducible] def encFunc (k : ℕ) : Encodable (LAct.Func k)`; L73 `@[instance_reducible] def encRel (k : ℕ) : Encodable (LAct.Rel k)`
- L83 `instance instEncFunc (k : ℕ) : Encodable (Language.Func ℒₒᵣ k ⊕ Language.Func (Language.constant Act) k) := encFunc k`; L85 `instance instEncRel (k : ℕ) : Encodable (Language.Rel ℒₒᵣ k ⊕ Language.Rel (Language.constant Act) k) := encRel k`
- L88 `instance : LAct.Encodable := Language.Encodable.mk instEncFunc instEncRel`
- L90 `@[simp] lemma encode_inl_func {k : ℕ} (f : Language.Func ℒₒᵣ k) : Encodable.encode (α := LAct.Func k) (Sum.inl f) = Encodable.encode f := rfl`
- L92 `@[simp] lemma encode_inl_rel {k : ℕ} (r : Language.Rel ℒₒᵣ k) : Encodable.encode (α := LAct.Rel k) (Sum.inl r) = Encodable.encode r := rfl`
- L94 `@[simp] lemma encode_const_C : Encodable.encode (α := LAct.Func 0) (const Act.C) = 2 := rfl`; L95 `@[simp] lemma encode_const_D : … (const Act.D) = 3 := rfl`
- L98 `lemma mem_range_encode_func {k f : ℕ} : f ∈ Set.range (Encodable.encode : LAct.Func k → ℕ) ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)`
- L121 `lemma mem_range_encode_rel {k r : ℕ} : r ∈ Set.range (Encodable.encode : LAct.Rel k → ℕ) ↔ (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)`
- L134 `instance : LAct.LORDefinable where func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)”; rel := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”; …`
- L143–149 `instance : Language.Eq LAct := ⟨Sum.inl Language.Eq.eq⟩`, `Language.LT LAct`, `Language.Zero LAct`, `Language.One LAct`, `Language.Add LAct`, `Language.Mul LAct`, `instance : Language.ORing LAct := Language.ORing.mk`
- L152 `abbrev emb : ℒₒᵣ →ᵥ LAct := Language.Hom.add₁ _ _`
- L155 `def swap : LAct →ᵥ LAct where func {k} f := match k, f with | _, Sum.inl f => Sum.inl f | 0, Sum.inr (Language.Constant.Func.const Act.C) => const Act.D | 0, Sum.inr (Language.Constant.Func.const Act.D) => const Act.C; rel r := r`
- L162 `@[simp] lemma swap_inl {k : ℕ} (f : Language.Func ℒₒᵣ k) : swap.func (Sum.inl f : LAct.Func k) = Sum.inl f := rfl`
- L163 `@[simp] lemma swap_C : swap.func (const Act.C) = const Act.D := rfl`; L164 `@[simp] lemma swap_D : swap.func (const Act.D) = const Act.C := rfl`
- L165 `@[simp] lemma swap_rel {k : ℕ} (r : LAct.Rel k) : swap.rel r = r := rfl`
- L167 `lemma swap_swap_func {k : ℕ} (f : LAct.Func k) : swap.func (swap.func f) = f`
- L170 `lemma swap_emb {k : ℕ} (f : Language.Func ℒₒᵣ k) : swap.func (emb.func f) = emb.func f := rfl`

`section lengthInvariance` (L176–217), `variable {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂)`:
- L180 `lemma tlen_lMap {n : ℕ} (t : SyntacticSemiterm L₁ n) : tlen (Semiterm.lMap Φ t) = tlen t`
- L186 `lemma flen_lMap {n : ℕ} (φ : Semiproposition L₁ n) : flen (Semiformula.lMap Φ φ) = flen φ`

## 9. `ArithS/TheoryAct.lean` (244 lines) — `namespace ArithS`

- L19 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L20 `open LAct`
- L25 `instance stdAct : Structure LAct ℕ where func _ f := match f with | Sum.inl f => (standardModel ℕ).func f | Sum.inr (Language.Constant.Func.const Act.C) => fun _ ↦ 0 | Sum.inr (Language.Constant.Func.const Act.D) => fun _ ↦ 1; rel _ r := match r with | Sum.inl r => (standardModel ℕ).rel r | Sum.inr e => PEmpty.elim e`
- L34 `lemma stdAct_lMap_emb : Structure.lMap emb stdAct = standardModel ℕ`
- L38 `lemma models_lMap_emb (σ : Sentence ℒₒᵣ) : ℕ↓[LAct] ⊧ Semiformula.lMap emb σ ↔ ℕ↓[ℒₒᵣ] ⊧ σ`
- L47 `def cterm (a : Act) {ξ : Type*} {n : ℕ} : Semiterm LAct ξ n := Semiterm.func (const a) ![]`
- L50 `def axNe : Sentence LAct := Semiformula.nrel Language.Eq.eq ![cterm Act.C, cterm Act.D]`
- L53 `def axNe' : Sentence LAct := Semiformula.nrel Language.Eq.eq ![cterm Act.D, cterm Act.C]`
- L56 `abbrev TAct : Theory LAct := insert axNe (insert axNe' (Theory.lMap emb 𝗣𝗔))`

`section codes` (L60–121), `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`:
- L64 `lemma quote_func_emb {k : ℕ} (f : Language.Func ℒₒᵣ k) : (⌜emb.func f⌝ : V) = (⌜f⌝ : V) := rfl`; L65 `lemma quote_rel_emb {k : ℕ} (r : Language.Rel ℒₒᵣ k) : (⌜emb.rel r⌝ : V) = (⌜r⌝ : V) := rfl`
- L67 `lemma matrixToVec_congr {k : ℕ} {w₁ w₂ : Fin k → V} (h : ∀ i, w₁ i = w₂ i) : matrixToVec w₁ = matrixToVec w₂`
- L72 `theorem quote_term_lMap_emb {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) : (⌜Semiterm.lMap emb t⌝ : V) = ⌜t⌝`
- L84 `theorem quote_lMap_emb {n : ℕ} (φ : Semiproposition ℒₒᵣ n) : (⌜Semiformula.lMap emb φ⌝ : V) = ⌜φ⌝`
- L117 `theorem quote_sentence_lMap_emb (σ : Sentence ℒₒᵣ) : (⌜Semiformula.lMap emb σ⌝ : V) = ⌜σ⌝`

`section delta1` (L125–172), L127 `open Arithmetic.HierarchySymbol.Semiformula`:
- L130 `noncomputable def isFormulaOR : 𝚫₁.Semisentence 1 := .mkDelta (.mkSigma “p. !(isSemiformula ℒₒᵣ).sigma 0 p”) (.mkPi “p. !(isSemiformula ℒₒᵣ).pi 0 p”)`
- L134 `lemma isFormulaOR_properOn (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : isFormulaOR.ProperOn V`
- L140 `lemma eval_isFormulaOR {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V) : V ⊧/![p] isFormulaOR.val ↔ IsSemiformula ℒₒᵣ 0 p`
- L147 `noncomputable instance embPA_delta1 : (Theory.lMap emb 𝗣𝗔).Δ₁ where ch := isFormulaOR ⋏ Theory.Δ₁ch 𝗣𝗔; …`
- L170 `noncomputable instance : TAct.Δ₁ := inferInstance`

`section closure` (L176–242):
- L178 `lemma term_lMap_swap_emb {n : ℕ} {ξ : Type*} (t : Semiterm ℒₒᵣ ξ n) : Semiterm.lMap swap (Semiterm.lMap emb t) = Semiterm.lMap emb t`
- L185 `lemma lMap_swap_emb {n : ℕ} {ξ : Type*} (φ : Semiformula ℒₒᵣ ξ n) : Semiformula.lMap swap (Semiformula.lMap emb φ) = Semiformula.lMap emb φ`
- L209 `lemma lMap_swap_cterm_C {ξ : Type*} {n : ℕ} : Semiterm.lMap swap (cterm Act.C : Semiterm LAct ξ n) = cterm Act.D`
- L216 `lemma lMap_swap_cterm_D {ξ : Type*} {n : ℕ} : Semiterm.lMap swap (cterm Act.D : Semiterm LAct ξ n) = cterm Act.C`
- L223 `lemma lMap_swap_axNe : Semiformula.lMap swap axNe = axNe'`; L229 `lemma lMap_swap_axNe' : Semiformula.lMap swap axNe' = axNe`
- L236 `theorem lMap_swap_mem_TAct {σ : Sentence LAct} (h : σ ∈ TAct) : Semiformula.lMap swap σ ∈ TAct`

## 10. `ArithS/Transpose.lean` (158 lines) — `namespace ArithS`

- L17 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L18 `open LAct`
- `section transport` L20–65, `variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₂.DecidableEq] (Φ : L₁ →ᵥ L₂)`, `variable {T : Theory L₁} {T' : Theory L₂}`:
  - L26 `noncomputable def lMapT (hT : ∀ σ ∈ T, Semiformula.lMap Φ σ ∈ T') : {Γ : Finset (Proposition L₁)} → T ⟹₂ Γ → T' ⟹₂ Γ.image (Semiformula.lMap Φ)` (node-for-node transport; `exs` witness becomes `Semiterm.lMap Φ t`)
- `section length` L69–108, `variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₁.Encodable] [L₁.LORDefinable] [L₂.DecidableEq] [L₂.Encodable] [L₂.LORDefinable]`, `variable {T : Theory L₁} [T.Δ₁] {T' : Theory L₂} [T'.Δ₁]`:
  - L75 `lemma mlen_cast {Γ Δ : Finset (Proposition L₁)} (d : T ⟹₂ Γ) (h : Γ = Δ) : mlen (d.cast h) = mlen d`
  - L79 `lemma sqlen_image (Φ : L₁ →ᵥ L₂) (hinj : Function.Injective (Semiformula.lMap Φ : Proposition L₁ → Proposition L₂)) (Γ : Finset (Proposition L₁)) : sqlen (Γ.image (Semiformula.lMap Φ)) = sqlen Γ`
  - L88 `theorem mlen_lMapT (Φ : L₁ →ᵥ L₂) (hT : ∀ σ ∈ T, Semiformula.lMap Φ σ ∈ T') (hinj : Function.Injective (Semiformula.lMap Φ : Proposition L₁ → Proposition L₂)) {Γ : Finset (Proposition L₁)} (d : T ⟹₂ Γ) : mlen (lMapT Φ hT d) = mlen d`
- `section swap` L112–156:
  - L114 `lemma term_lMap_swap_swap {n : ℕ} {ξ : Type*} (t : Semiterm LAct ξ n) : Semiterm.lMap swap (Semiterm.lMap swap t) = t`
  - L121 `lemma lMap_swap_swap {n : ℕ} {ξ : Type*} (φ : Semiformula LAct ξ n) : Semiformula.lMap swap (Semiformula.lMap swap φ) = φ`
  - L145 `lemma lMap_swap_injective {n : ℕ} {ξ : Type*} : Function.Injective (Semiformula.lMap swap : Semiformula LAct ξ n → Semiformula LAct ξ n)`
  - L151 `theorem transpose_exists (φ : Proposition LAct) (d : TAct ⟹₂ {φ}) : ∃ d' : TAct ⟹₂ {Semiformula.lMap swap φ}, mlen d' = mlen d`

## 11. `ArithS/Sound.lean` (126 lines) — `namespace ArithS`

- L15 `open FFL FFL.FirstOrder Arithmetic Bootstrapping Derivation2`
- L17 `variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]`; L18 `variable {T : Theory L} [T.Δ₁]`
- L21 `lemma fstIdx_quote {Γ : Finset (Proposition L)} (b : T ⟹₂ Γ) : fstIdx (⌜b⌝ : ℕ) = ⌜Γ⌝`
- L25 `theorem Derivation.sound' {d : ℕ} (h : Derivation T d) : ∃ Γ : Finset (Proposition L), ∃ b : T ⟹₂ Γ, (⌜b⌝ : ℕ) = d`
- L118 `theorem Proof.sound' {φ : Proposition L} {d : ℕ} (h : Proof T d (⌜φ⌝ : ℕ)) : ∃ b : T ⟹₂ {φ}, (⌜b⌝ : ℕ) = d`

## 12. `ArithS/Symmetry.lean` (74 lines) — `namespace ArithS`

- L20 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L21 `open PeanoMinus`; L22 `open LAct`
- L25 `def ProvableLen (T : Theory LAct) [T.Δ₁] (k : ℕ) (φ : Proposition LAct) : Prop := ∃ d : ℕ, Proof T d (⌜φ⌝ : ℕ) ∧ dlen T d ≤ k`
- L28 `theorem provableLen_swap {k : ℕ} {φ : Proposition LAct} (h : ProvableLen TAct k φ) : ProvableLen TAct k (Semiformula.lMap swap φ)`
- L38 `theorem provableLen_swap_iff (k : ℕ) (φ : Proposition LAct) : ProvableLen TAct k φ ↔ ProvableLen TAct k (Semiformula.lMap swap φ)`
- L46 `theorem lenProvable_fbound_swap {k : ℕ} {φ : Sentence LAct} (h : LenProvable (fbound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ)) : LenProvable (fbound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ)`
- L69 `theorem lenProvable_fbound_swap_iff (k : ℕ) (φ : Sentence LAct) : LenProvable (fbound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ) ↔ LenProvable (fbound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ)`

## 13. `ArithS/Prog.lean` (543 lines) — `namespace ArithS`

- L22 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L23 `open PeanoMinus ISigma0 ISigma1`
- L25 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`

Constructors (action values `0 = C`, `1 = D`):
- L29 `noncomputable def pConst (a : V) : V := ⟪0, a⟫ + 1`
- L30 `noncomputable def pSelf : V := ⟪1, 0⟫ + 1`
- L31 `noncomputable def pOpp : V := ⟪2, 0⟫ + 1`
- L32 `noncomputable def pBot (p : V) : V := ⟪3, p⟫ + 1`
- L33 `noncomputable def pSim (p q : V) : V := ⟪4, p, q⟫ + 1`
- L34 `noncomputable def pIte (b a p q : V) : V := ⟪5, b, a, p, q⟫ + 1`
- L35 `noncomputable def pSearch (k g a p q : V) : V := ⟪6, k, g, a, p, q⟫ + 1`

(NB: the module docstring L13 still says `pSearch k a p q = ⟪6, k, a, p, q⟫ + 1` — stale; the definition has SIX components `⟪6, k, g, a, p, q⟫`.)

`section graphs` L37–64:
- L39 `def pConstGraph : 𝚺₀.Semisentence 2 := .mkSigma “y a. ∃ y' < y, !pairDef y' 0 a ∧ y = y' + 1”`; L40 `instance pConst.defined : 𝚺₀-Function₁[V] pConst via pConstGraph`
- L43 `def pSelfGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !pairDef y' 1 0 ∧ y = y' + 1”`; L44 `def pOppGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !pairDef y' 2 0 ∧ y = y' + 1”`
- L46 `def pBotGraph : 𝚺₀.Semisentence 2 := .mkSigma “y p. ∃ y' < y, !pairDef y' 3 p ∧ y = y' + 1”`; L47 `instance pBot.defined : 𝚺₀-Function₁[V] pBot via pBotGraph`
- L50 `def pSimGraph : 𝚺₀.Semisentence 3 := .mkSigma “y p q. ∃ y' < y, !pair₃Def y' 4 p q ∧ y = y' + 1”`; L51 `instance pSim.defined : 𝚺₀-Function₂[V] pSim via pSimGraph`
- L54 `def pIteGraph : 𝚺₀.Semisentence 5 := .mkSigma “y b a p q. ∃ y' < y, !pair₅Def y' 5 b a p q ∧ y = y' + 1”`; L56 `instance pIte.defined : 𝚺₀-Function₄ (pIte : V → V → V → V → V) via pIteGraph`
- L59 `def pSearchGraph : 𝚺₀.Semisentence 6 := .mkSigma “y k g a p q. ∃ y' < y, !pair₆Def y' 6 k g a p q ∧ y = y' + 1”`; L61 `instance pSearch.defined : 𝚺₀-Function₅ (pSearch : V → V → V → V → V → V) via pSearchGraph`

Size facts (all `@[simp]`): L68 `p_lt_pBot (p : V) : p < pBot p`; L70 `p_lt_pSim (p q : V) : p < pSim p q`; L72 `q_lt_pSim … : q < pSim p q`; L74 `b_lt_pIte (b a p q : V) : b < pIte b a p q`; L76 `p_lt_pIte … : p < pIte b a p q`; L79 `q_lt_pIte … : q < pIte b a p q`; L82 `p_lt_pSearch (k g a p q : V) : p < pSearch k g a p q`; L85 `q_lt_pSearch … : q < pSearch k g a p q`; L147 `a_lt_pConst (a : V) : a < pConst a`; L148 `a_lt_pIte (b a p q : V) : a < pIte b a p q`; L150 `k_lt_pSearch (k g a p q : V) : k < pSearch k g a p q`; L152 `g_lt_pSearch … : g < pSearch k g a p q`; L154 `a_lt_pSearch … : a < pSearch k g a p q`.

Re-valuing actions:
- L92 `noncomputable def relabelAct (a u w : V) : V := if a = 0 then u else if a = 1 then w else a`
- L94 `def relabelActGraph : 𝚺₀.Semisentence 4 := .mkSigma “y a u w. (a = 0 → y = u) ∧ (a = 1 → y = w) ∧ (a ≠ 0 → a ≠ 1 → y = a)”`
- L97 `instance relabelAct.defined : 𝚺₀-Function₃ (relabelAct : V → V → V → V) via relabelActGraph`
- L109 `noncomputable abbrev swapAct (a : V) : V := relabelAct a 1 0`
- L111 `lemma relabelAct_le (a u w : V) : relabelAct a u w ≤ a + u + w`
- L119 `@[simp] lemma relabelAct_zero_one (a : V) : relabelAct a 0 1 = a`
- L127 `@[simp] lemma swapAct_swapAct (a : V) : swapAct (swapAct a) = a`

Shapes:
- L138 `def IsShape (x : V) : Prop := (∃ a, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p, x = pBot p) ∨ (∃ p q, x = pSim p q) ∨ (∃ b a p q, x = pIte b a p q) ∨ (∃ k g a p q, x = pSearch k g a p q)`
- L142 `def isShape : 𝚺₀.Semisentence 1 := .mkSigma “x. (∃ a < x, !pConstGraph x a) ∨ !pSelfGraph x ∨ !pOppGraph x ∨ (∃ p < x, !pBotGraph x p) ∨ (∃ p < x, ∃ q < x, !pSimGraph x p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q) ∨ (∃ k < x, ∃ g < x, ∃ a < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g a p q)”`
- L158 `lemma isShape_iff (x : V) : IsShape x ↔ (∃ a < x, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p < x, x = pBot p) ∨ (∃ p < x, ∃ q < x, x = pSim p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q) ∨ (∃ k < x, ∃ g < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pSearch k g a p q)`
- L184 `lemma lt_and_eq_succ_iff {a y : V} : (a < y ∧ y = a + 1) ↔ y = a + 1`
- L187 `instance IsShape.defined : 𝚺₀-Predicate[V] IsShape via isShape`; L190 `instance IsShape.definable : 𝚺₀-Predicate[V] IsShape`; L192 `instance IsShape.definable' (Γ m) : Γ-[m]-Predicate[V] IsShape`

`namespace Relabel` (L197–320):
- L201 `def Phi (param : Fin 2 → V) (C : Set V) (pr : V) : Prop := (∃ a, pr = ⟪pConst a, pConst (relabelAct a (param 0) (param 1))⟫) ∨ pr = ⟪pSelf, pSelf⟫ ∨ pr = ⟪pOpp, pOpp⟫ ∨ (∃ p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪pBot p, pBot p'⟫) ∨ (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨ (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pIte b a p q, pIte b' (relabelAct a (param 0) (param 1)) p' q'⟫) ∨ (∃ k g a p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSearch k g a p q, pSearch k g (relabelAct a (param 0) (param 1)) p' q'⟫) ∨ (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)` — NOTE: `pSearch`'s `k` and `g` are passed through UNCHANGED (only `a` is relabelled); `pIte`'s `a` is relabelled.
- L212 `def core₀ : 𝚺₀.Semisentence 4 := .mkSigma “pr C u w. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧ (…eight arms…)”`
- L228 `noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨core₀.ofZero _⟩`
- L230 `private lemma phi_iff (param : Fin 2 → V) (C pr : V) : Phi param {x | x ∈ C} pr ↔ ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧ (…bounded arms…)`
- L279 `lemma core₀_defined : 𝚺₀.Defined (fun v : Fin 4 → V ↦ Phi (fun i ↦ v i.succ.succ) {x | x ∈ v 1} (v 0)) core₀`
- L286 `noncomputable def construction : Fixpoint.Construction V blueprint where Φ := Phi; defined := core₀_defined.of_zero; monotone := …`
- L303 `instance : construction.StrongFinite V`

- L323 `def RelabelGraph (u w x y : V) : Prop := Relabel.construction.Fixpoint ![u, w] ⟪x, y⟫`
- L325 `noncomputable def relabelGraphDef : 𝚫₁.Semisentence 4 := .mkDelta (.mkSigma “u w x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !Relabel.blueprint.fixpointDefΔ₁.sigma pr u w”) (.mkPi “u w x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !Relabel.blueprint.fixpointDefΔ₁.pi pr u w”)`
- L329 `private lemma relabel_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2]`
- L332 `instance relabelGraph_defined : 𝚫₁-Relation₄[V] RelabelGraph via relabelGraphDef`; L343 `instance relabelGraph_definable : 𝚫₁-Relation₄[V] RelabelGraph`; L345 `instance relabelGraph_definable' : Γ-[m + 1]-Relation₄[V] RelabelGraph`
- L348 `lemma RelabelGraph.case_iff {u w x y : V} : RelabelGraph u w x y ↔ (∃ a, x = pConst a ∧ y = pConst (relabelAct a u w)) ∨ (x = pSelf ∧ y = pSelf) ∨ (x = pOpp ∧ y = pOpp) ∨ (∃ p p', RelabelGraph u w p p' ∧ x = pBot p ∧ y = pBot p') ∨ (∃ p q p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨ (∃ b a p q b' p' q', RelabelGraph u w b b' ∧ RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ x = pIte b a p q ∧ y = pIte b' (relabelAct a u w) p' q') ∨ (∃ k g a p q p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ x = pSearch k g a p q ∧ y = pSearch k g (relabelAct a u w) p' q') ∨ (¬IsShape y ∧ x = y)`
- L363 `attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape` (section inversion)
- L365 `lemma RelabelGraph.const_iff {u w a y : V} : RelabelGraph u w (pConst a) y ↔ y = pConst (relabelAct a u w)`
- L369 `lemma RelabelGraph.self_iff {u w y : V} : RelabelGraph u w pSelf y ↔ y = pSelf`
- L372 `lemma RelabelGraph.opp_iff {u w y : V} : RelabelGraph u w pOpp y ↔ y = pOpp`
- L375 `lemma RelabelGraph.bot_iff {u w p y : V} : RelabelGraph u w (pBot p) y ↔ ∃ p', RelabelGraph u w p p' ∧ y = pBot p'`
- L379 `lemma RelabelGraph.sim_iff {u w p q y : V} : RelabelGraph u w (pSim p q) y ↔ ∃ p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ y = pSim p' q'`
- L384 `lemma RelabelGraph.ite_iff {u w b a p q y : V} : RelabelGraph u w (pIte b a p q) y ↔ ∃ b' p' q', RelabelGraph u w b b' ∧ RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ y = pIte b' (relabelAct a u w) p' q'`
- L390 `lemma RelabelGraph.search_iff {u w k g a p q y : V} : RelabelGraph u w (pSearch k g a p q) y ↔ ∃ p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ y = pSearch k g (relabelAct a u w) p' q'`
- L395 `lemma RelabelGraph.of_not_shape {u w x y : V} (hx : ¬IsShape x) : RelabelGraph u w x y ↔ y = x`
- L415 `lemma relabelGraph_exists (u w x : V) : ∃ y, RelabelGraph u w x y` (`ISigma1.sigma1_order_induction`)
- L435 `lemma relabelGraph_unique (u w x : V) : ∀ y₁ y₂, RelabelGraph u w x y₁ → RelabelGraph u w x y₂ → y₁ = y₂` (`ISigma1.pi1_order_induction`)
- L460 `lemma relabelGraph_existsUnique (u w x : V) : ∃! y, RelabelGraph u w x y`
- L465 `noncomputable def relabel (u w x : V) : V := Classical.choose! (relabelGraph_existsUnique u w x)`
- L467 `lemma relabel_graph (u w x : V) : RelabelGraph u w x (relabel u w x)`
- L470 `lemma relabel_eq_of_graph {u w x y : V} (h : RelabelGraph u w x y) : relabel u w x = y`
- L473 `noncomputable def relabelDef : 𝚺₁.Semisentence 4 := .mkSigma “y u w x. !relabelGraphDef.sigma u w x y”`
- L475 `instance relabel_defined : 𝚺₁-Function₃ (relabel : V → V → V → V) via relabelDef`; L481 `instance relabel_definable : 𝚺₁-Function₃ (relabel : V → V → V → V)`; L483 `instance relabel_definable' : Γ-[m + 1]-Function₃ (relabel : V → V → V → V)`
- L486 `@[simp] lemma relabel_const (u w a : V) : relabel u w (pConst a) = pConst (relabelAct a u w)`
- L488 `@[simp] lemma relabel_self (u w : V) : relabel u w (pSelf : V) = pSelf`
- L490 `@[simp] lemma relabel_opp (u w : V) : relabel u w (pOpp : V) = pOpp`
- L492 `@[simp] lemma relabel_bot (u w p : V) : relabel u w (pBot p) = pBot (relabel u w p)`
- L494 `@[simp] lemma relabel_sim (u w p q : V) : relabel u w (pSim p q) = pSim (relabel u w p) (relabel u w q)`
- L497 `@[simp] lemma relabel_ite (u w b a p q : V) : relabel u w (pIte b a p q) = pIte (relabel u w b) (relabelAct a u w) (relabel u w p) (relabel u w q)`
- L501 `@[simp] lemma relabel_search (u w k g a p q : V) : relabel u w (pSearch k g a p q) = pSearch k g (relabelAct a u w) (relabel u w p) (relabel u w q)`
- L505 `lemma relabel_of_not_shape {u w x : V} (hx : ¬IsShape x) : relabel u w x = x`
- L509 `theorem relabel_zero_one (x : V) : relabel 0 1 x = x`
- L525 `noncomputable abbrev swapcode (x : V) : V := relabel 1 0 x`
- L528 `theorem swapcode_swapcode (x : V) : swapcode (swapcode x) = x`

## 14. `ArithS/BewV.lean` (46 lines) — `namespace ArithS`

- L15 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L16 `open PeanoMinus ISigma0 ISigma1`
- L18 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`; L19 `variable {L : Language} [L.Encodable] [L.LORDefinable]`; L20 `variable (T : Theory L) [T.Δ₁]` (EXPLICIT `T`)
- L23 `def LenProvableV (k φ : V) : Prop := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k`
- L25 `noncomputable def lenProvableV : 𝚫₁.Semisentence 2 := .mkDelta (.mkSigma “k φ. ∃ E, !fboundDef E k ∧ ∃ d < E, !(proof T).sigma d φ ∧ ∃ n, !(dlenDef T) n d ∧ n ≤ k”) (.mkPi “k φ. ∀ E, !fboundDef E k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(dlenDef T) n d → n ≤ k”)`
- L29 `instance LenProvableV.defined : 𝚫₁-Relation[V] (LenProvableV T) via lenProvableV T`
- L37 `instance LenProvableV.definable : 𝚫₁-Relation[V] (LenProvableV T)`
- L39 `instance LenProvableV.definable' : Γ-[m + 1]-Relation[V] (LenProvableV T)`
- L43 `lemma lenProvableV_numeral (k : ℕ) (φ : V) : LenProvableV T (ORingStructure.numeral k) φ ↔ LenProvable (fbound : V → V) k T φ := Iff.rfl`

## 15. `ArithS/Guard.lean` (173 lines) — `namespace ArithS`

- L24 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L25 `open PeanoMinus ISigma0 ISigma1`; L26 `open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic`; L27 `open LAct`
- L29 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`
- L34 `noncomputable def csym (u : V) : V := ^func 0 (2 + u) 0` — term code of the constant with symbol code `2 + u` (`c_C` for `u = 0`, `c_D` for `u = 1`)
- L36 `noncomputable def csymGraph : 𝚺₁.Semisentence 2 := .mkSigma “y u. !qqFuncDef y 0 (2 + u) 0”`
- L38 `instance csym.defined : 𝚺₁-Function₁[V] csym via csymGraph`; L41 `instance csym.definable : 𝚺₁-Function₁[V] csym`; L42 `instance csym.definable' : Γ-[m + 1]-Function₁[V] csym`
- L47 `noncomputable def dnum (x : V) : V := if x ≤ swapcode x then x else swapcode x`
- L50 `noncomputable def dU (x : V) : V := if x < swapcode x then csym 0 else if swapcode x < x then csym 1 else numeral 0`
- L54 `noncomputable def dW (x : V) : V := if x < swapcode x then csym 1 else if swapcode x < x then csym 0 else numeral 1`
- L58 `noncomputable def actTermCode (a : V) : V := if a = 0 then csym 0 else if a = 1 then csym 1 else numeral a`
- L63 `noncomputable def dnumGraph : 𝚺₁.Semisentence 2 := .mkSigma “y x. ∃ s, !relabelDef s 1 0 x ∧ (x ≤ s → y = x) ∧ (s < x → y = s)”`
- L66 `instance dnum.defined : 𝚺₁-Function₁[V] dnum via dnumGraph`; L77 `instance dnum.definable`; L78 `instance dnum.definable' : Γ-[m + 1]-Function₁[V] dnum`
- L80 `noncomputable def dUGraph : 𝚺₁.Semisentence 2 := .mkSigma “y x. ∃ s, !relabelDef s 1 0 x ∧ ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z 0 ∧ (x < s → y = c0) ∧ (s < x → y = c1) ∧ (x = s → y = z)”`
- L84 `instance dU.defined : 𝚺₁-Function₁[V] dU via dUGraph`; L97 `dU.definable`; L98 `dU.definable'`
- L100 `noncomputable def dWGraph : 𝚺₁.Semisentence 2 := .mkSigma “y x. ∃ s, !relabelDef s 1 0 x ∧ ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z 1 ∧ (x < s → y = c1) ∧ (s < x → y = c0) ∧ (x = s → y = z)”`
- L104 `instance dW.defined : 𝚺₁-Function₁[V] dW via dWGraph`; L117 `dW.definable`; L118 `dW.definable'`
- L120 `noncomputable def actTermCodeGraph : 𝚺₁.Semisentence 2 := .mkSigma “y a. ∃ c0, !csymGraph c0 0 ∧ ∃ c1, !csymGraph c1 1 ∧ ∃ z, !numeralGraph z a ∧ (a = 0 → y = c0) ∧ (a = 1 → y = c1) ∧ (a ≠ 0 → a ≠ 1 → y = z)”`
- L124 `instance actTermCode.defined : 𝚺₁-Function₁[V] actTermCode via actTermCodeGraph`; L134 `actTermCode.definable`; L135 `actTermCode.definable'`
- L143 `noncomputable def descVec (me opp a : V) : V := numeral (dnum me) ∷ dU me ∷ dW me ∷ numeral (dnum opp) ∷ dU opp ∷ dW opp ∷ actTermCode a ∷ 0`
- L147 `noncomputable def guardCode (g me opp a : V) : V := subst LAct (descVec me opp a) g`
- L149 `noncomputable def descVecGraph : 𝚺₁.Semisentence 4 := .mkSigma “y me opp a. ∃ n₁, !dnumGraph n₁ me ∧ ∃ t₁, !numeralGraph t₁ n₁ ∧ ∃ u₁, !dUGraph u₁ me ∧ ∃ w₁, !dWGraph w₁ me ∧ ∃ n₂, !dnumGraph n₂ opp ∧ ∃ t₂, !numeralGraph t₂ n₂ ∧ ∃ u₂, !dUGraph u₂ opp ∧ ∃ w₂, !dWGraph w₂ opp ∧ ∃ t, !actTermCodeGraph t a ∧ ∃ v₆, !adjoinDef v₆ t 0 ∧ ∃ v₅, !adjoinDef v₅ w₂ v₆ ∧ ∃ v₄, !adjoinDef v₄ u₂ v₅ ∧ ∃ v₃, !adjoinDef v₃ t₂ v₄ ∧ ∃ v₂, !adjoinDef v₂ w₁ v₃ ∧ ∃ v₁, !adjoinDef v₁ u₁ v₂ ∧ !adjoinDef y t₁ v₁”`
- L156 `instance descVec.defined : 𝚺₁-Function₃ (descVec : V → V → V → V) via descVecGraph`; L159 `instance descVec.definable : 𝚺₁-Function₃ (descVec : V → V → V → V)`
- L161 `noncomputable def guardCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma “y g me opp a. ∃ w, !descVecGraph w me opp a ∧ !(substsGraph LAct) y w g”`
- L164 `instance guardCode.defined : 𝚺₁-Function₄ (guardCode : V → V → V → V → V) via guardCodeGraph`; L167 `guardCode.definable`; L170 `instance guardCode.definable' : Γ-[m + 1]-Function₄ (guardCode : V → V → V → V → V)`

## 16. `ArithS/Eval.lean` (241 lines) — `namespace ArithS`

- L24 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L25 `open PeanoMinus ISigma0 ISigma1`; L26 `open LAct`
- L28 `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`

`namespace EvalFix`:
- L33 `def Phi (C : Set V) (pr : V) : Prop :=` (verbatim, SIX arms on tuples `⟪n, me, opp, p, a⟫`)
  ```
  (∃ n me opp a, pr = ⟪n + 1, me, opp, pConst a, a⟫) ∨
  (∃ n me opp a, ⟪n, me, opp, me, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pSelf, a⟫) ∨
  (∃ n me opp a, ⟪n, me, opp, opp, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pOpp, a⟫) ∨
  (∃ n me opp p a, ⟪n, me, opp, p, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pBot p, a⟫) ∨
  (∃ n me opp b a' p q a r, ⟪n, me, opp, b, r⟫ ∈ C ∧
    ((r = a' ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pIte b a' p q, a⟫) ∨
  (∃ n me opp k g a' p q a,
    ((LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
      (¬LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pSearch k g a' p q, a⟫)
  ```
- L46 `noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta (.mkSigma “pr C. ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧ ( !pConstGraph p a ∨ (!pSelfGraph p ∧ ∃ t, !pair₅Def t n me opp me a ∧ t ∈ C) ∨ (!pOppGraph p ∧ ∃ t, !pair₅Def t n me opp opp a ∧ t ∈ C) ∨ (∃ p' < p, !pBotGraph p p' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨ (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧ ∃ r < pr + C + 1, (∃ t, !pair₅Def t n me opp b r ∧ t ∈ C) ∧ ((r = a' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨ (r ≠ a' ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) ∨ (∃ k < p, ∃ g < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g a' p' q ∧ ∃ gc, !guardCodeGraph gc g me opp a' ∧ ((!(lenProvableV TAct).sigma k gc ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨ (¬!(lenProvableV TAct).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) )”) (.mkPi “…∀-dual, with !(lenProvableV TAct).pi / ¬!(lenProvableV TAct).sigma swapped…”)⟩` (L46–74)
- L77 `private lemma lt_of_tuple_mem {n me opp b r C : V} (h : ⟪n, me, opp, b, r⟫ ∈ C) : r < C`
- L81 `private lemma tuple_bounds (n me opp p a : V) : n ≤ ⟪n + 1, me, opp, p, a⟫ ∧ me ≤ … ∧ opp ≤ … ∧ p ≤ … ∧ a ≤ ⟪n + 1, me, opp, p, a⟫`
- L92 `private lemma phi_iff (C pr : V) : Phi {x | x ∈ C} pr ↔ ∃ n ≤ pr, ∃ me ≤ pr, ∃ opp ≤ pr, ∃ p ≤ pr, ∃ a ≤ pr, pr = ⟪n + 1, me, opp, p, a⟫ ∧ (p = pConst a ∨ (p = pSelf ∧ ⟪n, me, opp, me, a⟫ ∈ C) ∨ (p = pOpp ∧ ⟪n, me, opp, opp, a⟫ ∈ C) ∨ (∃ p' < p, p = pBot p' ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, p = pIte b a' p' q ∧ ∃ r < pr + C + 1, ⟪n, me, opp, b, r⟫ ∈ C ∧ ((r = a' ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ∨ (∃ k < p, ∃ g < p, ∃ a' < p, ∃ p' < p, ∃ q < p, p = pSearch k g a' p' q ∧ ((LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (¬LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, q, a⟫ ∈ C))) )`
- L134 `noncomputable def construction : Fixpoint.Construction V blueprint where Φ := fun _ ↦ Phi; defined := …; monotone := …`
- L162 `instance : construction.Finite V` (**`Finite`, NOT `StrongFinite`** — sub-calls decrease fuel but may grow other components)

- L191 `def EvalGraph (n me opp p a : V) : Prop := EvalFix.construction.Fixpoint ![] ⟪n, me, opp, p, a⟫`
- L193 `noncomputable def evalGraphDef : 𝚺₁.Semisentence 5 := .mkSigma “n me opp p a. ∃ pr, !pair₅Def pr n me opp p a ∧ !EvalFix.blueprint.fixpointDef pr”` (Σ₁ only; no Δ₁ form)
- L196 `private lemma eval_param_eq (p : Fin 0 → V) (x : V) : EvalFix.construction.Fixpoint p x = EvalFix.construction.Fixpoint ![] x`
- L200 `lemma evalGraph_defined : 𝚺₁.Defined (fun v : Fin 5 → V ↦ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4)) evalGraphDef`
- L205 `instance evalGraph_definable : 𝚺₁-Relation₅[V] EvalGraph`
- L207 `lemma EvalGraph.case_iff {n me opp p a : V} : EvalGraph n me opp p a ↔ ∃ n', n = n' + 1 ∧ ( p = pConst a ∨ (p = pSelf ∧ EvalGraph n' me opp me a) ∨ (p = pOpp ∧ EvalGraph n' me opp opp a) ∨ (∃ p', p = pBot p' ∧ EvalGraph n' me opp p' a) ∨ (∃ b a' p' q r, p = pIte b a' p' q ∧ EvalGraph n' me opp b r ∧ ((r = a' ∧ EvalGraph n' me opp p' a) ∨ (r ≠ a' ∧ EvalGraph n' me opp q a))) ∨ (∃ k g a' p' q, p = pSearch k g a' p' q ∧ ((LenProvableV TAct k (guardCode g me opp a') ∧ EvalGraph n' me opp p' a) ∨ (¬LenProvableV TAct k (guardCode g me opp a') ∧ EvalGraph n' me opp q a))) )`

## 17. `ArithS/EvalN.lean` (142 lines) — `namespace ArithS`

- L12 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L13 `open LAct`
- `section inversion` L15–57, `variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, L19 `attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch`:
  - L21 `lemma EvalGraph.zero_iff {me opp p a : V} : ¬EvalGraph 0 me opp p a`
  - L26 `lemma EvalGraph.const_iff {n me opp a a' : V} : EvalGraph (n + 1) me opp (pConst a) a' ↔ a' = a`
  - L30 `lemma EvalGraph.self_iff {n me opp a : V} : EvalGraph (n + 1) me opp pSelf a ↔ EvalGraph n me opp me a`
  - L34 `lemma EvalGraph.opp_iff {n me opp a : V} : EvalGraph (n + 1) me opp pOpp a ↔ EvalGraph n me opp opp a`
  - L38 `lemma EvalGraph.bot_iff {n me opp p a : V} : EvalGraph (n + 1) me opp (pBot p) a ↔ EvalGraph n me opp p a`
  - L42 `lemma EvalGraph.sim_iff {n me opp p q a : V} : ¬EvalGraph (n + 1) me opp (pSim p q) a` — **`pSim` never evaluates**
  - L45 `lemma EvalGraph.ite_iff {n me opp b a' p q a : V} : EvalGraph (n + 1) me opp (pIte b a' p q) a ↔ ∃ r, EvalGraph n me opp b r ∧ ((r = a' ∧ EvalGraph n me opp p a) ∨ (r ≠ a' ∧ EvalGraph n me opp q a))`
  - L51 `lemma EvalGraph.search_iff {n me opp k g a' p q a : V} : EvalGraph (n + 1) me opp (pSearch k g a' p q) a ↔ ((LenProvableV TAct k (guardCode g me opp a') ∧ EvalGraph n me opp p a) ∨ (¬LenProvableV TAct k (guardCode g me opp a') ∧ EvalGraph n me opp q a))`
- `section nat` L61–140 (all at `ℕ`):
  - L64 `theorem EvalGraph.unique (n : ℕ) : ∀ me opp p a₁ a₂ : ℕ, EvalGraph n me opp p a₁ → EvalGraph n me opp p a₂ → a₁ = a₂`
  - L103 `theorem EvalGraph.mono (n : ℕ) : ∀ me opp p a : ℕ, EvalGraph n me opp p a → EvalGraph (n + 1) me opp p a`
  - L128 `theorem EvalGraph.mono_le {n n' me opp p a : ℕ} (h : n ≤ n') (e : EvalGraph n me opp p a) : EvalGraph n' me opp p a`
  - L135 `theorem EvalGraph.unique' {n n' me opp p a a' : ℕ} (h : EvalGraph n me opp p a) (h' : EvalGraph n' me opp p a') : a = a'`

(Doc L7 mentions `evalN` packaging as `Option ℕ` — **no such definition exists in the file**.)

## 18. `ArithS/Template.lean` (296 lines) — `namespace ArithS`

- L23 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L24 `open PeanoMinus ISigma0 ISigma1`; L25 `open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic`; L26 `open LAct`
- L31 `noncomputable def gtmpl : 𝚺₁.Semisentence 7 := .mkSigma “x₁ u₁ w₁ x₂ u₂ w₂ t. ∃ me, !relabelDef me u₁ w₁ x₁ ∧ ∃ opp, !relabelDef opp u₂ w₂ x₂ ∧ ∃ n, !evalGraphDef n opp me opp t”` — an ℒₒᵣ-semisentence (7 free vars). Reading: variable 0–2 describe "me" (`x₁ u₁ w₁`), 3–5 describe "opp" (`x₂ u₂ w₂`), 6 is the action `t`; the body says the OPPONENT (`relabel u₂ w₂ x₂`) playing in frame `(opp, me)` plays `t`, i.e. "opp plays `t` against me".
- L39 `lemma eval_gtmpl (v : Fin 7 → V) : V ⊧/v gtmpl.val ↔ ∃ n, EvalGraph n (relabel (v 4) (v 5) (v 3)) (relabel (v 1) (v 2) (v 0)) (relabel (v 4) (v 5) (v 3)) (v 6)` (section `eval`, `variable {V …}`)
- L47 `noncomputable def Gtmpl : Semisentence LAct 7 := Semiformula.lMap emb gtmpl.val`
- L49 `lemma lMap_swap_Gtmpl : Semiformula.lMap swap Gtmpl = Gtmpl`
- L54 `noncomputable def numT (k : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (↑k : ClosedSemiterm ℒₒᵣ 0)`
- L57 `noncomputable def dnumT (x : ℕ) : ClosedSemiterm LAct 0 := numT (dnum x)`
- L60 `noncomputable def dUT (x : ℕ) : ClosedSemiterm LAct 0 := if x < swapcode x then cterm Act.C else if swapcode x < x then cterm Act.D else numT 0`
- L64 `noncomputable def dWT (x : ℕ) : ClosedSemiterm LAct 0 := if x < swapcode x then cterm Act.D else if swapcode x < x then cterm Act.C else numT 1`
- L68 `noncomputable def actT (a : ℕ) : ClosedSemiterm LAct 0 := if a = 0 then cterm Act.C else if a = 1 then cterm Act.D else numT a`
- L71 `noncomputable def descTerms (me opp a : ℕ) : Fin 7 → ClosedSemiterm LAct 0 := ![dnumT me, dUT me, dWT me, dnumT opp, dUT opp, dWT opp, actT a]`
- L75 `noncomputable def guardSentence (me opp a : ℕ) : Sentence LAct := Gtmpl ⇜ descTerms me opp a`
- L79 `lemma lMap_swap_numT (k : ℕ) : Semiterm.lMap swap (numT k) = numT k`
- `section dnum` L81–105 (generic `V`): L85 `lemma dnum_of_lt {x : V} (h : x < swapcode x) : dnum x = x`; L88 `lemma dnum_of_eq {x : V} (h : x = swapcode x) : dnum x = x`; L91 `lemma dnum_of_gt {x : V} (h : swapcode x < x) : dnum x = swapcode x`; L99 `lemma dnum_swapcode (x : V) : dnum (swapcode x) = dnum x`
- L107 `lemma lMap_swap_dUT (x : ℕ) : Semiterm.lMap swap (dUT x) = dUT (swapcode x)`
- L116 `lemma lMap_swap_dWT (x : ℕ) : Semiterm.lMap swap (dWT x) = dWT (swapcode x)`
- L125 `lemma lMap_swap_actT (a : ℕ) : Semiterm.lMap swap (actT a) = actT (swapAct a)`
- L133 `lemma lMap_swap_dnumT (x : ℕ) : Semiterm.lMap swap (dnumT x) = dnumT (swapcode x)`
- L138 `theorem lMap_swap_guardSentence (me opp a : ℕ) : Semiformula.lMap swap (guardSentence me opp a) = guardSentence (swapcode me) (swapcode opp) (swapAct a)` — **the swap equation**
- `section codes` L148–186 (generic `V`): L152 `lemma quote_Gtmpl : (⌜Gtmpl⌝ : V) = ⌜gtmpl.val⌝`; L156 `lemma term_emb_lMap_emb (t : ClosedSemiterm ℒₒᵣ 0) : (Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct 0) = Semiterm.lMap emb (Rew.emb t)`; L163 `lemma quote_numT (k : ℕ) : (⌜numT k⌝ : V) = numeral (k : V)`; L170 `lemma encode_const_C : Encodable.encode (const Act.C) = 2 := rfl`; L171 `lemma encode_const_D : Encodable.encode (const Act.D) = 3 := rfl`; L173 `lemma quote_cterm_C : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = csym 0`; L179 `lemma quote_cterm_D : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = csym 1`
- L188 `lemma quote_dnumT (x : ℕ) : (⌜dnumT x⌝ : ℕ) = numeral (dnum x)`; L191 `lemma quote_dUT (x : ℕ) : (⌜dUT x⌝ : ℕ) = dU x`; L199 `lemma quote_dWT (x : ℕ) : (⌜dWT x⌝ : ℕ) = dW x`; L207 `lemma quote_actT (a : ℕ) : (⌜actT a⌝ : ℕ) = actTermCode a`
- L215 `lemma typed_val_emb (t : ClosedSemiterm LAct 0) : ((⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)).val = (⌜t⌝ : ℕ) := rfl`
- L219 `lemma semitermVec_val_descTerms (me opp a : ℕ) : SemitermVec.val (fun i ↦ (⌜(Rew.emb (descTerms me opp a i) : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) = descVec me opp a`
- L235 `theorem quote_guardSentence (me opp a : ℕ) : (⌜guardSentence me opp a⌝ : ℕ) = guardCode (⌜Gtmpl⌝ : ℕ) me opp a` — **the code equation**
- `section truth` L246–294: L248 `lemma val_numT (k : ℕ) : (numT k).val (s := stdAct) ![] Empty.elim = k`; L253 `lemma val_cterm_C : (cterm Act.C : ClosedSemiterm LAct 0).val (s := stdAct) ![] Empty.elim = 0 := rfl`; L254 `lemma val_cterm_D : … = 1 := rfl`; L256 `lemma val_dnumT (x : ℕ) : (dnumT x).val (s := stdAct) ![] Empty.elim = dnum x`; L259 `lemma relabel_val_desc (x : ℕ) : relabel ((dUT x).val (s := stdAct) ![] Empty.elim) ((dWT x).val (s := stdAct) ![] Empty.elim) (dnum x) = x`; L272 `lemma val_actT (a : ℕ) : (actT a).val (s := stdAct) ![] Empty.elim = a`
- L281 `theorem models_guardSentence_iff (me opp a : ℕ) : ℕ↓[LAct] ⊧ guardSentence me opp a ↔ ∃ n, EvalGraph n opp me opp a` — **the truth equation**

## 19. `ArithS/RedCell.lean` (128 lines) — `namespace ArithS`

- L22 `open FFL FFL.FirstOrder Arithmetic Bootstrapping`; L23 `open PeanoMinus`; L24 `open LAct`
- L29 `noncomputable def Dupoc (k : ℕ) : ℕ := pSearch k (⌜Gtmpl⌝ : ℕ) 0 (pConst 0) (pConst 1)`
- L32 `noncomputable def Cupod (k : ℕ) : ℕ := pSearch k (⌜Gtmpl⌝ : ℕ) 1 (pConst 1) (pConst 0)`
- L34 `lemma swapAct_zero : swapAct (0 : ℕ) = 1`; L35 `lemma swapAct_one : swapAct (1 : ℕ) = 0`
- L38 `theorem swapcode_Dupoc (k : ℕ) : swapcode (Dupoc k) = Cupod k`; L43 `theorem swapcode_Cupod (k : ℕ) : swapcode (Cupod k) = Dupoc k`
- L48 `lemma models_axNe : ℕ↓[LAct] ⊧ axNe`; L55 `lemma models_axNe' : ℕ↓[LAct] ⊧ axNe'`
- L62 `instance models_TAct : ℕ↓[LAct] ⊧* TAct`
- L74 `lemma lenProvableV_nat (k φ : ℕ) : LenProvableV TAct k φ ↔ LenProvable (fbound : ℕ → ℕ) k TAct φ`
- L80 `theorem evalGraph_of_guard {k me opp a : ℕ} (h : LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) me opp a)) : ∃ n, EvalGraph n opp me opp a` — guard soundness (via `provable_iff_provable`, `models_of_provable models_TAct`)
- L89 `theorem guard_Dupoc_iff_guard_Cupod (k : ℕ) : LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) (Dupoc k) (Cupod k) 0) ↔ LenProvableV TAct k (guardCode (⌜Gtmpl⌝ : ℕ) (Cupod k) (Dupoc k) 1)`
- **L99 `theorem red_cell (k : ℕ) : EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0`** — Dupoc plays `1` (= D) vs Cupod, Cupod plays `0` (= C) vs Dupoc, every shared `k`, fuel `2`.
- L123 `theorem red_cell_unique (k n : ℕ) {a b : ℕ} (ha : EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) a) (hb : EvalGraph n (Cupod k) (Dupoc k) (Cupod k) b) : a = 1 ∧ b = 0`

---

## Gap list vs the engine's full `Prog`/`Formula`

Engine reference: `engine/PrisonersDilemma/Program.lean:25–91` (`mutual` block) and `Dynamics.lean:20–76` (`eval`).

### Engine `Prog` constructors (Program.lean:26–70)
```
| const  : Action → Prog
| self   : Prog
| opp    : Prog
| bot    : Prog → Prog
| sim    : Prog → Prog → Prog
| ite    : Prog → Action → Prog → Prog → Prog
| search : Nat → Formula → Prog → Prog → Prog
| tvote  : VoteList → Nat → Prog → Prog → Prog
| sys    : ProgList → Nat → Prog
| selfIdx : Nat → Prog
```
plus `ProgList (nil | cons)`, `VoteList (nil | cons : Nat → Prog → VoteList → VoteList)`.

### Engine `Formula` constructors (Program.lean:78–84)
```
| plays : Prog → Prog → Action → Formula
| impl  : Formula → Formula → Formula
| neg   : Formula → Formula
| box   : Nat → Formula → Formula
| eq    : Prog → Prog → Formula
| diag  : Nat → Formula → Formula
```

### ArithS code-level constructors (Prog.lean:29–35) and their status

| Engine ctor | ArithS code | `IsShape` arm | `relabel`/`swapcode` clause | `EvalFix.Phi` clause (Eval.lean:33) | `EvalGraph.*_iff` |
|---|---|---|---|---|---|
| `.const a` | `pConst a = ⟪0,a⟫+1` | yes | `pConst (relabelAct a u w)` | **yes** (arm 1) | `const_iff` |
| `.self` | `pSelf = ⟪1,0⟫+1` | yes | fixed | **yes** (arm 2: runs `me` in same frame) | `self_iff` |
| `.opp` | `pOpp = ⟪2,0⟫+1` | yes | fixed | **yes** (arm 3: runs `opp` in same frame) | `opp_iff` |
| `.bot p` | `pBot p = ⟪3,p⟫+1` | yes | `pBot (relabel p)` | **yes** (arm 4) | `bot_iff` |
| `.sim p q` | `pSim p q = ⟪4,p,q⟫+1` | yes | `pSim (relabel p) (relabel q)` | **NO clause** — code exists, relabel descends, but `EvalFix.Phi` has no `pSim` arm; `EvalGraph.sim_iff : ¬EvalGraph (n+1) me opp (pSim p q) a` (EvalN.lean:42). Eval.lean doc L14–15: "the engine substitutes the frame into `p`, `q` first, which needs a program-substitution function — deferred generalisation". No `subst` on program codes exists in ArithS. | `sim_iff` (negative) |
| `.ite b a p q` | `pIte b a p q = ⟪5,b,a,p,q⟫+1` | yes | `pIte (relabel b) (relabelAct a) (relabel p) (relabel q)` | **yes** (arm 5: `r ≠ a'` else-branch, matches engine `if r == a`) | `ite_iff` |
| `.search k φ p q` | `pSearch k g a p q = ⟪6,k,g,a,p,q⟫+1` | yes | `pSearch k g (relabelAct a) (relabel p) (relabel q)` (k, g untouched) | **yes** (arm 6) | `search_iff` |
| `.tvote v θ p q` | **none** | — | — | — | — |
| `.sys defs i` | **none** | — | — | — | — |
| `.selfIdx j` | **none** | — | — | — | — |
| `ProgList`/`VoteList` | **none** | — | — | — | — |

Fuel: engine `eval 0 _ _ _ = none`; ArithS `EvalGraph.zero_iff : ¬EvalGraph 0 me opp p a` (EvalN.lean:21). Engine `eval` returns `Option Action`; ArithS `EvalGraph` is a relation, with determinism (`EvalGraph.unique`) and fuel monotonicity (`EvalGraph.mono`, `mono_le`, `unique'`) proved ONLY at `V = ℕ` (EvalN.lean §nat). `EvalFix.construction` is `Finite` not `StrongFinite`; `evalGraphDef` is Σ₁ only (no Π₁/Δ₁ form of `EvalGraph`).

### `pSearch` vs the engine's `.search k φ p q`

Engine (Dynamics.lean:34–37): `| .search k φ p q => if proofSearch k (φ.subst me opponent) then eval n me opponent p else eval n me opponent q`, where `φ : Formula` (an arbitrary DSL formula, closed by `Formula.subst me opponent`) and `proofSearch k φ := decide (Pf k φ)`.

ArithS `pSearch k g a p q` stores FIVE components (Prog.lean:35):
- `k` — the proof-length budget (an element of `V`, passed as the first argument of `LenProvableV TAct k _` — object-level, NOT `ℕ`);
- `g` — a **formula CODE** of an ℒₒᵣ/LAct semisentence with 7 free variables (the "template"); in the red cell it is `⌜Gtmpl⌝ : ℕ` (RedCell.lean:29,32);
- `a` — the action value (`0 = C`, `1 = D`) that the guard asserts "opp plays `a` against me";
- `p`, `q` — then/else sub-programs.

Evaluation (Eval.lean:41–44): `LenProvableV TAct k (guardCode g me opp a')` decides the branch, where `guardCode g me opp a' = subst LAct (descVec me opp a') g` (Guard.lean:147). So the only guard FORM available is "the 7-variable template `g` instantiated at the canonical descriptions of `(me, opp)` and action `a`" — the engine's `Formula.plays/impl/neg/box/eq/diag` structure has NO counterpart; there is no ArithS code-level `Formula` type at all. The template `g` is arbitrary as a code (any `g` is a valid `pSearch` component and `IsShape` accepts any `g < x`), but only `Gtmpl` (= "opp plays `t` against me", the `.plays .opp .self a` guard of DupocBot/CupodBot) has a meta sentence, code equation, swap equation and truth equation (Template.lean). `guardCode` substitutes the description vector positionally: variable `#0 ↦ numeral (dnum me)`, `#1 ↦ dU me`, `#2 ↦ dW me`, `#3 ↦ numeral (dnum opp)`, `#4 ↦ dU opp`, `#5 ↦ dW opp`, `#6 ↦ actTermCode a` (Guard.lean:143–147).

### How `guardCode` / `descVec` / canonical descriptions work

- A program code `x` is described by the triple `(numeral (dnum x), dU x, dW x)` meaning `relabel (dU x) (dW x) (dnum x) = x` (Template.lean:259 `relabel_val_desc`, at the standard model `stdAct` where `c_C ↦ 0`, `c_D ↦ 1`):
  - `dnum x = if x ≤ swapcode x then x else swapcode x` (Guard.lean:47) — the canonical (smaller) representative of the τ-orbit `{x, swapcode x}`, inserted as a NUMERAL;
  - `dU x` / `dW x` (Guard.lean:50,54): if `x < swapcode x` then `(c_C, c_D)` (`csym 0, csym 1`); if `swapcode x < x` then `(c_D, c_C)`; on a tie `(numeral 0, numeral 1)`.
  - `csym u = ^func 0 (2 + u) 0` (Guard.lean:34) is the term code of the LAct constant with symbol code `2 + u` (`encode_const_C = 2`, `encode_const_D = 3`, LangAct.lean:94–95).
  - `actTermCode a = if a = 0 then csym 0 else if a = 1 then csym 1 else numeral a` (Guard.lean:58).
- `swap : LAct →ᵥ LAct` exchanges `c_C ↔ c_D` syntactically, so `lMap swap` sends the description of `x` to the description of `swapcode x` and `actT a` to `actT (swapAct a)` (Template.lean:107–133), whence `lMap_swap_guardSentence` (Template.lean:138). This is what makes the τ-argument work WITHOUT numerals being swapped (numerals are `swap`-invariant: `lMap_swap_numT`).
- All of `csym, dnum, dU, dW, actTermCode, descVec, guardCode` are Σ₁-definable with graphs `csymGraph, dnumGraph (via relabelDef s 1 0 x), dUGraph, dWGraph, actTermCodeGraph, descVecGraph, guardCodeGraph (via substsGraph LAct)`.
- Meta side (Template.lean): `numT k`, `dnumT x`, `dUT x`, `dWT x`, `actT a : ClosedSemiterm LAct 0`; `descTerms me opp a : Fin 7 → ClosedSemiterm LAct 0`; `guardSentence me opp a := Gtmpl ⇜ descTerms me opp a`; code equation `⌜guardSentence me opp a⌝ = guardCode ⌜Gtmpl⌝ me opp a` (ℕ only); truth equation `ℕ↓[LAct] ⊧ guardSentence me opp a ↔ ∃ n, EvalGraph n opp me opp a`.

### `LenProvableV` / `LenProvable` / `ProvableLen` / `fbound`

- `LenProvable (f : V → V) (k : ℕ) (T : Theory L) [T.Δ₁] (φ : V) : Prop := ∃ d < f (numeral k), Proof T d φ ∧ dlen T d ≤ numeral k` (Bew.lean:35) — meta budget `k : ℕ`, parametric bound `f`; Π₁-defined by `lenProvable T fDef k : 𝚷₁.Semisentence 1` (Bew.lean:40); `lenProvabilityPred T fDef k σ := (lenProvable T fDef k).val/[⌜σ⌝]` is the sentence `□_k σ`.
- `LenProvableV (T) (k φ : V) : Prop := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k` (BewV.lean:23) — budget as an OBJECT variable, bound fixed to `fbound`; Δ₁-defined by `lenProvableV T : 𝚫₁.Semisentence 2`; `lenProvableV_numeral : LenProvableV T (numeral k) φ ↔ LenProvable fbound k T φ := Iff.rfl`; at ℕ `lenProvableV_nat` (RedCell.lean:74). This is what `EvalFix.Phi`'s search arm consults, with `T := TAct`.
- `ProvableLen (T : Theory LAct) [T.Δ₁] (k : ℕ) (φ : Proposition LAct) : Prop := ∃ d : ℕ, Proof T d ⌜φ⌝ ∧ dlen T d ≤ k` (Symmetry.lean:25) — the code-bound-FREE reading at ℕ; τ-closure `provableLen_swap_iff`.
- `fbound (k : V) : V := Exp.exp (Exp.exp (Exp.exp (12 * k))) + 1` (Proper.lean:581), `fbound_nat : fbound k = F (12 * k) + 1` with `F s = 2^(2^(2^s))`; Σ₁ graph `fboundDef`. Properness: `proper_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) (b : T ⊢! σ) (h : dlen T ⌜b⌝ ≤ k) : ⌜b⌝ < fbound k` — hence the code bound never bites for `ℒₒᵣ` (`smallCodes_LOR`) or `LAct` (`smallCodes_LAct`, `smallRelCodes_LAct`), and `lenProvable_fbound_swap_iff` (Symmetry.lean:69) holds for `LenProvable fbound k TAct` on sentence codes.
- `dlen T d` (DerivationLength.lean:389): `Classical.choose!` of the Δ₁ graph `DlenGraph L d n` (Fixpoint on `⟪d, n⟫`, `StrongFinite`), `0` on non-derivations; cost model per node = `setLen L s + 1` (+ sub-lengths, + `termLen L t` at `exsIntro`); meta twin `mlen` with bridge `dlen_quote : dlen T ⌜d⌝ = mlen d` (ℕ).

### `TAct` / `LAct` / `swap`

- `LAct : Language := ℒₒᵣ + Language.constant Act` (LangAct.lean:26), `Act := C | D`; hand-written `Encodable` keeping ℒₒᵣ codes and `c_C ↦ 2`, `c_D ↦ 3`; `LAct.LORDefinable` instance with `func := “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)”`, `rel := “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”`; `Language.ORing LAct` instance; `emb : ℒₒᵣ →ᵥ LAct := Language.Hom.add₁ _ _`.
- `swap : LAct →ᵥ LAct` (LangAct.lean:155): `func`: `Sum.inl f ↦ Sum.inl f`, `const C ↦ const D`, `const D ↦ const C`; `rel r := r`. Involution on symbols (`swap_swap_func`), on terms/formulas (`term_lMap_swap_swap`, `lMap_swap_swap`), injective (`lMap_swap_injective`), fixes the ℒₒᵣ image (`lMap_swap_emb`).
- `TAct : Theory LAct := insert axNe (insert axNe' (Theory.lMap emb 𝗣𝗔))` (TheoryAct.lean:56), `axNe = nrel eq ![cterm C, cterm D]`, `axNe' = nrel eq ![cterm D, cterm C]`; `cterm a := Semiterm.func (const a) ![]`. Δ₁ instance `embPA_delta1` with `ch := isFormulaOR ⋏ Theory.Δ₁ch 𝗣𝗔`; `noncomputable instance : TAct.Δ₁`. Literally closed under swap (`lMap_swap_mem_TAct`). Standard model `stdAct : Structure LAct ℕ` (`c_C ↦ 0`, `c_D ↦ 1`), `models_TAct : ℕ↓[LAct] ⊧* TAct` (RedCell.lean:62).

### Other observations relevant to M3

- `Gtmpl`'s body is Σ₁ (`∃ me, ∃ opp, ∃ n, …`); its instantiated guard is a Σ₁ LAct-sentence about `EvalGraph`. There is no arithmetized `Pf`/box/Löb layer: provability in ArithS is Foundation's `Proof TAct d φ` + `dlen`, not a mirror of the engine's 33-constructor `Pf`.
- No transfer theorem (`Pf k φ → LenProvableV …` or converse) exists anywhere in `arith/`; the engine is never imported (lakefile comment: "the engine is required only from milestone M3").
- The description scheme depends on `<` comparing `x` and `swapcode x` on `V`; `dnum/dU/dW` are defined for general `V` but `dnumT/dUT/dWT/actT/guardSentence` and all `quote_*`/truth lemmas are ℕ-only.
- Stale docs to be aware of: Prog.lean L13 (five-tuple `pSearch`), EvalN.lean L7 (`evalN` does not exist).