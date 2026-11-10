import ArithS.Agents.Code

/-!
# ArithS.Agents.CodeTranspose — τ on program codes and templates, boxes included

**What this file proves.** `Agents/Code.lean` proves that the code-level transposition of a program's code is
the code of the engine's transposed program, and that τ maps the template of a formula to the template of
the transposed formula, on the search-bot fragment `fragP`/`fragF` — which has no `.box` in a guard. This
file proves both on the fragment WITH boxes:

* `transposableP`/`transposableF`: no tau constructor (`.tvote`/`.sys`/`.selfIdx`), hereditarily through the
  guards and through the programs the guards mention; `.box` allowed at any depth; no condition on the atoms.
  `fragP p → transposableP p` (`transposableP_of_fragP`).
* `lMap_swap_templateAt_of_transposableF`: `τ (templateAt φ k₀) = templateAt φ.transpose k₀`;
  `lMap_swap_template_of_transposableF`: the same for the six-variable `template`;
  `transposeCode_progCode_of_transposableP`: `transposeCode (progCode p) = progCode p.transpose`.

**Why the box case now holds.** A `.box k ψ` names the template of `ψ` by the closed term `boxQuote`
(`Agents/Code.lean`), which carries an action constant: `τ (boxQuote σ) = boxQuote (τ σ)`
(`lMap_swap_boxQuote`). With the induction hypothesis `τ (template13 ψ) = template13 ψ.transpose` the box
clause transposes into the box clause of `ψ.transpose`; the rest of the clause (the two frame descriptions,
`guardCodeG`, `lenProvG`, the budget numeral) is τ-invariant.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### The fragment -/

mutual
  /-- The programs the transposition theorem covers: no tau constructor, every guard in `transposableF`. -/
  def transposableP : PD.Prog → Bool
    | .const _ => true
    | .self => true
    | .opp => true
    | .bot p => transposableP p
    | .sim p q => transposableP p && transposableP q
    | .ite b _ p q => transposableP b && transposableP p && transposableP q
    | .search _ φ p q => transposableF φ && transposableP p && transposableP q
    | .tvote _ _ _ _ => false
    | .sys _ _ => false
    | .selfIdx _ => false
  /-- The guards the transposition theorem covers: atoms over `transposableP` programs, the connectives, and
  `.box` at any depth. -/
  def transposableF : PD.Formula → Bool
    | .plays p q _ => transposableP p && transposableP q
    | .impl φ ψ => transposableF φ && transposableF ψ
    | .neg φ => transposableF φ
    | .box _ φ => transposableF φ
    | .eq p q => transposableP p && transposableP q
    | .diag _ _ => true
end

mutual
  /-- The search-bot fragment is inside the transposition fragment. -/
  theorem transposableP_of_fragP : ∀ p : PD.Prog, fragP p = true → transposableP p = true
    | .const _, _ => rfl
    | .self, _ => rfl
    | .opp, _ => rfl
    | .bot p, h => by
      simp only [fragP] at h
      simp only [transposableP, transposableP_of_fragP p h]
    | .sim p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [transposableP, transposableP_of_fragP p h.1, transposableP_of_fragP q h.2, Bool.and_self]
    | .ite b _ p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [transposableP, transposableP_of_fragP b h.1.1, transposableP_of_fragP p h.1.2,
        transposableP_of_fragP q h.2, Bool.and_self]
    | .search _ φ p q, h => by
      simp only [fragP, Bool.and_eq_true] at h
      simp only [transposableP, transposableF_of_fragF φ h.1.1, transposableP_of_fragP p h.1.2,
        transposableP_of_fragP q h.2, Bool.and_self]
    | .tvote _ _ _ _, h => by simp [fragP] at h
    | .sys _ _, h => by simp [fragP] at h
    | .selfIdx _, h => by simp [fragP] at h
  theorem transposableF_of_fragF : ∀ φ : PD.Formula, fragF φ = true → transposableF φ = true
    | .plays p q _, h => by
      simp only [fragF, Bool.and_eq_true] at h
      simp only [transposableF, transposableP_of_fragP p h.1.1.2, transposableP_of_fragP q h.2, Bool.and_self]
    | .impl φ ψ, h => by
      simp only [fragF, Bool.and_eq_true] at h
      simp only [transposableF, transposableF_of_fragF φ h.1, transposableF_of_fragF ψ h.2, Bool.and_self]
    | .neg φ, h => by
      simp only [fragF] at h
      simp only [transposableF, transposableF_of_fragF φ h]
    | .box _ _, h => by simp [fragF] at h
    | .eq p q, h => by
      simp only [fragF, Bool.and_eq_true] at h
      simp only [transposableF, transposableP_of_fragP p h.1.2, transposableP_of_fragP q h.2, Bool.and_self]
    | .diag _ _, _ => rfl
end

mutual
  /-- A program of the transposition fragment has no dangling pronoun. -/
  theorem noSelfIdxP_of_transposableP : ∀ p : PD.Prog, transposableP p = true → noSelfIdxP p = true
    | .const _, _ => rfl
    | .self, _ => rfl
    | .opp, _ => rfl
    | .bot p, h => by
      simp only [transposableP] at h
      simp only [noSelfIdxP, noSelfIdxP_of_transposableP p h]
    | .sim p q, h => by
      simp only [transposableP, Bool.and_eq_true] at h
      simp only [noSelfIdxP, noSelfIdxP_of_transposableP p h.1, noSelfIdxP_of_transposableP q h.2, Bool.and_self]
    | .ite b _ p q, h => by
      simp only [transposableP, Bool.and_eq_true] at h
      simp only [noSelfIdxP, noSelfIdxP_of_transposableP b h.1.1, noSelfIdxP_of_transposableP p h.1.2,
        noSelfIdxP_of_transposableP q h.2, Bool.and_self]
    | .search _ φ p q, h => by
      simp only [transposableP, Bool.and_eq_true] at h
      simp only [noSelfIdxP, noSelfIdxF_of_transposableF φ h.1.1, noSelfIdxP_of_transposableP p h.1.2,
        noSelfIdxP_of_transposableP q h.2, Bool.and_self]
    | .tvote _ _ _ _, h => by simp [transposableP] at h
    | .sys _ _, h => by simp [transposableP] at h
    | .selfIdx _, h => by simp [transposableP] at h
  theorem noSelfIdxF_of_transposableF : ∀ φ : PD.Formula, transposableF φ = true → noSelfIdxF φ = true
    | .plays p q _, h => by
      simp only [transposableF, Bool.and_eq_true] at h
      simp only [noSelfIdxF, noSelfIdxP_of_transposableP p h.1, noSelfIdxP_of_transposableP q h.2, Bool.and_self]
    | .impl φ ψ, h => by
      simp only [transposableF, Bool.and_eq_true] at h
      simp only [noSelfIdxF, noSelfIdxF_of_transposableF φ h.1, noSelfIdxF_of_transposableF ψ h.2, Bool.and_self]
    | .neg φ, h => by
      simp only [transposableF] at h
      simp only [noSelfIdxF, noSelfIdxF_of_transposableF φ h]
    | .box _ φ, h => by
      simp only [transposableF] at h
      simp only [noSelfIdxF, noSelfIdxF_of_transposableF φ h]
    | .eq p q, h => by
      simp only [transposableF, Bool.and_eq_true] at h
      simp only [noSelfIdxF, noSelfIdxP_of_transposableP p h.1, noSelfIdxP_of_transposableP q h.2, Bool.and_self]
    | .diag _ _, _ => rfl
end

/-! ### τ on the templates and on the codes -/

/-- τ on the name of a quoted template, in any bound-variable context. -/
lemma lMap_swap_cl_boxQuote {n m : ℕ} (σ : Semisentence LAct m) :
    Semiterm.lMap swap (cl (boxQuote σ) : Semiterm LAct Empty n) = cl (boxQuote (Semiformula.lMap swap σ)) := by
  rw [lMap_swap_cl, lMap_swap_boxQuote]

/-- τ fixes the budget numeral, in any bound-variable context. -/
lemma lMap_swap_cl_numTB {n : ℕ} (k : ℕ) :
    Semiterm.lMap swap (cl (numTB k) : Semiterm LAct Empty n) = cl (numTB k) := by
  rw [lMap_swap_cl, lMap_swap_numTB]

mutual
  /-- **τ on the stored templates, boxes included**: the transposition of the template at the node budget is
  the template of the transposed formula at the same budget. -/
  theorem lMap_swap_templateAt_of_transposableF : ∀ (k₀ : Option ℕ) (φ : PD.Formula), transposableF φ = true →
      Semiformula.lMap swap (templateAt φ k₀) = templateAt φ.transpose k₀
    | k₀, .plays p q a, h => by
      simp only [transposableF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, templateAt_plays, templateAt_plays]
      unfold progGraphAt
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_evalG,
        lMap_swap_progAuxAt k₀ (noSelfIdxP_of_transposableP p h.1) (transposeCode_progCode_of_transposableP p h.1),
        lMap_swap_progAuxAt k₀ (noSelfIdxP_of_transposableP q h.2) (transposeCode_progCode_of_transposableP q h.2)]
      congr 4
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        · congr 1; funext i; fin_cases i <;> rfl
        · congr 1
          funext i
          fin_cases i
          · rfl
          · rfl
          · rfl
          · rfl
          · show Semiterm.lMap swap (cl (actT (actCode a))) = cl (actT (actCode a.swap))
            rw [lMap_swap_cl, lMap_swap_actT, actCode_swap]
    | k₀, .impl φ ψ, h => by
      simp only [transposableF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, templateAt_impl, templateAt_impl, LogicalConnective.HomClass.map_imply,
        lMap_swap_templateAt_of_transposableF k₀ φ h.1, lMap_swap_templateAt_of_transposableF k₀ ψ h.2]
    | k₀, .neg φ, h => by
      simp only [transposableF] at h
      rw [PD.Formula.transpose, templateAt_neg, templateAt_neg, LogicalConnective.HomClass.map_neg,
        lMap_swap_templateAt_of_transposableF k₀ φ h]
    | k₀, .box k ψ, h => by
      simp only [transposableF] at h
      have hq : Semiformula.lMap swap (template13 ψ) = template13 ψ.transpose :=
        lMap_swap_templateAt_of_transposableF none ψ h
      rw [PD.Formula.transpose, templateAt_box, templateAt_box, progAuxAt_self, progAuxAt_opp]
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_guardCodeG, lMap_swap_lenProvG, lMap_swap_descF, Semiterm.lMap_bvar]
      congr 3
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        · congr 1; funext i; fin_cases i <;> rfl
        · congr 2
          · congr 1
            funext i
            fin_cases i
            · rfl
            · show Semiterm.lMap swap (cl (boxQuote (template13 ψ))) = cl (boxQuote (template13 ψ.transpose))
              rw [lMap_swap_cl_boxQuote, hq]
            · rfl
            · rfl
          · congr 1
            funext i
            fin_cases i
            · show Semiterm.lMap swap (cl (numTB k)) = cl (numTB k)
              exact lMap_swap_cl_numTB k
            · rfl
    | k₀, .eq p q, h => by
      simp only [transposableF, Bool.and_eq_true] at h
      rw [PD.Formula.transpose, templateAt_eq, templateAt_eq]
      unfold progGraphAt
      simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
        lMap_swap_progAuxAt k₀ (noSelfIdxP_of_transposableP p h.1) (transposeCode_progCode_of_transposableP p h.1),
        lMap_swap_closedDescAt, transposeCode_progCode_of_transposableP q h.2, Semiformula.lMap_rel]
      congr 3
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        · congr 1; funext i; fin_cases i <;> rfl
        · show FirstOrder.Semiformula.rel _ (Semiterm.lMap swap ∘ ![#1, #0]) = _
          congr 1; funext i; fin_cases i <;> rfl
    | k₀, .diag _ _, _ => by
      rw [PD.Formula.transpose, templateAt_diag, templateAt_diag, LogicalConnective.HomClass.map_bot]
  /-- **τ on program codes, boxes included**: the code-level transposition of a program's code is the code of
  the engine's transposed program. -/
  theorem transposeCode_progCode_of_transposableP : ∀ p : PD.Prog, transposableP p = true →
      transposeCode (progCode p) = progCode p.transpose
    | .const a, _ => by simp [PD.Prog.transpose, transposeCode, actCode_swap]
    | .self, _ => by simp [PD.Prog.transpose, transposeCode]
    | .opp, _ => by simp [PD.Prog.transpose, transposeCode]
    | .bot p, h => by
      simp only [transposableP] at h
      simp [PD.Prog.transpose, transposeCode, transposeCode_progCode_of_transposableP p h]
    | .sim p q, h => by
      simp only [transposableP, Bool.and_eq_true] at h
      simp [PD.Prog.transpose, transposeCode, transposeCode_progCode_of_transposableP p h.1,
        transposeCode_progCode_of_transposableP q h.2]
    | .ite b a p q, h => by
      simp only [transposableP, Bool.and_eq_true] at h
      simp [PD.Prog.transpose, transposeCode, transposeCode_progCode_of_transposableP b h.1.1,
        transposeCode_progCode_of_transposableP p h.1.2, transposeCode_progCode_of_transposableP q h.2, actCode_swap]
    | .search k φ p q, h => by
      simp only [transposableP, Bool.and_eq_true] at h
      simp only [PD.Prog.transpose, progCode_search, transposeCode, revalue_search,
        transposeCode_progCode_of_transposableP p h.1.2, transposeCode_progCode_of_transposableP q h.2]
      unfold templateCodeAt
      rw [revalueTemplate_quote_sentence, lMap_swap_templateAt_of_transposableF (some k) φ h.1.1]
    | .tvote _ _ _ _, h => by simp [transposableP] at h
    | .sys _ _, h => by simp [transposableP] at h
    | .selfIdx _, h => by simp [transposableP] at h
end

/-- **τ on the six-variable templates, boxes included.** -/
theorem lMap_swap_template_of_transposableF : ∀ φ : PD.Formula, transposableF φ = true →
    Semiformula.lMap swap (template φ) = template φ.transpose
  | .plays p q a, h => by
    simp only [transposableF, Bool.and_eq_true] at h
    rw [PD.Formula.transpose, template_plays, template_plays]
    unfold progGraph
    simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
      lMap_swap_evalG, lMap_swap_progAux (transposeCode_progCode_of_transposableP p h.1),
      lMap_swap_progAux (transposeCode_progCode_of_transposableP q h.2)]
    congr 4
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · show Semiterm.lMap swap (cl (actT (actCode a))) = cl (actT (actCode a.swap))
          rw [lMap_swap_cl, lMap_swap_actT, actCode_swap]
  | .impl φ ψ, h => by
    simp only [transposableF, Bool.and_eq_true] at h
    rw [PD.Formula.transpose, template_impl, template_impl, LogicalConnective.HomClass.map_imply,
      lMap_swap_template_of_transposableF φ h.1, lMap_swap_template_of_transposableF ψ h.2]
  | .neg φ, h => by
    simp only [transposableF] at h
    rw [PD.Formula.transpose, template_neg, template_neg, LogicalConnective.HomClass.map_neg,
      lMap_swap_template_of_transposableF φ h]
  | .box k ψ, h => by
    simp only [transposableF] at h
    have hq : Semiformula.lMap swap (template13 ψ) = template13 ψ.transpose :=
      lMap_swap_templateAt_of_transposableF none ψ h
    rw [PD.Formula.transpose, template_box, template_box, progAux_self, progAux_opp]
    simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
      lMap_swap_guardCodeG, lMap_swap_lenProvG, lMap_swap_descF, Semiterm.lMap_bvar]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · congr 2
        · congr 1
          funext i
          fin_cases i
          · rfl
          · show Semiterm.lMap swap (cl (boxQuote (template13 ψ))) = cl (boxQuote (template13 ψ.transpose))
            rw [lMap_swap_cl_boxQuote, hq]
          · rfl
          · rfl
        · congr 1
          funext i
          fin_cases i
          · show Semiterm.lMap swap (cl (numTB k)) = cl (numTB k)
            exact lMap_swap_cl_numTB k
          · rfl
  | .eq p q, h => by
    simp only [transposableF, Bool.and_eq_true] at h
    rw [PD.Formula.transpose, template_eq, template_eq]
    unfold progGraph
    simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
      lMap_swap_progAux (transposeCode_progCode_of_transposableP p h.1), lMap_swap_closedDesc,
      transposeCode_progCode_of_transposableP q h.2, Semiformula.lMap_rel]
    congr 3
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      · congr 1; funext i; fin_cases i <;> rfl
      · show FirstOrder.Semiformula.rel _ (Semiterm.lMap swap ∘ ![#1, #0]) = _
        congr 1; funext i; fin_cases i <;> rfl
  | .diag _ _, _ => by
    rw [PD.Formula.transpose, template_diag, template_diag, LogicalConnective.HomClass.map_bot]

/-- **τ on template codes, boxes included.** -/
theorem revalueTemplate_templateCode_of_transposableF (φ : PD.Formula) (h : transposableF φ = true) :
    revalueTemplate 1 0 (templateCode φ) = templateCode φ.transpose := by
  unfold templateCode template13
  rw [revalueTemplate_quote_sentence, lMap_swap_templateAt_of_transposableF none φ h]

/-! ### τ on the realized sentences: the bridge, boxes included -/

/-- **The bridge, boxes included**: τ on the sentence of `φ` realized in the frame `(me, opp)` is the sentence of
`φ.transpose` realized in the transposed frame — the paper's `𝒯 Plays(π, π', a) = Plays(𝒯π, 𝒯π', 𝒯a)` for every
formula and every pair of players of the transposition fragment. -/
theorem lMap_swap_sentenceAt_of_transposableP {me opp : PD.Prog} (hme : transposableP me = true)
    (hopp : transposableP opp = true) (φ : PD.Formula) (hφ : transposableF φ = true) :
    Semiformula.lMap swap (sentenceAt me opp φ) = sentenceAt me.transpose opp.transpose φ.transpose := by
  unfold sentenceAt
  rw [Semiformula.lMap_subst, lMap_swap_template_of_transposableF φ hφ]
  congr 1
  funext i
  fin_cases i <;> simp [descriptionTerms, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta,
    transposeCode_progCode_of_transposableP me hme, transposeCode_progCode_of_transposableP opp hopp]

/-- The bridge on a play atom: `τ Plays(p, q, a) = Plays(τ p, τ q, τ a)` in the transposed frame. -/
theorem lMap_swap_sentenceAt_plays_of_transposableP {me opp p q : PD.Prog} (hme : transposableP me = true)
    (hopp : transposableP opp = true) (hp : transposableP p = true) (hq : transposableP q = true) (a : PD.Action) :
    Semiformula.lMap swap (sentenceAt me opp (.plays p q a)) =
      sentenceAt me.transpose opp.transpose (.plays p.transpose q.transpose a.swap) :=
  lMap_swap_sentenceAt_of_transposableP hme hopp (.plays p q a) (by simp [transposableF, hp, hq])

/-! ### What the quote denotes

Under the standard reading (`c_C ↦ 0`, `c_D ↦ 1`) the quote of `σ` is the code of `σ`: every box sentence
means in ℕ what it meant with the numeral quote. Under the swapped reading — the standard reading of the
transposed term — it is the code of the transposed `σ`. -/

lemma val_numTB (c : ℕ) : (numTB c).val (s := stdReadingNat) ![] Empty.elim = c := by
  unfold numTB
  rw [Semiterm.val_lMap, stdReadingNat_lMap_emb]
  exact val_binNumeralMeta c

lemma val_addT (t u : ClosedSemiterm LAct 0) :
    (addT t u).val (s := stdReadingNat) ![] Empty.elim =
      t.val (s := stdReadingNat) ![] Empty.elim + u.val (s := stdReadingNat) ![] Empty.elim := by
  unfold addT
  rw [Semiterm.val_func]
  rfl

lemma val_mulT (t u : ClosedSemiterm LAct 0) :
    (mulT t u).val (s := stdReadingNat) ![] Empty.elim =
      t.val (s := stdReadingNat) ![] Empty.elim * u.val (s := stdReadingNat) ![] Empty.elim := by
  unfold mulT
  rw [Semiterm.val_func]
  rfl

/-- **The quote denotes the code**, under the standard reading. -/
theorem val_boxQuote {n : ℕ} (σ : Semisentence LAct n) :
    (boxQuote σ).val (s := stdReadingNat) ![] Empty.elim = (⌜σ⌝ : ℕ) := by
  unfold boxQuote
  generalize (⌜Semiformula.lMap swap σ⌝ : ℕ) = c'
  generalize (⌜σ⌝ : ℕ) = c
  rcases lt_trichotomy c c' with h | h | h
  · rw [if_pos h, val_addT, val_mulT, val_numTB, val_numTB, val_cterm_C]; simp
  · subst h; simp [val_numTB]
  · rw [if_neg (lt_asymm h), if_pos h, val_addT, val_mulT, val_numTB, val_numTB, val_cterm_D]
    omega

/-- **The transposed quote denotes the code of the transposed formula**: the value of the quote under the
swapped reading. -/
theorem val_lMap_swap_boxQuote {n : ℕ} (σ : Semisentence LAct n) :
    (Semiterm.lMap swap (boxQuote σ)).val (s := stdReadingNat) ![] Empty.elim = (⌜Semiformula.lMap swap σ⌝ : ℕ) := by
  rw [lMap_swap_boxQuote, val_boxQuote]

end ArithS
