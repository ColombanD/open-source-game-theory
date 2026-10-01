import ArithS.Tau.NeverFits
import ArithS.Tau.ClosedWatch

/-!
# ArithS.Tau.NeverFitsSys — a `.self`-guard over a watch that freezes a budget-carrying SYSTEM never fits (Phase 3e)

**The finding (2026-10-01, Phase 3e).** Route (c) made generic (`Agents/CodeTermAbs.lean`) abstracts the node's
budget in the description of a closed program by descending through `bot`/`sim`/`ite`/`search` nodes — and NOT into
a SYSTEM (`codeTermMetaAbs_sys`: a `pSys d i` is described verbatim, by design, for the member-slot equation of
`Agents/SysTemplate.lean`). The claim "no paper-zoo guard names a closed system" in that module's docstring is false
for ONE theorem bit of the Phase-3 table: `dimcid × ebot`. τ(EBot)'s instance seeing DIMCID has a THIRD watch, on
DIMCID's instance at the MIRROR, which is the closed system `.sys [dim 1, mm 0] 0` (`Entangled/Base.inst_dimcid_mirror`)
with the `.search k` member `dim 1 k`. So the stored template of DIMCID's instance at τ(EBot),
`templateCodeAt (dimG (inst ebot dimcid)) k`, still writes `binNumeral k` (inside the verbatim system), its code is
`≥ binNumeral k` (`binNumeral_le_templateCodeAt_selfBot`), DIMCID's own description — written by the `.self`
antecedent — has a numeral of more than `k` bits, and the guard sentence is LONGER than `k`: never found, at every
budget (`selfBot_sys_guard_not_found`, `Tau/NeverFits.lean`'s argument one level down, on the abstracted template).

Consequence: under the PRESENT coding `dimcid × ebot` is **C at every budget** (`dimcid_ebot_C`) — the ENGINE's
value, not the `D≠` of the table in `SPRIME_SOURCE_OF_TRUTH.md` §3. The table's value needs the abstraction to
descend into systems (the "(α) upgrade" of `ARITH_TRAPS.md` §4b: a code-level `codeTermAbs` in `Guard`/`SysClose`).
The bit is therefore NOT stated in `Rows/DIMCID.lean` (neither side is forced); this module records what the
kernel proves about it today. Floor bits are unaffected (`cimcic/dupoc/prudent/maxconfidence/minconfidence × ebot`
are `‡` cells: their hinges fail for the same reason, which is the engine-side value).

* §1 `OccB` — a closed ℒₒᵣ-term occurs (shifted) in a one-variable term; `TOccC_of_OccB` — it then occurs, as a
  closed `LAct`-term, in the abstracted description after the budget slot is filled;
* §2 `HasSysC k` — a code reaches a system with a `pSearch k` member through `bot`/`sim`/`ite` nodes (closed under
  the code-level τ); `occB_of_hasSysC` — the abstracted description of such a code writes a closed term of code
  `≥ binNumeral k`, at ANY node budget;
* §3 the stored template of a `.self`-guard over such a program, and its transposition, have codes `≥ binNumeral k`;
* §4 the obstruction, and `dimcid × ebot`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. A closed term inside a one-variable description -/

/-- The closed term `u` occurs, shifted, in the one-variable term. -/
inductive OccB (u : ClosedSemiterm ℒₒᵣ 0) : Semiterm ℒₒᵣ Empty 1 → Prop
  | here : OccB u (Rew.bShift u)
  | func {k : ℕ} (f : (ℒₒᵣ).Func k) (v : Fin k → Semiterm ℒₒᵣ Empty 1) (j : Fin k) :
      OccB u (v j) → OccB u (Semiterm.func f v)

lemma OccB.succT1 {u : ClosedSemiterm ℒₒᵣ 0} {t : Semiterm ℒₒᵣ Empty 1} (h : OccB u t) : OccB u (succT1 t) :=
  .func _ _ 0 h

lemma OccB.ppairL {u : ClosedSemiterm ℒₒᵣ 0} {s : Semiterm ℒₒᵣ Empty 1} (t : Semiterm ℒₒᵣ Empty 1) (h : OccB u s) :
    OccB u (ppairT1 s t) :=
  .func _ _ 0 (.func _ _ 0 (.func _ _ 0 h))

lemma OccB.ppairR {u : ClosedSemiterm ℒₒᵣ 0} (s : Semiterm ℒₒᵣ Empty 1) {t : Semiterm ℒₒᵣ Empty 1} (h : OccB u t) :
    OccB u (ppairT1 s t) :=
  .func _ _ 1 h

/-- An occurrence in the one-variable ℒₒᵣ-term is an occurrence of the closed `LAct`-term in the description with
the budget slot filled by any term. -/
theorem TOccC_of_OccB {u : ClosedSemiterm ℒₒᵣ 0} {t : Semiterm ℒₒᵣ Empty 1} (h : OccB u t) {n : ℕ}
    (b : Semiterm LAct Empty n) :
    TOccC (Semiterm.lMap emb u) (Rew.subst ![b] (Semiterm.lMap emb t)) := by
  induction h with
  | here => rw [Semiterm.lMap_bShift, subst_bShift_cl]; exact .here
  | func f v j _ ih => rw [Semiterm.lMap_func, Rew.func]; exact .func _ _ j ih

lemma quote_emb_lMap_emb_closed (u : ClosedSemiterm ℒₒᵣ 0) :
    (⌜(Rew.emb (Semiterm.lMap emb u) : SyntacticSemiterm LAct 0)⌝ : ℕ) = ⌜u⌝ := by
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def]

/-! ### 2. A system with a budget-carrying member, inside a watch -/

/-- The member list carries a member with a `pSearch k` leaf. -/
inductive ListHasSearch (k : ℕ) : ℕ → Prop
  | head {e : ℕ} (r : ℕ) : HasSearchC k e → ListHasSearch k (pCons e r)
  | tail (e : ℕ) {r : ℕ} : ListHasSearch k r → ListHasSearch k (pCons e r)

/-- The code reaches, through `bot`/`sim`/`ite` nodes, a SYSTEM with a budget-`k` member. -/
inductive HasSysC (k : ℕ) : ℕ → Prop
  | sys {d : ℕ} (i : ℕ) : ListHasSearch k d → HasSysC k (pSys d i)
  | bot {p : ℕ} : HasSysC k p → HasSysC k (pBot p)
  | simL {p : ℕ} (q : ℕ) : HasSysC k p → HasSysC k (pSim p q)
  | simR (p : ℕ) {q : ℕ} : HasSysC k q → HasSysC k (pSim p q)
  | iteB {b : ℕ} (a p q : ℕ) : HasSysC k b → HasSysC k (pIte b a p q)
  | iteP (b a : ℕ) {p : ℕ} (q : ℕ) : HasSysC k p → HasSysC k (pIte b a p q)
  | iteQ (b a p : ℕ) {q : ℕ} : HasSysC k q → HasSysC k (pIte b a p q)

theorem ListHasSearch.revalue {k : ℕ} (u w : ℕ) {d : ℕ} (h : ListHasSearch k d) : ListHasSearch k (revalue u w d) := by
  induction h with
  | head r h => rw [revalue_cons]; exact .head _ (h.revalue u w)
  | tail e _ ih => rw [revalue_cons]; exact .tail _ ih

/-- τ on codes keeps the system and its budget leaf. -/
theorem HasSysC.revalue {k : ℕ} (u w : ℕ) {y : ℕ} (h : HasSysC k y) : HasSysC k (revalue u w y) := by
  induction h with
  | sys i h => rw [revalue_sys]; exact .sys _ (h.revalue u w)
  | bot _ ih => rw [revalue_bot]; exact .bot ih
  | simL q _ ih => rw [revalue_sim]; exact .simL _ ih
  | simR p _ ih => rw [revalue_sim]; exact .simR _ ih
  | iteB a p q _ ih => rw [revalue_ite]; exact .iteB _ _ _ ih
  | iteP b a q _ ih => rw [revalue_ite]; exact .iteP _ _ _ ih
  | iteQ b a p _ ih => rw [revalue_ite]; exact .iteQ _ _ _ ih

theorem HasSysC.canonical_bot {k : ℕ} {y : ℕ} (h : HasSysC k y) : HasSysC k (canonical (pBot y)) := by
  rw [canonical_pBot]
  refine .bot ?_
  unfold canonical
  split_ifs
  · exact h
  · exact h.revalue 1 0

theorem binNumeral_le_codeTerm_of_listHas {k : ℕ} {d : ℕ} (h : ListHasSearch k d) : binNumeral k ≤ codeTerm d := by
  induction h with
  | head r h =>
    rw [codeTerm_cons]
    exact le_trans (binNumeral_le_codeTerm_of_hasSearchC h)
      (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))
  | tail e _ ih =>
    rw [codeTerm_cons]
    exact le_trans ih (le_trans (le_ppairTerm_right _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))

/-- **The abstracted description of a code with a budget-carrying system writes a closed term of code
`≥ binNumeral k`, at any node budget**: the abstraction does not descend into the system. -/
theorem occB_of_hasSysC {k : ℕ} {y : ℕ} (h : HasSysC k y) (K : ℕ) :
    ∃ u : ClosedSemiterm ℒₒᵣ 0, OccB u (codeTermMetaAbs K y) ∧ binNumeral k ≤ (⌜u⌝ : ℕ) := by
  induction h with
  | @sys d i h =>
    refine ⟨codeTermMeta (pSys d i), by rw [codeTermMetaAbs_sys]; exact .here, ?_⟩
    rw [quote_codeTermMeta_nat, codeTerm_sys]
    exact le_trans (binNumeral_le_codeTerm_of_listHas h)
      (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))
  | bot _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, by rw [codeTermMetaAbs_bot]; exact (hu.ppairR _).succT1, hb⟩
  | simL q _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, by rw [codeTermMetaAbs_sim]; exact ((hu.ppairL _).ppairR _).succT1, hb⟩
  | simR p _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, by rw [codeTermMetaAbs_sim]; exact ((hu.ppairR _).ppairR _).succT1, hb⟩
  | iteB a p q _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, by rw [codeTermMetaAbs_ite]; exact ((hu.ppairL _).ppairR _).succT1, hb⟩
  | iteP b a q _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, by rw [codeTermMetaAbs_ite]; exact ((((hu.ppairL _).ppairR _).ppairR _).ppairR _).succT1, hb⟩
  | iteQ b a p _ ih =>
    obtain ⟨u, hu, hb⟩ := ih
    exact ⟨u, by rw [codeTermMetaAbs_ite]; exact ((((hu.ppairR _).ppairR _).ppairR _).ppairR _).succT1, hb⟩

/-! ### 3. The stored template -/

/-- `descF X T U W` writes whatever its canonical-numeral slot `T` writes. -/
lemma FOccC_descF_of_T {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) {u : ClosedSemiterm LAct 0} (h : TOccC u T) :
    FOccC u (descF X T U W) := by
  unfold descF
  exact .exs (.andL _ (.rel _ _ 1 h))

/-- The stored (abstracted) description of a code whose canonical form has a budget-carrying system writes a
`swap`-fixed closed term of code `≥ binNumeral k`. -/
theorem FOccC_closedDescAt_of_hasSysC {k K c : ℕ} (h : HasSysC k (canonical c)) :
    ∃ u : ClosedSemiterm LAct 0, FOccC u (closedDescAt (some K) c) ∧
      binNumeral k ≤ (⌜(Rew.emb u : SyntacticSemiterm LAct 0)⌝ : ℕ) ∧ Semiterm.lMap swap u = u := by
  obtain ⟨u₀, ho, hb⟩ := occB_of_hasSysC h K
  refine ⟨Semiterm.lMap emb u₀, ?_, by rw [quote_emb_lMap_emb_closed]; exact hb, term_lMap_swap_emb _⟩
  unfold closedDescAt
  rw [canonicalSlot_some]
  unfold canonicalAbs
  exact FOccC_descF_of_T _ _ _ _ (TOccC_of_OccB ho _)

/-- The `.plays` shape writes what its second description writes. -/
lemma FOccC_plAt_right (D₁ : Semisentence LAct 14) {D₂ : Semisentence LAct 14} (a : ℕ) {u : ClosedSemiterm LAct 0}
    (h : FOccC u D₂) : FOccC u (plAt D₁ D₂ a) := by
  unfold plAt Rewriting.subst
  exact .exs (.exs (.exs (.andR _ (.andL _ (FOccC_rew h _)))))

/-- **The stored template of a `.self`-guard over a program that freezes a budget-carrying system has code
`≥ binNumeral k`, and so does its code-level transposition** — budget abstraction notwithstanding. -/
theorem binNumeral_le_templateCodeAt_selfBot {k : ℕ} {X : PD.Prog} (hX : HasSysC k (canonical (progCode (.bot X))))
    (hns : noSelfIdxP (.bot X) = true) (a : PD.Action) (ψ : PD.Formula) :
    binNumeral k ≤ templateCodeAt (.impl (.plays .self (.bot X) a) ψ) k ∧
    binNumeral k ≤ revalueTemplate 1 0 (templateCodeAt (.impl (.plays .self (.bot X) a) ψ) k) := by
  obtain ⟨u, hO, hb, hsw⟩ := FOccC_closedDescAt_of_hasSysC (K := k) hX
  have hA : FOccC u (templateAt (.plays .self (.bot X) a) (some k)) := by
    rw [templateAt_plays_eq, progGraphAt_self, progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns)]
    exact FOccC_plAt_right _ _ hO
  have hA' := FOccC_lMap_swap hA
  rw [hsw] at hA'
  constructor
  · unfold templateCodeAt
    rw [templateAt_impl, Semiformula.imp_eq]
    exact le_trans hb (le_quote_sentence_of_FOccC (.orL _ (FOccC_neg hA)))
  · unfold templateCodeAt
    rw [revalueTemplate_quote_sentence, templateAt_impl, LogicalConnective.HomClass.map_imply, Semiformula.imp_eq]
    exact le_trans hb (le_quote_sentence_of_FOccC (.orL _ (FOccC_neg hA')))

/-! ### 4. The obstruction, and `dimcid × ebot` -/

/-- **The guard of a `.self`-guard over a program that freezes a budget-carrying system, consulted by the bot-wrapped
searcher that stores the ABSTRACTED template, is never found within `k`** — against any opponent code. -/
theorem selfBot_sys_guard_not_found {k : ℕ} {X : PD.Prog} (hX : HasSysC k (canonical (progCode (.bot X))))
    (hnsX : noSelfIdxP (.bot X) = true) (a : PD.Action) {ψ : PD.Formula}
    (hns : noSelfIdxF (.impl (.plays .self (.bot X) a) ψ) = true) (p q opp : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot X) a) ψ))
      (pBot (pSearch k (templateCodeAt (.impl (.plays .self (.bot X) a) ψ) k) p q)) opp) := by
  intro hl
  obtain ⟨h1, h2⟩ := binNumeral_le_templateCodeAt_selfBot hX hnsX a ψ
  rw [← quote_sentenceAtC _ _ _ hns, lenBox_nat] at hl
  have hle := formulaLenMeta_le_of_lenBoxNat hl
  rw [formulaLenMeta_emb_sentenceAtC_impl] at hle
  have hA := size_canonical_le_formulaLenMeta_sentenceAtC_self
    (pBot (pSearch k (templateCodeAt (.impl (.plays .self (.bot X) a) ψ) k) p q)) opp (.bot X) a
  have hS : k + 2 ≤ Nat.size (canonical (pBot (pSearch k (templateCodeAt (.impl (.plays .self (.bot X) a) ψ) k) p q))) := by
    rw [canonical_pBot]
    refine le_trans (size_binNumeral_ge k) (Nat.size_le_size ?_)
    refine le_trans ?_ (by unfold pBot; exact le_trans (nppair_le_right _ _) (Nat.le_succ _))
    unfold canonical
    split_ifs
    · exact le_trans h1 (le_pSearch _ _ _ _)
    · rw [transposeCode, revalue_search]; exact le_trans h2 (le_pSearch _ _ _ _)
  omega

/-- DIMCID's instance at the mirror is a system with the budget-`k` member `dim 1 k`. -/
lemma hasSysC_dimcid_mirror (k : ℕ) : HasSysC k (instCode k .dimcid .mirror) := by
  unfold instCode
  rw [inst_dimcid_mirror, progCode_sys2]
  refine .sys _ (.head _ ?_)
  rw [show dim 1 k = .search k (entDimG 1) (.const .D) (.const .C) from rfl, progCode_search]
  exact .search _ _ _

/-- τ(EBot)'s instance seeing DIMCID reaches that system through its third watch. -/
lemma hasSysC_ebot_dimcid (k : ℕ) : HasSysC k (instCode k .ebot .dimcid) := by
  rw [instCode_ebot]
  exact .iteQ _ _ _ (.iteQ _ _ _ (.iteB _ _ _ (.simL _ (.bot (hasSysC_dimcid_mirror k)))))

theorem instCode_dimcid_ebot' (k : ℕ) : instCode k .dimcid .ebot =
    pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .ebot .dimcid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_ebot]; simp [actCode]

/-- **`dimcid × ebot` is C at EVERY budget under the present coding** — the ENGINE's value, NOT the `D≠` of the
Phase-3 table: DIMCID's guard over τ(EBot)'s instance is longer than its budget (the instance freezes the system
`inst dimcid mirror`, which budget abstraction does not enter), so it is never found and the else-branch plays C.
Not a row slot (`Rows/DIMCID.lean`): the table's value needs the abstraction to descend into systems. -/
theorem dimcid_ebot_C (k : ℕ) : bitPlays k .dimcid .ebot .C := by
  have hX : HasSysC k (canonical (progCode (.bot (inst (tauZoo k) .ebot .dimcid)))) := by
    rw [progCode_bot_inst]; exact (hasSysC_ebot_dimcid k).canonical_bot
  have hn := selfBot_sys_guard_not_found hX rfl .C (ψ := .plays (.bot (inst (tauZoo k) .ebot .dimcid)) .self .D) rfl
    (pConst 1) (pConst 0)
    (pBot (pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .ebot .dimcid)) k) (pConst 1) (pConst 0)))
  exact bitPlays_of_eq (instCode_dimcid_ebot' k) ⟨_, search_else_at _ hn (const_play 0 _ _ _) rfl⟩

end ArithS.Tau
