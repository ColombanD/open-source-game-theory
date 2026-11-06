import ArithS.Tau.NeverFits
import ArithS.Tau.ClosedWatch

/-!
# ArithS.Tau.NeverFitsSys — a `.self`-guard over a watch that freezes a budget-carrying SYSTEM, stored VERBATIM, never fits

**History.** Phase 3e (2026-10-01) found ONE bit of the paper table that route (c) made generic (Phase 2c) did not
recover: `dimcid × ebot`. τ(EBot)'s instance seeing DIMCID has a THIRD watch, on DIMCID's instance at the MIRROR,
the closed system `.sys [dim 1, mm 0] 0` (`Entangled/Base.inst_dimcid_mirror`) with the `.search k` member
`dim 1 k`; Phase 2c's abstraction did not descend into a system, so the stored template of `inst dimcid ebot`
still wrote `binNumeral k`, DIMCID's own description had a numeral of more than `k` bits, and the guard was
never found — the bit was C at every budget, the ENGINE's value, against the table's `D≠`.

**Status after Phase 2d (decision (α), 2026-10-02).** The abstraction DESCENDS into systems
(`Agents/CodeTermAbs.codeTermMetaAbs_sys`; the closer takes the node's budget, `sysCloseTemplateAt`), the stored
template of `inst dimcid ebot` is a constant, and the bit is **D** (`Tau/ClosedWatch3.dimcid_ebot_D`), a row slot.
The obstruction is a property of a searcher that stores the system's description VERBATIM. The statements below
are kept as theorems about the explicit code `pBot (pSearch k' (templateCode φ) p q)` — the searcher storing the
UNABSTRACTED template — exactly as `Tau/NeverFits.lean` was restated in Phase 2c; they cover the case that file's
`HasSearchP` does not: the only budget-carrying part of the frozen program may sit INSIDE a system (`HasSysC`).
The tau corollary carries the hypothesis `instCode k .dimcid T = pSearch k (templateCode …) …`, which no compiled
instance satisfies (they store `templateCodeAt … k`); `hasSysC_ebot_dimcid` records that τ(EBot)'s instance at
DIMCID does have the system shape — only the storage hypothesis fails.

* §1 `HasSysC k` — a code reaches a system with a `pSearch k` member through `bot`/`sim`/`ite` nodes (closed under
  the code-level τ); `binNumeral_le_codeTerm_of_hasSysC` — its VERBATIM structural term is `≥ binNumeral k`;
* §2 the unabstracted template of a `.self`-guard over such a program, and its transposition, have codes
  `≥ binNumeral k`;
* §3 the obstruction, and the (vacuous on compiled instances) tau corollary.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. A system with a budget-carrying member, inside a watch -/

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

/-- **The VERBATIM structural term of a code with a budget-carrying system is `≥ binNumeral k`.** -/
theorem binNumeral_le_codeTerm_of_hasSysC {k : ℕ} {y : ℕ} (h : HasSysC k y) : binNumeral k ≤ codeTerm y := by
  induction h with
  | @sys d i h =>
    rw [codeTerm_sys]
    exact le_trans (binNumeral_le_codeTerm_of_listHas h)
      (le_trans (le_ppairTerm_left _ _) (le_trans (le_ppairTerm_right _ _) (le_qqAdd_left _ _)))
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

/-- The code of the canonical numeral term, as a syntactic term, is `≥ binNumeral k`. -/
theorem binNumeral_le_quote_emb_canonicalMeta_of_hasSysC {k c : ℕ} (h : HasSysC k (canonical c)) :
    binNumeral k ≤ (⌜(Rew.emb (canonicalMeta c) : SyntacticSemiterm LAct 0)⌝ : ℕ) := by
  unfold canonicalMeta
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_codeTermMeta_nat]
  exact binNumeral_le_codeTerm_of_hasSysC h

/-! ### 2. The unabstracted template -/

/-- **The UNABSTRACTED template of a `.self`-guard over a program that freezes a budget-carrying system has code
`≥ binNumeral k`, and so does its code-level transposition** (`Tau/NeverFits.binNumeral_le_templateCode_selfBot`
with the budget inside a system). -/
theorem binNumeral_le_templateCode_selfBot_sys {k : ℕ} {X : PD.Prog} (hX : HasSysC k (canonical (progCode (.bot X))))
    (a : PD.Action) {ψ : PD.Formula} (hns : noSelfIdxF (.impl (.plays .self (.bot X) a) ψ) = true) :
    binNumeral k ≤ templateCode (.impl (.plays .self (.bot X) a) ψ) ∧
    binNumeral k ≤ revalueTemplate 1 0 (templateCode (.impl (.plays .self (.bot X) a) ψ)) := by
  have hb := binNumeral_le_quote_emb_canonicalMeta_of_hasSysC hX
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

/-! ### 3. The obstruction, and the tau corollary -/

/-- **The guard of a `.self`-guard over a program that freezes a budget-carrying system, consulted by the bot-wrapped
searcher that stores the UNABSTRACTED template, at ANY search budget, is never found within `k`** — against any
opponent code. -/
theorem selfBot_sys_guard_not_found {k : ℕ} {X : PD.Prog} (hX : HasSysC k (canonical (progCode (.bot X))))
    (a : PD.Action) {ψ : PD.Formula}
    (hns : noSelfIdxF (.impl (.plays .self (.bot X) a) ψ) = true) (k' : ℕ) (p q opp : ℕ) :
    ¬ LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot X) a) ψ))
      (pBot (pSearch k' (templateCode (.impl (.plays .self (.bot X) a) ψ)) p q)) opp) := by
  intro hl
  obtain ⟨h1, h2⟩ := binNumeral_le_templateCode_selfBot_sys hX a hns
  rw [← quote_sentenceAtC _ _ _ hns, lenBox_nat] at hl
  have hle := formulaLenMeta_le_of_lenBoxNat hl
  rw [formulaLenMeta_emb_sentenceAtC_impl] at hle
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

/-- τ(EBot)'s instance seeing DIMCID has the system shape, in canonical form (the hypothesis `hX` of the obstruction). -/
lemma hasSysC_canonical_bot_ebot_dimcid (k : ℕ) :
    HasSysC k (canonical (progCode (.bot (inst (tauZoo k) .ebot .dimcid)))) := by
  rw [progCode_bot_inst]; exact (hasSysC_ebot_dimcid k).canonical_bot

/-- **τ(DIMCID) at a hypothesis whose instance seeing it freezes a budget-carrying system: C** — IF the instance
stored the UNABSTRACTED template (`hc`). No compiled instance does: since Phase 2c `progCode` stores
`templateCodeAt … k`, and since Phase 2d that template is a constant even when the frozen program contains a
system — `dimcid × ebot` is D (`Tau/ClosedWatch3.dimcid_ebot_D`). -/
theorem dimcid_selfBot_sys_C {k : ℕ} {T : Tmpl}
    (hc : instCode k .dimcid T = pSearch k (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) .C)
      (.plays (.bot (inst (tauZoo k) T .dimcid)) .self .D))) (pConst 1) (pConst 0))
    (hX : HasSysC k (canonical (progCode (.bot (inst (tauZoo k) T .dimcid)))))
    (hns : noSelfIdxF (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid)) .C)
      (.plays (.bot (inst (tauZoo k) T .dimcid)) .self .D)) = true) :
    bitPlays k .dimcid T .C := by
  have hn := selfBot_sys_guard_not_found hX .C hns k (pConst 1) (pConst 0) (pBot (instCode k .dimcid T))
  rw [hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else _ hn (const_play 0 _ _ _) hns⟩

end ArithS.Tau
