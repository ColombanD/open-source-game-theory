import ArithS.Agents.Code

/-!
# ArithS.Agents.SysTemplate — the member slots read the system: `sysCloseTemplate` is the engine's `Formula.sysClose`

The last item of Phase 2 of `SPRIME_SOURCE_OF_TRUTH.md` (§2.5, 2026-10-01). A system member's guard names its
partner through the pronoun `.bot (.selfIdx j)`; the engine's `.sys` clause closes the member with
`Prog.sysClose defs` (`.selfIdx j ↦ .sys defs j`) before it runs, and the arithmetized evaluator does the same
on codes (`sysCloseCode`, whose `pSearch` clause closes the stored template by `sysCloseTemplate d`: the member
slots `#7..#12` filled with the closed descriptions of `pSys d 0`, `pSys d 1`). This file proves that the two
closers agree on the compiled members:

* **`template13_sysClose`** (meta): filling the member slots of `template13 φ` with the description triples of
  the members IS `template13 (φ.sysClose defs)` — LITERALLY, the way `template_subst` is literal — for every
  member guard (`memberGuardF`: atoms over `.self`/`.opp`/the pronouns `.bot (.selfIdx j)`, `j ∈ {0, 1}`, and
  closed pronoun-free programs; no `.box`; no pronoun on the frozen right-hand side of an `.eq`). The pronoun
  clause of `progAux13` matches the closed description of `.bot (.sys defs j)` because `pBot` commutes with
  `canonical` and fixes the re-valuation terms (`pBotTerm_canonicalMeta`, `revalueUMeta_pBot`, `revalueWMeta_pBot`).
* **`templateCode_sysClose`** (codes): `sysCloseTemplate (progListCode defs) (templateCode φ) = templateCode
  (φ.sysClose defs)`.
* **`progCode_sysClose_member`**: `progCode (p.sysClose defs) = sysCloseCode (progListCode defs) (progCode p)` for
  every program whose search guards are member guards (`memberP`) — the compiled members of `Tau/Spec.lean`.

The two shapes `sysGo` emits — `.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a` and `.impl (.plays .self
(.bot (.selfIdx j)) a) (.plays (.bot (.selfIdx j)) .self a')` — are member guards by computation; the closed
third-party probes `.bot (instAt …)` of a member's other stages are `noSelfIdxP` (a `.sys` binds its own
pronouns) and are fixed by the closer at the code level (`progCode_sysClose_of_noSelfIdxP`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### The code-level fixpoint: a pronoun-free program is fixed by the closer -/

lemma sysClose_ne_self {p : PD.Prog} (h : p ≠ .self) (defs : PD.ProgList) : p.sysClose defs ≠ .self := by
  cases p <;> first | exact absurd rfl h | simp [PD.Prog.sysClose]

lemma sysClose_ne_opp {p : PD.Prog} (h : p ≠ .opp) (defs : PD.ProgList) : p.sysClose defs ≠ .opp := by
  cases p <;> first | exact absurd rfl h | simp [PD.Prog.sysClose]

lemma sysClose_ne_selfIdx (p : PD.Prog) (defs : PD.ProgList) (j : ℕ) : p.sysClose defs ≠ .selfIdx j := by
  cases p <;> simp [PD.Prog.sysClose]

lemma pronounP_bot_of_ne {q : PD.Prog} (h0 : q ≠ .selfIdx 0) (h1 : q ≠ .selfIdx 1) : pronounP (.bot q) = false := by
  cases q
  case selfIdx j =>
    rcases j with _ | _ | j
    · exact absurd rfl h0
    · exact absurd rfl h1
    · rfl
  all_goals rfl

lemma pronounP_sysClose {p : PD.Prog} (hp : noSelfIdxP p = true) (defs : PD.ProgList) :
    pronounP (p.sysClose defs) = false := by
  cases p
  case selfIdx j => simp [noSelfIdxP] at hp
  case bot q =>
    show pronounP (.bot (q.sysClose defs)) = false
    exact pronounP_bot_of_ne (sysClose_ne_selfIdx q defs 0) (sysClose_ne_selfIdx q defs 1)
  all_goals rfl

mutual
  /-- A pronoun-free program's code is fixed by the closer (its frozen `.diag` bodies are not read). -/
  theorem progCode_sysClose_of_noSelfIdxP : ∀ (p : PD.Prog) (defs : PD.ProgList), noSelfIdxP p = true →
      progCode (p.sysClose defs) = progCode p
    | .const _, _, _ => rfl
    | .self, _, _ => rfl
    | .opp, _, _ => rfl
    | .bot p, defs, h => by
      simp only [PD.Prog.sysClose, progCode_bot, progCode_sysClose_of_noSelfIdxP p defs h]
    | .sim p q, defs, h => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.sysClose, progCode_sim, progCode_sysClose_of_noSelfIdxP p defs h.1,
        progCode_sysClose_of_noSelfIdxP q defs h.2]
    | .ite b _ p q, defs, h => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.sysClose, progCode_ite, progCode_sysClose_of_noSelfIdxP b defs h.1.1,
        progCode_sysClose_of_noSelfIdxP p defs h.1.2, progCode_sysClose_of_noSelfIdxP q defs h.2]
    | .search k φ p q, defs, h => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.sysClose, progCode_search, progCode_sysClose_of_noSelfIdxP p defs h.1.2,
        progCode_sysClose_of_noSelfIdxP q defs h.2]
      unfold templateCodeAt
      rw [templateAt_sysClose_of_noSelfIdxF (some k) φ defs h.1.1]
    | .tvote _ _ p q, defs, h => by
      simp only [noSelfIdxP, Bool.and_eq_true] at h
      simp only [PD.Prog.sysClose, progCode_tvote, progCode_sysClose_of_noSelfIdxP p defs h.1,
        progCode_sysClose_of_noSelfIdxP q defs h.2]
    | .sys _ _, _, _ => rfl
    | .selfIdx _, _, h => by simp [noSelfIdxP] at h
  /-- A pronoun-free formula's thirteen-variable template (at any node budget) is fixed by the closer. -/
  theorem templateAt_sysClose_of_noSelfIdxF : ∀ (k₀ : Option ℕ) (φ : PD.Formula) (defs : PD.ProgList), noSelfIdxF φ = true →
      templateAt (φ.sysClose defs) k₀ = templateAt φ k₀
    | k₀, .plays p q a, defs, h => by
      simp only [noSelfIdxF, Bool.and_eq_true] at h
      rw [PD.Formula.sysClose, templateAt_plays, templateAt_plays, progGraphAt_sysClose_of_noSelfIdxP k₀ p defs h.1,
        progGraphAt_sysClose_of_noSelfIdxP k₀ q defs h.2]
    | k₀, .impl φ ψ, defs, h => by
      simp only [noSelfIdxF, Bool.and_eq_true] at h
      rw [PD.Formula.sysClose, templateAt_impl, templateAt_impl, templateAt_sysClose_of_noSelfIdxF k₀ φ defs h.1,
        templateAt_sysClose_of_noSelfIdxF k₀ ψ defs h.2]
    | k₀, .neg φ, defs, h => by
      simp only [noSelfIdxF] at h
      rw [PD.Formula.sysClose, templateAt_neg, templateAt_neg, templateAt_sysClose_of_noSelfIdxF k₀ φ defs h]
    | k₀, .box k ψ, defs, h => by
      simp only [noSelfIdxF] at h
      rw [PD.Formula.sysClose, templateAt_box, templateAt_box]
      unfold templateCode template13
      rw [templateAt_sysClose_of_noSelfIdxF none ψ defs h]
    | k₀, .eq p q, defs, h => by
      simp only [noSelfIdxF, Bool.and_eq_true] at h
      rw [PD.Formula.sysClose, templateAt_eq, templateAt_eq, progGraphAt_sysClose_of_noSelfIdxP k₀ p defs h.1,
        progCode_sysClose_of_noSelfIdxP q defs h.2]
    | k₀, .diag _ _, _, _ => by rw [PD.Formula.sysClose, templateAt_diag, templateAt_diag]
  /-- The frame description of a pronoun-free program is fixed by the closer. -/
  theorem progGraphAt_sysClose_of_noSelfIdxP : ∀ (k₀ : Option ℕ) (p : PD.Prog) (defs : PD.ProgList), noSelfIdxP p = true →
      progGraphAt k₀ (p.sysClose defs) = progGraphAt k₀ p
    | _, .self, _, _ => rfl
    | _, .opp, _, _ => rfl
    | k₀, .const a, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sysClose_of_noSelfIdxP (.const a) defs h]
    | k₀, .bot p, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP h), progCode_sysClose_of_noSelfIdxP (.bot p) defs h]
    | k₀, .sim p q, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sysClose_of_noSelfIdxP (.sim p q) defs h]
    | k₀, .ite b a p q, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sysClose_of_noSelfIdxP (.ite b a p q) defs h]
    | k₀, .search k φ p q, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sysClose_of_noSelfIdxP (.search k φ p q) defs h]
    | k₀, .tvote v θ p q, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sysClose_of_noSelfIdxP (.tvote v θ p q) defs h]
    | k₀, .sys d i, defs, h => by
      unfold progGraphAt
      rw [progAuxAt_of_ne _ (sysClose_ne_self (by simp) defs) (sysClose_ne_opp (by simp) defs) (pronounP_sysClose h defs),
        progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sysClose_of_noSelfIdxP (.sys d i) defs h]
    | _, .selfIdx _, _, h => by simp [noSelfIdxP] at h
end

/-- The unabstracted instance (today's name). -/
theorem template13_sysClose_of_noSelfIdxF (φ : PD.Formula) (defs : PD.ProgList) (h : noSelfIdxF φ = true) :
    template13 (φ.sysClose defs) = template13 φ := templateAt_sysClose_of_noSelfIdxF none φ defs h

theorem progGraph13_sysClose_of_noSelfIdxP (p : PD.Prog) (defs : PD.ProgList) (h : noSelfIdxP p = true) :
    progGraph13 (p.sysClose defs) = progGraph13 p := progGraphAt_sysClose_of_noSelfIdxP none p defs h

/-! ### Member guards -/

/-- A program allowed in a member guard's atom: a pronoun shape or a pronoun-free program (`.self`/`.opp`
included). -/
def memberAtomP (p : PD.Prog) : Bool := pronounP p || noSelfIdxP p

/-- The member-guard fragment: atoms over `memberAtomP` programs, `.impl`/`.neg`, no `.box`; the frozen
right-hand side of an `.eq` is pronoun-free (it is described by its closed code on both sides). -/
def memberGuardF : PD.Formula → Bool
  | .plays p q _ => memberAtomP p && memberAtomP q
  | .impl φ ψ => memberGuardF φ && memberGuardF ψ
  | .neg φ => memberGuardF φ
  | .box _ _ => false
  | .eq p q => memberAtomP p && noSelfIdxP q
  | .diag _ _ => true

/-- A compiled member: every search guard is a member guard. -/
def memberP : PD.Prog → Bool
  | .const _ => true
  | .self => true
  | .opp => true
  | .bot p => memberP p
  | .sim p q => memberP p && memberP q
  | .ite b _ p q => memberP b && memberP p && memberP q
  | .search _ φ p q => memberGuardF φ && memberP p && memberP q
  | .tvote _ _ p q => memberP p && memberP q
  | .sys _ _ => true
  | .selfIdx _ => true

/-! ### Lemma A′: the member slots filled, atom by atom -/

/-- The member-slot substitution, as meta terms: `#0..#6` kept, the closed description triples of the two
members of `defs` in `#7..#12` (`descriptionsSys (progListCode defs)` on codes, `semitermVec_val_vSys13`). -/
noncomputable def vSys13 (D : ℕ) : Fin 13 → Semiterm LAct Empty 13 :=
  ![#0, #1, #2, #3, #4, #5, #6,
    cl (canonicalMeta (pSys D 0)), cl (revalueUMeta (pSys D 0)), cl (revalueWMeta (pSys D 0)),
    cl (canonicalMeta (pSys D 1)), cl (revalueUMeta (pSys D 1)), cl (revalueWMeta (pSys D 1))]

/-- The closed description of a bot-wrapped system is the same at every node budget (a system is opaque to the
abstraction, `codeTermMetaAbs_sys`). -/
lemma closedDescAt_bot_sys (k₀ : Option ℕ) (D j : ℕ) : closedDescAt k₀ (pBot (pSys D j)) = closedDesc13 (pBot (pSys D j)) := by
  cases k₀ with
  | none => rfl
  | some k => exact closedDescAt_of_noSearchAt ((NoSearchAt.bot _ (NoSearchAt.sys k D j)).canonical)

/-- **Lemma A′**: substituting the member descriptions into the description of a member-atom program gives
the description of the closed program. `w` reads the member slots as the closed descriptions of
`pSys D 0`/`pSys D 1` and agrees with `w'` on the program variable and the frame. -/
lemma progAuxAt_sysClose {m : ℕ} (k₀ : Option ℕ) (defs : PD.ProgList) {p : PD.Prog} (hp : memberAtomP p = true)
    (w w' : Fin 14 → Semiterm LAct Empty m) (hf : ∀ i : Fin 14, i.val ≤ 7 → w i = w' i)
    (h8 : w 8 = cl (canonicalMeta (pSys (progListCode defs) 0)))
    (h9 : w 9 = cl (revalueUMeta (pSys (progListCode defs) 0)))
    (h10 : w 10 = cl (revalueWMeta (pSys (progListCode defs) 0)))
    (h11 : w 11 = cl (canonicalMeta (pSys (progListCode defs) 1)))
    (h12 : w 12 = cl (revalueUMeta (pSys (progListCode defs) 1)))
    (h13 : w 13 = cl (revalueWMeta (pSys (progListCode defs) 1))) :
    progAuxAt k₀ p (progCode p) ⇜ w = progAuxAt k₀ (p.sysClose defs) (progCode (p.sysClose defs)) ⇜ w' := by
  have h0 := hf 0 (by decide)
  by_cases hpr : pronounP p = true
  · rcases pronounP_cases hpr with rfl | rfl | rfl | rfl
    · -- `.selfIdx 0 ↦ .sys defs 0`
      rw [progAuxAt_selfIdx0, PD.Prog.sysClose, progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sys, closedDescAt_subst,
        canonicalSlot_of_sys]
      unfold Rewriting.subst
      rw [rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 8)) (Rew.bShift (w 9)) (Rew.bShift (w 10)) = _
      rw [h0, h8, h9, h10, rew_cl, rew_cl, rew_cl]
    · rw [progAuxAt_selfIdx1, PD.Prog.sysClose, progAuxAt_of_ne _ (by simp) (by simp) rfl, progCode_sys, closedDescAt_subst,
        canonicalSlot_of_sys]
      unfold Rewriting.subst
      rw [rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 11)) (Rew.bShift (w 12)) (Rew.bShift (w 13)) = _
      rw [h0, h11, h12, h13, rew_cl, rew_cl, rew_cl]
    · -- `.bot (.selfIdx 0) ↦ .bot (.sys defs 0)`: the pronoun clause meets the closed description of `pBot (pSys d 0)`
      rw [progAuxAt_botSelfIdx0, PD.Prog.sysClose, PD.Prog.sysClose, progAuxAt_of_ne _ (by simp) (by simp) rfl,
        progCode_bot, progCode_sys, closedDescAt_bot_sys, closedDesc13_subst, revalueUMeta_pBot, revalueWMeta_pBot]
      unfold Rewriting.subst
      rw [rew_descF, rew_pBotTerm]
      show descF (Rew.bShift (w 0)) (pBotTerm (Rew.bShift (w 8))) (Rew.bShift (w 9)) (Rew.bShift (w 10)) = _
      rw [h0, h8, h9, h10, rew_cl, rew_cl, rew_cl, pBotTerm_canonicalMeta]
    · rw [progAuxAt_botSelfIdx1, PD.Prog.sysClose, PD.Prog.sysClose, progAuxAt_of_ne _ (by simp) (by simp) rfl,
        progCode_bot, progCode_sys, closedDescAt_bot_sys, closedDesc13_subst, revalueUMeta_pBot, revalueWMeta_pBot]
      unfold Rewriting.subst
      rw [rew_descF, rew_pBotTerm]
      show descF (Rew.bShift (w 0)) (pBotTerm (Rew.bShift (w 11))) (Rew.bShift (w 12)) (Rew.bShift (w 13)) = _
      rw [h0, h11, h12, h13, rew_cl, rew_cl, rew_cl, pBotTerm_canonicalMeta]
  · have hns : noSelfIdxP p = true := by
      simp only [memberAtomP, Bool.or_eq_true] at hp
      exact hp.resolve_left hpr
    by_cases h1 : p = .self
    · subst h1
      rw [PD.Prog.sysClose, progAuxAt_self]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) =
        descF (Rew.bShift (w' 0)) (Rew.bShift (w' 1)) (Rew.bShift (w' 2)) (Rew.bShift (w' 3))
      rw [h0, hf 1 (by decide), hf 2 (by decide), hf 3 (by decide)]
    by_cases h2 : p = .opp
    · subst h2
      rw [PD.Prog.sysClose, progAuxAt_opp]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 4)) (Rew.bShift (w 5)) (Rew.bShift (w 6)) =
        descF (Rew.bShift (w' 0)) (Rew.bShift (w' 4)) (Rew.bShift (w' 5)) (Rew.bShift (w' 6))
      rw [h0, hf 4 (by decide), hf 5 (by decide), hf 6 (by decide)]
    rw [progAuxAt_of_ne _ h1 h2 (pronounP_eq_false_of_noSelfIdxP hns),
      progAuxAt_of_ne _ (sysClose_ne_self h1 defs) (sysClose_ne_opp h2 defs) (pronounP_sysClose hns defs),
      progCode_sysClose_of_noSelfIdxP p defs hns, closedDescAt_subst, closedDescAt_subst, h0, hf 7 (by decide)]

/-! ### The semantic equation -/

/-- **The member-slot equation, meta level**: on a member guard, filling the member slots with the members'
descriptions IS the thirteen-variable template of the closed guard — literally. -/
theorem templateAt_sysClose (defs : PD.ProgList) (k₀ : Option ℕ) :
    ∀ φ : PD.Formula, memberGuardF φ = true →
      templateAt φ k₀ ⇜ vSys13 (progListCode defs) = templateAt (φ.sysClose defs) k₀
  | .plays p q a, h => by
    simp only [memberGuardF, Bool.and_eq_true] at h
    rw [PD.Formula.sysClose, templateAt_plays, templateAt_plays]
    unfold progGraphAt
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 4
    · refine progAuxAt_sysClose k₀ defs h.1 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro i hi; fin_cases i <;> first | rfl | exact absurd hi (by decide)
      all_goals (show Rew.bShift (Rew.bShift (Rew.bShift (cl _))) = _; rw [rew_cl, rew_cl, rew_cl])
    · congr 1
      · refine progAuxAt_sysClose k₀ defs h.2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro i hi; fin_cases i <;> first | rfl | exact absurd hi (by decide)
        all_goals (show Rew.bShift (Rew.bShift (Rew.bShift (cl _))) = _; rw [rew_cl, rew_cl, rew_cl])
      · congr 1
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · rfl
        · exact rew_cl _ _
  | .impl φ ψ, h => by
    simp only [memberGuardF, Bool.and_eq_true] at h
    rw [PD.Formula.sysClose, templateAt_impl, templateAt_impl, ← templateAt_sysClose defs k₀ φ h.1,
      ← templateAt_sysClose defs k₀ ψ h.2]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_imply]
  | .neg φ, h => by
    simp only [memberGuardF] at h
    rw [PD.Formula.sysClose, templateAt_neg, templateAt_neg, ← templateAt_sysClose defs k₀ φ h]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_neg]
  | .box _ _, h => by simp [memberGuardF] at h
  | .eq p q, h => by
    simp only [memberGuardF, Bool.and_eq_true] at h
    rw [PD.Formula.sysClose, templateAt_eq, templateAt_eq]
    unfold progGraphAt
    simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
    congr 3
    · refine progAuxAt_sysClose k₀ defs h.1 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro i hi; fin_cases i <;> first | rfl | exact absurd hi (by decide)
      all_goals (show Rew.bShift (Rew.bShift (cl _)) = _; rw [rew_cl, rew_cl])
    · congr 1
      · rw [closedDescAt_subst, closedDescAt_subst, progCode_sysClose_of_noSelfIdxP q defs h.2]; rfl
      · rw [Semiformula.rew_rel]
        congr 1
        funext i
        fin_cases i <;> rfl
  | .diag _ _, _ => by
    rw [PD.Formula.sysClose, templateAt_diag, templateAt_diag]
    unfold Rewriting.subst
    rw [LogicalConnective.HomClass.map_bot]

/-- The unabstracted instance (today's name). -/
theorem template13_sysClose (defs : PD.ProgList) (φ : PD.Formula) (h : memberGuardF φ = true) :
    template13 φ ⇜ vSys13 (progListCode defs) = template13 (φ.sysClose defs) := templateAt_sysClose defs none φ h

/-! ### The code equation -/

/-- The codes of the member-slot terms form the member-slot vector `descriptionsSys`. -/
lemma semitermVec_val_vSys13 (D : ℕ) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb (vSys13 D i) : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13)) =
      descriptionsSys D := by
  have e : ∀ t : Semiterm LAct Empty 13,
      ((⌜(Rew.emb t : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13)).val =
        (⌜(Rew.emb t : SyntacticSemiterm LAct 13)⌝ : ℕ) := fun _ ↦ rfl
  have hv : (fun i ↦ (⌜(Rew.emb (vSys13 D i) : SyntacticSemiterm LAct 13)⌝ : Bootstrapping.Semiterm ℕ LAct 13)) =
      ![⌜(#0 : SyntacticSemiterm LAct 13)⌝, ⌜(#1 : SyntacticSemiterm LAct 13)⌝, ⌜(#2 : SyntacticSemiterm LAct 13)⌝,
        ⌜(#3 : SyntacticSemiterm LAct 13)⌝, ⌜(#4 : SyntacticSemiterm LAct 13)⌝, ⌜(#5 : SyntacticSemiterm LAct 13)⌝,
        ⌜(#6 : SyntacticSemiterm LAct 13)⌝,
        ⌜(Rew.emb (cl (canonicalMeta (pSys D 0))) : SyntacticSemiterm LAct 13)⌝,
        ⌜(Rew.emb (cl (revalueUMeta (pSys D 0))) : SyntacticSemiterm LAct 13)⌝,
        ⌜(Rew.emb (cl (revalueWMeta (pSys D 0))) : SyntacticSemiterm LAct 13)⌝,
        ⌜(Rew.emb (cl (canonicalMeta (pSys D 1))) : SyntacticSemiterm LAct 13)⌝,
        ⌜(Rew.emb (cl (revalueUMeta (pSys D 1))) : SyntacticSemiterm LAct 13)⌝,
        ⌜(Rew.emb (cl (revalueWMeta (pSys D 1))) : SyntacticSemiterm LAct 13)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, e]
  simp only [quote_emb_cl]
  simp only [← Semiterm.empty_quote_def, quote_canonicalMeta, quote_revalueUMeta, quote_revalueWMeta]
  rfl

/-- **The member-slot equation, codes**: the closer's action on a member's stored template is the template
code of the closed guard. -/
theorem templateCode_sysClose (defs : PD.ProgList) (φ : PD.Formula) (h : memberGuardF φ = true) :
    sysCloseTemplate (progListCode defs) (templateCode φ) = templateCode (φ.sysClose defs) := by
  rw [sysCloseTemplate_of_template₁₃ (isSemiformula_templateCode13 φ)]
  unfold templateCode
  rw [← template13_sysClose defs φ h, quote_subst_gen, semitermVec_val_vSys13]

/-- **The member-slot equation on the STORED template codes**: the closer's action on a member's stored template
at budget `k` is the stored template of the closed guard at `k`. -/
theorem templateCodeAt_sysClose (defs : PD.ProgList) (φ : PD.Formula) (k : ℕ) (h : memberGuardF φ = true) :
    sysCloseTemplate (progListCode defs) (templateCodeAt φ k) = templateCodeAt (φ.sysClose defs) k := by
  rw [sysCloseTemplate_of_template₁₃ (isSemiformula_templateCodeAt13 φ k)]
  unfold templateCodeAt
  rw [← templateAt_sysClose defs (some k) φ h, quote_subst_gen, semitermVec_val_vSys13]

/-- **The closer equation on compiled members**: `sysCloseCode` is the engine's `Prog.sysClose` on the code of
every program whose search guards are member guards. -/
theorem progCode_sysClose_member (defs : PD.ProgList) :
    ∀ p : PD.Prog, memberP p = true →
      progCode (p.sysClose defs) = sysCloseCode (progListCode defs) (progCode p)
  | .const _, _ => by simp [PD.Prog.sysClose]
  | .self, _ => by simp [PD.Prog.sysClose]
  | .opp, _ => by simp [PD.Prog.sysClose]
  | .bot p, h => by simp [PD.Prog.sysClose, progCode_sysClose_member defs p h]
  | .sim p q, h => by
    simp only [memberP, Bool.and_eq_true] at h
    simp [PD.Prog.sysClose, progCode_sysClose_member defs p h.1, progCode_sysClose_member defs q h.2]
  | .ite b _ p q, h => by
    simp only [memberP, Bool.and_eq_true] at h
    simp [PD.Prog.sysClose, progCode_sysClose_member defs b h.1.1, progCode_sysClose_member defs p h.1.2,
      progCode_sysClose_member defs q h.2]
  | .search k φ p q, h => by
    simp only [memberP, Bool.and_eq_true] at h
    simp only [PD.Prog.sysClose, progCode_search, sysCloseCode_search, templateCodeAt_sysClose defs φ k h.1.1,
      progCode_sysClose_member defs p h.1.2, progCode_sysClose_member defs q h.2]
  | .tvote v _ p q, h => by
    simp only [memberP, Bool.and_eq_true] at h
    simp [PD.Prog.sysClose, progCode_sysClose_member defs p h.1, progCode_sysClose_member defs q h.2]
  | .sys _ _, _ => by simp [PD.Prog.sysClose]
  | .selfIdx _, _ => by simp [PD.Prog.sysClose]

/-- The two guard shapes `sysGo` emits are member guards (by computation), for both member indices. -/
example (a : PD.Action) :
    memberGuardF (.plays (.bot (.selfIdx 0)) (.bot (.selfIdx 0)) a) = true ∧
    memberGuardF (.plays (.bot (.selfIdx 1)) (.bot (.selfIdx 1)) a) = true ∧
    memberGuardF (.impl (.plays .self (.bot (.selfIdx 0)) a) (.plays (.bot (.selfIdx 0)) .self a)) = true ∧
    memberGuardF (.impl (.plays .self (.bot (.selfIdx 1)) a) (.plays (.bot (.selfIdx 1)) .self a)) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end ArithS
