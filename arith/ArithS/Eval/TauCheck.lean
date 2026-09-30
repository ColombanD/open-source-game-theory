import ArithS.Agents.SysTemplate
import PrisonersDilemma.Tau.Zoo

/-!
# ArithS.Eval.TauCheck — the gates of Phase 2 (the tau constructors in the trusted base)

`SPRIME_SOURCE_OF_TRUTH.md` §2.6, 2026-09-30. Four gates, each a theorem or an `example`:

* **(a)** `EvalGraph.case_iff` has the tau disjuncts (`EvalGraph.tvote_nil_iff`, `tvote_cons_iff`, `sys_iff`;
  `pSelfIdx` never evaluates) — restated below as examples on the inversion lemmas.
* **(b)** The engine's symmetric system `cfdSys k` (`Tau/Zoo.lean`) has a real code, and its evaluation
  unfolds by `sys_iff` to the member's closed code, for BOTH components (`evalGraph_cfdSys_unfold`).
* **(c)** `progCode (inst (tauZoo k) A T) ≠ 0` for every roster template in both roles — a consequence of
  `progCode_ne_zero` (every program code is a shape).
* **(d)** **Lockstep** with the engine's `eval` at the same fuel on the tau-search-free fragment
  (`evalGraph_of_eval_tauSearchFree`): the `.tvote` peel (nil/zero threshold, the entry's own frame,
  truncated subtraction) and the `.sys` unfold (`listGet` + `sysCloseCode`) agree with `Dynamics.eval`
  clause by clause; the corollaries `evalGraph_of_eval_sys_step` / `evalGraph_of_eval_tvote_nil` /
  `evalGraph_of_eval_tvote_zero` state the one-step cases the phase note asks for.

**(e) The pronoun reading (2026-10-01, the last item of §2.5).** `sysCloseCode` closes a member's stored
template by `sysCloseTemplate`, which fills the member slots `#7..#12` of the thirteen-variable template
(`Agents/SysTemplate.lean`): `sysCloseCode_cfdSys_member` shows the closed member of `cfdSys k` is the CODE OF
THE ENGINE'S CLOSED MEMBER, whose guard names `.bot (.sys (cfdSys k) (1 - i))` (`cfdGuard_sysClose`,
`sysCloseTemplate_cfdGuard`). The truth equation of that closed guard at ℕ — "the partner, bot-wrapped, plays C
against itself" — is `Cells/TauMember.lean` (it needs the frozen bridge's `models_sentenceAt_plays`). Search
nodes with pronoun guards stay outside the SEARCH-FREE lockstep fragment by definition (they search).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### (a) The tau disjuncts of the evaluator -/

#check @EvalGraph.case_iff

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n me opp θ p q a : V} :
    EvalGraph (n + 1) me opp (pTvote pNil θ p q) a ↔
    ((θ = 0 ∧ EvalGraph n me opp p a) ∨ (θ ≠ 0 ∧ EvalGraph n me opp q a)) :=
  EvalGraph.tvote_nil_iff

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n me opp w I rest θ p q a : V} :
    EvalGraph (n + 1) me opp (pTvote (pCons (ppair w I) rest) θ p q) a ↔
    ((θ = 0 ∧ EvalGraph n me opp p a) ∨
     (θ ≠ 0 ∧ ∃ r, EvalGraph n (pBot I) (pBot I) I r ∧
       ((r = 0 ∧ EvalGraph n me opp (pTvote rest (θ - w) p q) a) ∨
        (r ≠ 0 ∧ EvalGraph n me opp (pTvote rest θ p q) a)))) :=
  EvalGraph.tvote_cons_iff

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n me opp d i a : V} :
    EvalGraph (n + 1) me opp (pSys d i) a ↔ ∃ m, listGet d i = m + 1 ∧ EvalGraph n me opp (sysCloseCode d m) a :=
  EvalGraph.sys_iff

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n me opp j a : V} :
    ¬EvalGraph n me opp (pSelfIdx j) a :=
  EvalGraph.selfIdx_iff

/-! ### (b) The symmetric system `cfdSys k` -/

/-- Member `i` of `cfdSys k`: the searcher probing the OTHER member through the pronoun `.selfIdx (1 - i)`. -/
def cfdMember (k i : ℕ) : PD.Prog :=
  .search k (.plays (.bot (.selfIdx (1 - i))) (.bot (.selfIdx (1 - i))) Action.C) (.const .C) (.const .D)

theorem cfdSys_get?_zero (k : ℕ) : (cfdSys k).get? 0 = some (cfdMember k 0) := rfl
theorem cfdSys_get?_one (k : ℕ) : (cfdSys k).get? 1 = some (cfdMember k 1) := rfl

theorem progCode_cfdSys_ne_zero (k i : ℕ) : progCode (.sys (cfdSys k) i) ≠ 0 := progCode_ne_zero _

theorem progCode_cfdSys (k i : ℕ) :
    progCode (.sys (cfdSys k) i) =
    pSys (pCons (progCode (cfdMember k 0)) (pCons (progCode (cfdMember k 1)) pNil)) i := by
  simp [cfdSys, cfdMember]

/-- **One-step unfolding** of the system at ℕ, both components: `sys_iff` finds the member and runs it
closed. -/
theorem evalGraph_cfdSys_unfold (k n me opp a : ℕ) (i : ℕ) (hi : i ≤ 1) :
    EvalGraph (n + 1) me opp (progCode (.sys (cfdSys k) i)) a ↔
    EvalGraph n me opp (sysCloseCode (progListCode (cfdSys k)) (progCode (cfdMember k i))) a := by
  rw [progCode_sys, EvalGraph.sys_iff]
  have hget : listGet (progListCode (cfdSys k)) i = progCode (cfdMember k i) + 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
    · exact listGet_progListCode_some _ _ _ (cfdSys_get?_zero k)
    · exact listGet_progListCode_some _ _ _ (cfdSys_get?_one k)
  rw [hget]
  constructor
  · rintro ⟨m, hm, h⟩
    obtain rfl : progCode (cfdMember k i) = m := Nat.succ_injective hm
    exact h
  · intro h; exact ⟨_, rfl, h⟩

/-- The guard of member `i` of `cfdSys k`: "the partner, bot-wrapped, plays `C` against itself" through the
pronoun `.selfIdx (1 - i)`. -/
def cfdGuard (i : ℕ) : PD.Formula := .plays (.bot (.selfIdx (1 - i))) (.bot (.selfIdx (1 - i))) Action.C

theorem cfdMember_eq (k i : ℕ) : cfdMember k i = .search k (cfdGuard i) (.const .C) (.const .D) := rfl

/-- **The closed member is the engine's closed member** (the pronoun reading, `progCode_sysClose_member`):
`sysCloseCode` on the code of member `i` is the code of `(cfdMember k i).sysClose (cfdSys k)`, whose guard names
`.bot (.sys (cfdSys k) (1 - i))` — no dangling code survives. -/
theorem sysCloseCode_cfdSys_member (k i : ℕ) (hi : i ≤ 1) :
    sysCloseCode (progListCode (cfdSys k)) (progCode (cfdMember k i)) = progCode ((cfdMember k i).sysClose (cfdSys k)) := by
  symm
  apply progCode_sysClose_member
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl <;> rfl

/-- The closed member's guard, spelled out: the partner `.bot (.sys (cfdSys k) (1 - i))` plays `C` against itself. -/
theorem cfdGuard_sysClose (k i : ℕ) :
    (cfdGuard i).sysClose (cfdSys k) =
      .plays (.bot (.sys (cfdSys k) (1 - i))) (.bot (.sys (cfdSys k) (1 - i))) Action.C := rfl

/-- The closed member's stored template is the template code of the closed guard (`templateCode_sysClose`). -/
theorem sysCloseTemplate_cfdGuard (k i : ℕ) (hi : i ≤ 1) :
    sysCloseTemplate (progListCode (cfdSys k)) (templateCode (cfdGuard i)) =
      templateCode (.plays (.bot (.sys (cfdSys k) (1 - i))) (.bot (.sys (cfdSys k) (1 - i))) Action.C) := by
  rw [← cfdGuard_sysClose]
  apply templateCode_sysClose
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl <;> rfl

/-! ### (c) Every compiled instance has a real code -/

/-- The census over the whole roster (17 templates, both roles): no compiled instance has the code `0`. -/
example (k : ℕ) (A T : Tmpl) : progCode (inst (tauZoo k) A T) ≠ 0 := progCode_ne_zero _

/-- The 14 paper templates, spelled out. -/
example (k : ℕ) :
    ∀ A ∈ [Tmpl.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid,
             .cimcic, .prudent, .maxconfidence, .minconfidence],
    ∀ T ∈ [Tmpl.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid,
             .cimcic, .prudent, .maxconfidence, .minconfidence],
      progCode (inst (tauZoo k) A T) ≠ 0 ∧ progCode (inst (tauZoo k) T A) ≠ 0 :=
  fun _ _ _ _ ↦ ⟨progCode_ne_zero _, progCode_ne_zero _⟩

/-! ### (d) Lockstep on the tau-search-free fragment -/

private lemma actCode_eq_of_beq' {r a : PD.Action} (h : (r == a) = true) : actCode r = actCode a := by
  cases r <;> cases a <;> first | rfl | exact absurd h (by decide)

private lemma actCode_ne_of_beq_false' {r a : PD.Action} (h : (r == a) = false) : actCode r ≠ actCode a := by
  cases r <;> cases a <;> first | exact absurd h (by decide) | decide

/-- Truncated subtraction of `PeanoMinus` at `ℕ` is `Nat.sub` (the two `Sub ℕ` instances agree). -/
lemma pm_sub_eq_nat_sub (a b : ℕ) :
    @HSub.hSub ℕ ℕ ℕ (@instHSub ℕ ⟨FFL.FirstOrder.Arithmetic.sub⟩) a b = a - b := by
  show FFL.FirstOrder.Arithmetic.sub a b = a - b
  symm
  refine (sub_eq_iff (V := ℕ)).mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hle : b ≤ a := by
      rcases le_def.mp h with e | l
      · exact e.symm ▸ le_rfl
      · exact Nat.le_of_lt l
    exact (Nat.add_sub_cancel' hle).symm
  · exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

/-- **Lockstep, tau-search-free**: an engine run at fuel `n` on players and body without any `.search`
node (entries and members included) is an arithmetized run at the SAME fuel, with NO side condition on
the players. Clause by clause as `Cells/SearchFree.evalGraph_of_eval_searchFree_core`, plus the `.tvote`
peel and the `.sys` unfold. -/
theorem evalGraph_of_eval_tauSearchFree :
    ∀ (n : ℕ) (me opp body : PD.Prog) (a : PD.Action),
      tauSearchFreeP me = true → tauSearchFreeP opp = true → tauSearchFreeP body = true →
      PD.eval n me opp body = some a →
      EvalGraph n (progCode me) (progCode opp) (progCode body) (actCode a) := by
  intro n
  induction n with
  | zero => intro me opp body a _ _ _ h; simp [PD.eval] at h
  | succ n ih =>
    intro me opp body a hme hopp hb h
    cases body with
    | const c =>
      have hc : c = a := by simpa [PD.eval] using h
      subst hc
      rw [progCode_const]
      exact EvalGraph.const_iff.mpr rfl
    | self =>
      rw [PD.eval] at h
      rw [progCode_self, EvalGraph.self_iff]
      exact ih me opp me a hme hopp hme h
    | opp =>
      rw [PD.eval] at h
      rw [progCode_opp, EvalGraph.opp_iff]
      exact ih me opp opp a hme hopp hopp h
    | bot p =>
      rw [PD.eval] at h
      rw [progCode_bot, EvalGraph.bot_iff]
      exact ih me opp p a hme hopp hb h
    | sim p q =>
      simp only [tauSearchFreeP, Bool.and_eq_true] at hb
      rw [PD.eval] at h
      have hN := ih _ _ _ a (tauSearchFreeP_subst p me opp hb.1 hme hopp) (tauSearchFreeP_subst q me opp hb.2 hme hopp)
        (tauSearchFreeP_subst p me opp hb.1 hme hopp) h
      rw [progCode_subst_tauSearchFree me opp p hb.1, progCode_subst_tauSearchFree me opp q hb.2] at hN
      rw [progCode_sim, EvalGraph.sim_iff]
      exact hN
    | ite b c p q =>
      simp only [tauSearchFreeP, Bool.and_eq_true] at hb
      rw [PD.eval] at h
      cases hbr : PD.eval n me opp b with
      | none => simp [hbr] at h
      | some r =>
        rw [hbr] at h
        simp only [bind, Option.bind] at h
        have h₁ := ih me opp b r hme hopp hb.1.1 hbr
        rw [progCode_ite, EvalGraph.ite_iff]
        by_cases hr : (r == c) = true
        · rw [if_pos hr] at h
          exact ⟨actCode r, h₁, Or.inl ⟨actCode_eq_of_beq' hr, ih me opp p a hme hopp hb.1.2 h⟩⟩
        · rw [if_neg hr] at h
          exact ⟨actCode r, h₁,
            Or.inr ⟨actCode_ne_of_beq_false' (Bool.eq_false_iff.mpr hr), ih me opp q a hme hopp hb.2 h⟩⟩
    | search k φ p q => simp [tauSearchFreeP] at hb
    | tvote v θ p q =>
      simp only [tauSearchFreeP, Bool.and_eq_true] at hb
      cases v with
      | nil =>
        rw [progCode_tvote, voteListCode_nil, EvalGraph.tvote_nil_iff]
        by_cases hθ : θ = 0
        · subst hθ
          rw [PD.eval_tvote_zero] at h
          exact Or.inl ⟨rfl, ih me opp p a hme hopp hb.1.2 h⟩
        · rw [PD.eval_tvote_nil n hθ] at h
          exact Or.inr ⟨hθ, ih me opp q a hme hopp hb.2 h⟩
      | cons w I rest =>
        simp only [tauSearchFreeV, Bool.and_eq_true] at hb
        rw [progCode_tvote, voteListCode_cons, EvalGraph.tvote_cons_iff]
        by_cases hθ : θ = 0
        · subst hθ
          rw [PD.eval_tvote_zero] at h
          exact Or.inl ⟨rfl, ih me opp p a hme hopp hb.1.2 h⟩
        · refine Or.inr ⟨hθ, ?_⟩
          have hI : tauSearchFreeP (.bot I) = true := hb.1.1.1
          cases hIe : PD.eval n (.bot I) (.bot I) I with
          | none => rw [PD.eval_tvote_cons_none n hθ hIe] at h; exact absurd h (by simp)
          | some r =>
            have hIr := ih (.bot I) (.bot I) I r hI hI hb.1.1.1 hIe
            rw [progCode_bot] at hIr
            cases r with
            | C =>
              rw [PD.eval_tvote_cons_c n hθ hIe] at h
              have hcont := ih me opp (.tvote rest (θ - w) p q) a hme hopp
                (by simp only [tauSearchFreeP, Bool.and_eq_true]; exact ⟨⟨hb.1.1.2, hb.1.2⟩, hb.2⟩) h
              rw [progCode_tvote] at hcont
              refine ⟨0, hIr, Or.inl ⟨rfl, ?_⟩⟩
              rw [pm_sub_eq_nat_sub]
              exact hcont
            | D =>
              rw [PD.eval_tvote_cons_d n hθ hIe] at h
              have hcont := ih me opp (.tvote rest θ p q) a hme hopp
                (by simp only [tauSearchFreeP, Bool.and_eq_true]; exact ⟨⟨hb.1.1.2, hb.1.2⟩, hb.2⟩) h
              rw [progCode_tvote] at hcont
              exact ⟨1, hIr, Or.inr ⟨by decide, hcont⟩⟩
    | sys defs i =>
      rw [progCode_sys, EvalGraph.sys_iff]
      cases hget : defs.get? i with
      | none => rw [PD.eval_sys_none n hget] at h; exact absurd h (by simp)
      | some m =>
        rw [PD.eval_sys_some n hget] at h
        have hm : tauSearchFreeP m = true := tauSearchFreeP_of_get? defs i m hb hget
        refine ⟨progCode m, listGet_progListCode_some defs i m hget, ?_⟩
        rw [← progCode_sysClose_tauSearchFree defs m hm]
        exact ih me opp (m.sysClose defs) a hme hopp (tauSearchFreeP_sysClose m defs hm hb) h
    | selfIdx j => simp [PD.eval] at h

/-- The `.sys` one-step case, at the engine level: an engine run of `.sys defs i` is a code run of the
found member, closed, one fuel lower. -/
theorem evalGraph_of_eval_sys_step {n : ℕ} {me opp m : PD.Prog} {defs : PD.ProgList} {i : ℕ} {a : PD.Action}
    (hme : tauSearchFreeP me = true) (hopp : tauSearchFreeP opp = true) (hd : tauSearchFreeL defs = true)
    (hget : defs.get? i = some m) (h : PD.eval (n + 1) me opp (.sys defs i) = some a) :
    EvalGraph n (progCode me) (progCode opp) (sysCloseCode (progListCode defs) (progCode m)) (actCode a) := by
  rw [PD.eval_sys_some n hget] at h
  have hm : tauSearchFreeP m = true := tauSearchFreeP_of_get? defs i m hd hget
  rw [← progCode_sysClose_tauSearchFree defs m hm]
  exact evalGraph_of_eval_tauSearchFree n me opp _ a hme hopp (tauSearchFreeP_sysClose m defs hm hd) h

/-- The `.tvote` nil case: an exhausted list with a positive residual commits to the else branch. -/
theorem evalGraph_of_eval_tvote_nil {n : ℕ} {me opp p q : PD.Prog} {θ : ℕ} {a : PD.Action}
    (hme : tauSearchFreeP me = true) (hopp : tauSearchFreeP opp = true) (hq : tauSearchFreeP q = true)
    (hθ : θ ≠ 0) (h : PD.eval (n + 1) me opp (.tvote .nil θ p q) = some a) :
    EvalGraph n (progCode me) (progCode opp) (progCode q) (actCode a) := by
  rw [PD.eval_tvote_nil n hθ] at h
  exact evalGraph_of_eval_tauSearchFree n me opp q a hme hopp hq h

/-- The `.tvote` zero case: a met threshold commits to the then branch without consulting the entries. -/
theorem evalGraph_of_eval_tvote_zero {n : ℕ} {me opp p q : PD.Prog} {v : PD.VoteList} {a : PD.Action}
    (hme : tauSearchFreeP me = true) (hopp : tauSearchFreeP opp = true) (hp : tauSearchFreeP p = true)
    (h : PD.eval (n + 1) me opp (.tvote v 0 p q) = some a) :
    EvalGraph n (progCode me) (progCode opp) (progCode p) (actCode a) := by
  rw [PD.eval_tvote_zero] at h
  exact evalGraph_of_eval_tauSearchFree n me opp p a hme hopp hp h

end ArithS
