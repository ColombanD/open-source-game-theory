import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CIMCIC.vs_DBot

/-!
# Family-completion spike — the Tier-2 evidence bundle

**Goal.** Complete Family B (logical glue: `implRefl`, `implK`, `contrapose`, `negElim`)
and Family A (the ONE general in-frame reading rule `ctxBranch` that subsumes and closes
the fused-rule zoo). This spike is the `propose_pf_constructor`-style evidence: every
claim below is kernel-checked against the CURRENT engine, no `sorry`, no axiom.

**What is proven here:**
1. §1 — SOUNDNESS CERTIFICATES: the interp-level content of each proposed rule is a
   theorem of the current engine (the machine gate).
2. §2 — THE CANARY FIRES, AND THE REPAIR: `implRefl` FALSIFIES the tail-recursing
   census invariant used by every exclusion proof (`CimcicBotForbiddenC`-style), and
   the strengthened invariant `Guarded` (tail forbidden AND antecedent unforbidden,
   compositionally) survives the full extended glue family. Validated on a mini
   system carrying exactly the logical-glue rules old + new.
3. §3 — THE GAP, CLOSED: originally the kernel-checked proof that `⊢ φ → φ` was NOT
   derivable (via the CIMCIC census); since the 2026-07-28 integration of
   `Pf.implRefl`/`Pf.implK` it is the one-line positive demo.
4. §4 — FAMILY A: the `EvalCtx` telescope, its `plug`/`guards`, and the FULL
   soundness core of the proposed `ctxBranch` constructor (in-frame evaluation
   reaches the plugged branch when every guard on the spine holds). Plus `rfl`
   demos that the conclusions of `searchBranch` and `iteBranchSearch_t` are
   instances, and a depth-3 shape (PrudentBot3) beyond every current fused rule.

**Integration status:** `implRefl`/`implK` INTEGRATED 2026-07-28 (steps 1–2 of
`Research/Notes/FAMILY_COMPLETION_DESIGN.md`): censuses on the Guarded invariant,
constructors through the engine + PfG mirror + both deciders + T48 dichotomy +
T49 substrate + T50 transport + T51/T52; full build green. `contrapose`/`negElim`
(step 3) and `ctxBranch` (step 4) remain designed-but-not-integrated.
-/

namespace PD.Spikes.FamilyCompletion

open PD PD.BaseTheorems PD.Bots PD.Theorems

/-! ## §1 — Soundness certificates (the machine gate)

Each proposed rule's conclusion-interp follows from its premises' interps — these are
exactly the certificates `propose_pf_constructor` requires. All four are classically
(indeed intuitionistically, except `contrapose`) valid, and faithful: PA proves each. -/

/-- `implRefl`: `⊢ φ → φ` (identity). Premise-free leaf; cost = conclusion size. -/
theorem implRefl_sound (φ : Formula) : (Formula.impl φ φ).interp :=
  fun h => h

/-- `implK`: `⊢ φ → (ψ → φ)` (K as an object formula). Premise-free leaf.
    NOTE: `implK` + `mp` DERIVES `weakenImpl` (shown in §2), so the rule set stays
    non-redundant only for cost reasons (weakenImpl's transcript is tighter). -/
theorem implK_sound (φ ψ : Formula) : (Formula.impl φ (.impl ψ φ)).interp :=
  fun h _ => h

/-- `contrapose` (rule form): from `⊢ φ → ψ` infer `⊢ ¬ψ → ¬φ`. One-premise rule,
    the first CONSUMER of `.neg` in the logical core. -/
theorem contrapose_sound (φ ψ : Formula) (h : (Formula.impl φ ψ).interp) :
    (Formula.impl (.neg ψ) (.neg φ)).interp :=
  fun hn hp => hn (h hp)

/-- `negElim` (ex falso, rule form): from `⊢ ¬φ` and `⊢ φ` infer anything. In any
    census its case is discharged by `Pf_sound` on the two premises (they cannot
    coexist), so it is census-safe DESPITE its unconstrained conclusion. -/
theorem negElim_sound (φ ψ : Formula)
    (h1 : (Formula.neg φ).interp) (h2 : φ.interp) : ψ.interp :=
  absurd h2 h1

/-! ## §2 — The census canary fires, and the repair

Every structural exclusion census in the engine (`CimcicBotForbiddenC`,
`DBotForbiddenC`, the `Base/Exclusion` tail predicates) uses the TAIL-RECURSING
invariant: `Forbidden (.impl _ ψ) := Forbidden ψ`. That invariant is closed under
every CURRENT rule because every current implication-producing rule has a premise
whose tail contains the conclusion's tail. `implRefl`/`implK` are premise-free with
an ARBITRARY tail — they falsify the invariant (NOT the underlying unprovability:
to extract the tail of `φ → φ` by `mp` you would need `φ` itself).

THE REPAIR: strengthen compositionally —
    `Guarded (.impl α ψ) := Guarded ψ ∧ ¬ Guarded α`
"the forbidden tail is reachable only through unforbidden antecedents". The reflexive
and K shapes then self-destruct (`⟨h, hn⟩` with `hn h`), and every premise-carrying
rule still closes via `by_cases` on the antecedent (the premise IH refutes the
forbidden branch). Validated below on the full old+new glue family. -/

section CensusInvariant

/-- Mini proof system: the logical-glue family over an abstract leaf layer `L`
    (standing for atoms + transparency leaves). Budgets are dropped — the census
    invariant question is purely structural. -/
inductive MiniPf (L : Formula → Prop) : Formula → Prop where
  | leaf {φ} : L φ → MiniPf L φ
  | mp {φ α} : MiniPf L (.impl φ α) → MiniPf L φ → MiniPf L α
  | implTrans {φ ψ χ} :
      MiniPf L (.impl φ ψ) → MiniPf L (.impl ψ χ) → MiniPf L (.impl φ χ)
  | weakenImpl {φ ψ} : MiniPf L ψ → MiniPf L (.impl φ ψ)
  | impS2 {φ ψ χ} :
      MiniPf L (.impl φ (.impl ψ χ)) → MiniPf L (.impl φ ψ) → MiniPf L (.impl φ χ)
  -- ── the Family-B additions ──
  | implRefl (φ) : MiniPf L (.impl φ φ)
  | implK (φ ψ) : MiniPf L (.impl φ (.impl ψ φ))

/-- `implK` + `mp` derives `weakenImpl` — K-as-formula subsumes the current rule
    (kept primitive in the real system only for transcript-cost tightness). -/
theorem weakenImpl_derivable (L : Formula → Prop) {φ ψ : Formula}
    (h : MiniPf L ψ) : MiniPf L (.impl φ ψ) :=
  .mp (.implK ψ φ) h

/-- The CURRENT engine census invariant, distilled: tail-recurse through `.impl`. -/
def TailBad (A : Formula) : Formula → Prop
  | .impl _ ψ => TailBad A ψ
  | φ => φ = A

/-- The REPAIRED invariant: forbidden tail, unforbidden antecedents — compositional. -/
def Guarded (A : Formula) : Formula → Prop
  | .impl α ψ => Guarded A ψ ∧ ¬ Guarded A α
  | φ => φ = A

def A₀ : Formula := .plays .self .opp Action.C

/-- **THE CANARY**: with `implRefl` in the system, the tail-invariant census is
    FALSE — even over an EMPTY leaf layer, `⊢ A₀ → A₀` is derivable and TailBad.
    (So `cimcic_bot_no_provable_forbidden` et al. do not survive `implRefl` as
    stated; they need the `Guarded` repair.) -/
theorem old_invariant_falsified :
    ∃ φ, MiniPf (fun _ => False) φ ∧ TailBad A₀ φ :=
  ⟨.impl A₀ A₀, .implRefl A₀, by show A₀ = A₀; rfl⟩

/-- The reflexive shape self-destructs under the repaired invariant. -/
theorem new_invariant_immune : ¬ Guarded A₀ (.impl A₀ A₀) := by
  intro h
  obtain ⟨hg, hng⟩ := h
  exact hng hg

/-- **THE REPAIRED CENSUS** — closed under the FULL glue family including
    `implRefl`/`implK`. The `by_cases` on antecedents is the new proof pattern
    (each premise-carrying rule refutes the forbidden branch via its own IH). -/
theorem guarded_census (L : Formula → Prop) (A : Formula)
    (hL : ∀ φ, L φ → ¬ Guarded A φ) :
    ∀ φ, MiniPf L φ → ¬ Guarded A φ := by
  intro φ h
  induction h with
  | leaf hφ => exact hL _ hφ
  | @mp φ' α h1 h2 ih1 ih2 =>
      intro hF
      by_cases hφ : Guarded A φ'
      · exact ih2 hφ
      · exact ih1 (show Guarded A (.impl φ' α) from ⟨hF, hφ⟩)
  | @implTrans φ' ψ χ h1 h2 ih1 ih2 =>
      intro hF
      obtain ⟨hχ, hφn⟩ := hF
      by_cases hψ : Guarded A ψ
      · exact ih1 (show Guarded A (.impl φ' ψ) from ⟨hψ, hφn⟩)
      · exact ih2 (show Guarded A (.impl ψ χ) from ⟨hχ, hψ⟩)
  | @weakenImpl φ' ψ h ih =>
      intro hF
      obtain ⟨hψ, _⟩ := hF
      exact ih hψ
  | @impS2 φ' ψ χ h1 h2 ih1 ih2 =>
      intro hF
      obtain ⟨hχ, hφn⟩ := hF
      by_cases hψ : Guarded A ψ
      · exact ih2 (show Guarded A (.impl φ' ψ) from ⟨hψ, hφn⟩)
      · exact ih1 (show Guarded A (.impl φ' (.impl ψ χ)) from ⟨⟨hχ, hψ⟩, hφn⟩)
  | implRefl φ' =>
      intro hF
      obtain ⟨hg, hng⟩ := hF
      exact hng hg
  | implK φ' ψ =>
      intro hF
      obtain ⟨⟨hg, _⟩, hng⟩ := hF
      exact hng hg

/-- The repaired invariant still covers the REAL use-case: a bot guard
    `(p plays a vs q) → (r plays b vs s)` with distinct antecedent is `Guarded`
    (so the strengthened censuses still conclude guard-unprovability). -/
theorem guarded_covers_real_guards (p q r s : Prog) (a b : Action)
    (hne : Formula.plays p q a ≠ .plays r s b) :
    Guarded (.plays r s b) (.impl (.plays p q a) (.plays r s b)) :=
  ⟨show Formula.plays r s b = .plays r s b from rfl, fun h => hne h⟩

end CensusInvariant

/-! ## §3 — The gap, closed (HISTORICAL NOTE)

Before the 2026-07-28 integration this section proved the OPPOSITE: `⊢ A → A` for
`A := DBot plays C vs CIMCIC k` was unprovable at every budget (a corollary of the
then-tail-invariant CIMCIC census `dbot_no_provable_forbidden`) — the kernel-checked
witness that `implRefl` strictly extends `S`. With `Pf.implRefl` landed, the same
tautology is now a one-liner at its own size — the gap this spike identified is closed,
and the old negative statement is (by design) no longer true. -/

theorem implRefl_now_in_S (k : Nat) :
    Pf (Formula.impl (.plays DBot (CIMCIC k) Action.C)
                     (.plays DBot (CIMCIC k) Action.C)).size
       (.impl (.plays DBot (CIMCIC k) Action.C)
              (.plays DBot (CIMCIC k) Action.C)) :=
  .implRefl _ (Nat.le_refl _)

/-! ## §4 — Family A: the general in-frame rule `ctxBranch`

**The problem it solves.** `eval` runs a bot's body IN FRAME: every `.search` guard
on the way to the played branch substitutes the FULL `me`/`opponent`, not the branch
as a standalone program. So "S reads the source" needs one rule per *then-path shape*
— hence the fused zoo (`searchBranch`, `iteBranchSearch_t`, `searchThenSearch_t`, …),
one constructor per nesting pattern, growing with the bots.

**The general rule.** Reify the then-path as a first-class telescope `EvalCtx`
(hole | search-layer | ite-layer), with
  * `plug C p`  — the bot whose body is `C` wrapped around branch `p`;
  * `guards C me opp` — the in-frame guard facts, outermost first
    (`□_g (ψ.subst me opp)` per search layer; `opp plays a' vs .bot z` per ite layer,
    the guard restricted to the frame-independent probe `.sim .opp (.bot z)` exactly
    as in `iteBranchSearch_t` — arbitrary ite guards are frame-DEPENDENT and hence
    unsound to expose as standalone `.plays` atoms);
and ONE constructor concluding the implication chain
  `guards₁ → guards₂ → … → (me plays a)`   for `me = plug C (.const a)`.
Every fused reading rule's conclusion is an INSTANCE (`rfl` demos below); depth-3+
shapes (PrudentBot3) come for free; `searchThenSearch_t`-style single-box collapses
are DERIVED via `boxIntro` + `mp` on the inner guard. Family A stops growing. -/

/-- The then-path telescope. Each layer records the guard and the else-branch
    (needed to reconstruct the source), innermost at the `hole`. -/
inductive EvalCtx where
  | hole
  | searchT (g : Nat) (ψ : Formula) (elseB : Prog) (rest : EvalCtx)
  | iteT (z : Prog) (a' : Action) (elseB : Prog) (rest : EvalCtx)

/-- Rebuild the source program around the branch. -/
def EvalCtx.plug : EvalCtx → Prog → Prog
  | .hole, p => p
  | .searchT g ψ e rest, p => .search g ψ (rest.plug p) e
  | .iteT z a' e rest, p => .ite (.sim .opp (.bot z)) a' (rest.plug p) e

/-- The in-frame guard facts along the spine, outermost first. -/
def EvalCtx.guards (me opponent : Prog) : EvalCtx → List Formula
  | .hole => []
  | .searchT g ψ _ rest => .box g (ψ.subst me opponent) :: rest.guards me opponent
  | .iteT z a' _ rest => .plays opponent (.bot z) a' :: rest.guards me opponent

/-- Right-fold a guard list into an implication chain. -/
def implChain (gs : List Formula) (tgt : Formula) : Formula :=
  gs.foldr .impl tgt

/-- `interp` of an implication chain, introduction form. -/
theorem implChain_interp {tgt : Formula} :
    ∀ (gs : List Formula), ((∀ ψ ∈ gs, ψ.interp) → tgt.interp) →
      (implChain gs tgt).interp := by
  intro gs
  induction gs with
  | nil =>
      intro h
      exact h (fun ψ hψ => nomatch hψ)
  | cons g gs ih =>
      intro h hgI
      refine ih (fun hall => h ?_)
      intro ψ hψ
      rcases List.mem_cons.mp hψ with h1 | h2
      · exact h1 ▸ hgI
      · exact hall ψ h2

/-- **The soundness core of `ctxBranch`**: if every guard on the spine holds
    (in-frame), evaluation reaches the plugged constant. Induction on the telescope;
    the search layer commits via `proofSearch_spec`, the ite layer via the
    frame-independence of the `.sim .opp (.bot z)` probe. -/
theorem evalCtx_sound (me opponent : Prog) (a : Action) :
    ∀ (C : EvalCtx), (∀ ψ ∈ C.guards me opponent, ψ.interp) →
      ∃ n, eval n me opponent (C.plug (.const a)) = some a := by
  intro C
  induction C with
  | hole => exact fun _ => ⟨1, rfl⟩
  | searchT g ψ e rest ih =>
      intro hg
      have hhead : Pf g (ψ.subst me opponent) := hg _ List.mem_cons_self
      have hps : proofSearch g (ψ.subst me opponent) = true :=
        (proofSearch_spec _ _).2 hhead
      obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
      refine ⟨n + 1, ?_⟩
      show eval (n + 1) me opponent (.search g ψ (rest.plug (.const a)) e) = some a
      rw [eval, if_pos hps]
      exact hn
  | iteT z a' e rest ih =>
      intro hg
      have hhead : (Formula.plays opponent (.bot z) a').interp :=
        hg _ List.mem_cons_self
      obtain ⟨m, hm⟩ := hhead
      have hguard : eval (m + 1) me opponent (.sim .opp (.bot z)) = some a' :=
        eval_sim_opp_bot_of_play m me opponent z a' hm
      obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
      have hr : (a' == a') = true := by cases a' <;> rfl
      refine ⟨max (m + 1) n + 1, ?_⟩
      show eval (max (m + 1) n + 1) me opponent
        (.ite (.sim .opp (.bot z)) a' (rest.plug (.const a)) e) = some a
      rw [eval, eval_mono_le hguard _ (Nat.le_max_left _ _)]
      simp only [bind, Option.bind]
      rw [if_pos hr]
      exact eval_mono_le hn _ (Nat.le_max_right _ _)

/-- **The `ctxBranch` soundness certificate** (the machine gate): the proposed
    constructor's conclusion is interp-TRUE whenever its side conditions hold.
    Proposed rule (costs mirror the fused leaves — conclusion size, ≤ k):

        | ctxBranch (C : EvalCtx) (a : Action) (me opponent : Prog)
            (hme : me = C.plug (.const a)) :
            (implChain (C.guards me opponent) (.plays me opponent a)).size ≤ k →
            Pf k (implChain (C.guards me opponent) (.plays me opponent a))       -/
theorem ctxBranch_certificate (C : EvalCtx) (a : Action) (me opponent : Prog)
    (hme : me = C.plug (.const a)) :
    (implChain (C.guards me opponent) (.plays me opponent a)).interp := by
  subst hme
  refine implChain_interp _ (fun hg => ?_)
  obtain ⟨n, hn⟩ := evalCtx_sound (C.plug (.const a)) opponent a C hg
  exact ⟨n, hn⟩

/-! ### Instance demos — the fused zoo is subsumed, definitionally -/

/-- `searchBranch`'s conclusion = depth-1 search telescope. -/
example (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog) :
    implChain ((EvalCtx.searchT g ψ (.const b) .hole).guards me opponent)
        (.plays me opponent a)
      = .impl (.box g (ψ.subst me opponent)) (.plays me opponent a) := rfl

/-- `searchBranch`'s source shape = depth-1 plug. -/
example (g : Nat) (ψ : Formula) (a b : Action) :
    (EvalCtx.searchT g ψ (.const b) .hole).plug (.const a)
      = .search g ψ (.const a) (.const b) := rfl

/-- `iteBranchSearch_t`'s source shape (the PrudentBot `.ite`-over-`.search`)
    = ite-layer ∘ search-layer. -/
example (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula) (q : Prog) :
    (EvalCtx.iteT z a' q (.searchT g ψ (.const c1) .hole)).plug (.const c0)
      = .ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q := rfl

/-- `iteBranchSearch_t`'s conclusion = the corresponding 2-guard chain. -/
example (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula) (q me opponent : Prog) :
    implChain ((EvalCtx.iteT z a' q (.searchT g ψ (.const c1) .hole)).guards me opponent)
        (.plays me opponent c0)
      = .impl (.plays opponent (.bot z) a')
              (.impl (.box g (ψ.subst me opponent)) (.plays me opponent c0)) := rfl

/-- Depth-3 (a three-condition PrudentBot3) — beyond EVERY current fused rule,
    free under the telescope. -/
example (k₁ k₂ k₃ : Nat) (ψ₁ ψ₂ ψ₃ : Formula) (e₁ e₂ e₃ : Prog) (c0 : Action) :
    (EvalCtx.searchT k₁ ψ₁ e₁ (.searchT k₂ ψ₂ e₂ (.searchT k₃ ψ₃ e₃ .hole))).plug
        (.const c0)
      = .search k₁ ψ₁ (.search k₂ ψ₂ (.search k₃ ψ₃ (.const c0) e₃) e₂) e₁ := rfl

end PD.Spikes.FamilyCompletion
