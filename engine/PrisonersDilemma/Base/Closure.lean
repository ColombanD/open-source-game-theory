import PrisonersDilemma.ProofSystem

/-!
# Base/Closure — THE FAMILY CLOSURE CERTIFICATES (step 5 of the completion program)

`Research/Notes/FAMILY_COMPLETION_DESIGN.md`, 2026-07-28. The proof system `S`
(`Pf`, 27 constructors in three families) is CLOSED in the following senses, each
certified here by a kernel-checked theorem rather than a claim:

* **Family B (logical glue)**: identity is a leaf (`identity_provable` —
  historically UNDERIVABLE, the gap that drove the program), and K-as-formula makes
  `weakenImpl` REDUNDANT (`weakenImpl_from_implK`). NOTE the precise scope: this
  certifies the program's checklist, NOT propositional completeness of the →/¬
  fragment — S-combination and contraposition live only as RULES, and without the
  deduction theorem the rule forms are strictly weaker than axiom forms (exchange /
  Peirce are unsettled). The certifiable completeness target is spelled out in
  `FAMILY_COMPLETION_DESIGN.md` (closure audit, 2026-07-28).
* **Family A (reading rules) is closed over the search dimension at every depth**:
  `searchChain_reads_all_depths` reads any `.search`-telescope in one rule;
  `searchBranch_from_searchChain` shows the depth-1 primitive is an instance (with
  its const-else restriction LIFTED); and the flagship
  `searchThenSearch_t_from_searchChain` DERIVES the stacked-search primitive's
  conclusion from the telescope + the modal tier — the two historical fused rules
  survive only as conveniences, not as expressiveness.

**The ite frontier (2026-07-28): the THEN-polarity mixed telescope is LANDED** —
`Pf.ctxChain` reads any stack of `.search` tests and `.ite`-probe layers (then-descent,
frame-independent probes) at every depth, subsuming both `searchChain`
(`searchChain_from_ctxChain` below) and the fused `iteBranchSearch_t`
(`iteBranchSearch_from_ctxChain` — a definitional instance). The censuses survive via
the set-valued `TailToS` kernel (Base/Exclusion) plus one dischargeable `hctx`
disequality per instance; no outcome changed (the flip-claim of an earlier draft was
RETRACTED — every probe antecedent is Gödelian-uncertifiable, floor-priced, or false:
`Research/Spikes/family_completion/ProvenanceSpike.lean`, `cimcic_probe_uncertifiable`).

**What remains open — the ELSE polarity (full simulator transparency, what would read
DBot's cooperation outright):** sound (the soundness lemma was validated for both
polarities) and it flips nothing — but it genuinely FALSIFIES the floor censuses: with
an else rule, `implTrans` composes a searcher's own `searchBranch` self-read with the
else-probe chain into a provable box-headed chain to the floor target — concretely
`□_k(gC-inst) → (OBot plays D vs CupodBot k)` via Cupod's then-read
`□_k(gC-inst) → (Cupod plays D vs .bot CooperateBot)` ∘ OBot's else-chain — and
excluding such chains needs an avoid-set recursively closed over the modal tier
(`axKf` manufactures box-tailed implications with arbitrary antecedents, defeating
every finite widening). That census re-architecture is the honest open frontier;
since the else rule adds no extractable theorem (nothing to extract — the probes are
priced), it is deferred, not smuggled in. Full record:
`FAMILY_COMPLETION_DESIGN.md`.
-/

open PD

namespace PD.BaseTheorems

/-- **Family-A closure, search dimension**: every `.search`-telescope of every depth
    is readable — its full in-frame guard chain is provable at its own size. -/
theorem searchChain_reads_all_depths (g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)
    (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
    (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁) :
    ∃ K, Pf K (.impl (.box g₁ (ψ₁.subst me opponent))
      (implChain (searchGuards me opponent L) (.plays me opponent a))) :=
  ⟨_, .searchChain g₁ ψ₁ e₁ L a me opponent hme (Nat.le_refl _)⟩

/-- `searchBranch` is the depth-1 instance of the telescope — with the else-branch
    restriction LIFTED (`searchBranch` demanded `.const b`; the telescope reads any
    else). -/
theorem searchBranch_from_searchChain (g : Nat) (ψ : Formula) (a : Action)
    (e me opponent : Prog) (hme : me = .search g ψ (.const a) e) (k : Nat)
    (hle : (Formula.impl (.box g (ψ.subst me opponent))
      (.plays me opponent a)).size ≤ k) :
    Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)) :=
  .searchChain g ψ e [] a me opponent hme hle

/-- **The stacked-search primitive is redundant**: `searchThenSearch_t`'s exact
    conclusion — the single-box Löb-premise collapse `□_{k₁} ψ₁' → me plays c0` from a
    held proof of the inner guard — is DERIVABLE from the telescope reading plus the
    modal tier (`boxIntro` to enter the box at the proof's own budget, `boxMono` up to
    the source literal `k₂`, `weakenImpl` + `impS2` to discharge the middle guard).
    The primitive stays as a transcript-cheaper convenience; expressiveness-wise,
    Family A needed only the telescope. -/
theorem searchThenSearch_t_from_searchChain (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula)
    (c0 c1 : Action) (q me opponent : Prog)
    (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)
    (hprud : Pf m (ψ₂.subst me opponent)) (hmk : m ≤ k₂) :
    ∃ K, Pf K (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)) := by
  -- the inner guard, boxed at its own budget…
  have hb1 : Pf (m + (Formula.box m (ψ₂.subst me opponent)).size)
      (.box m (ψ₂.subst me opponent)) :=
    .boxIntro m _ _ hprud (Nat.le_refl _)
  -- …lifted to the source literal `k₂`…
  have hmono : Pf ((Formula.impl (.box m (ψ₂.subst me opponent))
      (.box k₂ (ψ₂.subst me opponent))).size)
      (.impl (.box m (ψ₂.subst me opponent)) (.box k₂ (ψ₂.subst me opponent))) :=
    .boxMono m k₂ _ _ hmk (Nat.le_refl _)
  have hb2 : Pf _ (.box k₂ (ψ₂.subst me opponent)) :=
    .mp _ _ _ _ hmono hb1 (Nat.le_refl _)
  -- …made available under the outer guard…
  have hAB : Pf _ (.impl (.box k₁ (ψ₁.subst me opponent))
      (.box k₂ (ψ₂.subst me opponent))) :=
    .weakenImpl _ _ _ hb2 (Nat.le_refl _)
  -- …and composed against the depth-2 telescope chain.
  have hchain : Pf ((Formula.impl (.box k₁ (ψ₁.subst me opponent))
      (.impl (.box k₂ (ψ₂.subst me opponent)) (.plays me opponent c0))).size)
      (.impl (.box k₁ (ψ₁.subst me opponent))
        (.impl (.box k₂ (ψ₂.subst me opponent)) (.plays me opponent c0))) :=
    .searchChain k₁ ψ₁ q [(k₂, ψ₂, .const c1)] c0 me opponent hme (Nat.le_refl _)
  exact ⟨_, .impS2 _ _ _ _ _ _ hchain hAB (Nat.le_refl _)⟩

/-- **Family-B closure**: `weakenImpl` is redundant — K-as-formula + modus ponens
    derive it (the primitive stays for transcript tightness only). -/
theorem weakenImpl_from_implK (φ ψ : Formula) (m : Nat) (h : Pf m ψ) :
    ∃ K, Pf K (.impl φ ψ) :=
  ⟨_, .mp _ _ _ _ (.implK ψ φ (Nat.le_refl _)) h (Nat.le_refl _)⟩

/-- **The gap that drove the program, closed**: identity, historically UNDERIVABLE in
    `S` (kernel-checked corollary of the CIMCIC census, pre-integration), is now a
    leaf at its own size. -/
theorem identity_provable (φ : Formula) :
    Pf (Formula.impl φ φ).size (.impl φ φ) :=
  .implRefl φ (Nat.le_refl _)

/-! ## The MIXED-telescope closure certificates (the ite frontier, 2026-07-28)

`ctxChain` closes Family A over search+ite-probe THEN-nesting at every depth. The two
older readers are its instances: `searchChain` via all-`searchL` layers, and
`iteBranchSearch_t` (the fused PrudentBot-shape rule) as the depth-2
`iteL`-over-`searchL` case — definitionally, no glue. -/

theorem ctxGuards_map_searchL (me opponent : Prog) :
    ∀ (L : List (Nat × Formula × Prog)),
      ctxGuards me opponent (L.map fun t => .searchL t.1 t.2.1 t.2.2)
        = searchGuards me opponent L
  | [] => rfl
  | (g, ψ, e) :: L => by
      simp only [List.map, ctxGuards, ctxGuard, searchGuards,
        ctxGuards_map_searchL me opponent L]

theorem ctxPlug_map_searchL :
    ∀ (L : List (Nat × Formula × Prog)) (p : Prog),
      ctxPlug (L.map fun t => .searchL t.1 t.2.1 t.2.2) p = searchPlug L p
  | [], _ => rfl
  | (g, ψ, e) :: L, p => by
      simp only [List.map, ctxPlug, searchPlug, ctxPlug_map_searchL L p]

/-- **The search telescope is subsumed**: `searchChain`'s exact conclusion via
    `ctxChain` with all-`searchL` layers. -/
theorem searchChain_from_ctxChain (g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)
    (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
    (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁) (k : Nat)
    (hle : (Formula.impl (.box g₁ (ψ₁.subst me opponent))
      (implChain (searchGuards me opponent L) (.plays me opponent a))).size ≤ k) :
    Pf k (.impl (.box g₁ (ψ₁.subst me opponent))
      (implChain (searchGuards me opponent L) (.plays me opponent a))) := by
  have hplug : me = ctxPlug
      (.searchL g₁ ψ₁ e₁ :: (L.map fun t => .searchL t.1 t.2.1 t.2.2)) (.const a) := by
    rw [hme]
    show Prog.search g₁ ψ₁ (searchPlug L (.const a)) e₁
      = .search g₁ ψ₁ (ctxPlug (L.map fun t => .searchL t.1 t.2.1 t.2.2) (.const a)) e₁
    rw [ctxPlug_map_searchL]
  have h := Pf.ctxChain (.searchL g₁ ψ₁ e₁)
    (L.map fun t => .searchL t.1 t.2.1 t.2.2) a me opponent hplug (k := k)
    (by simpa only [ctxGuard, ctxGuards_map_searchL] using hle)
  simpa only [ctxGuard, ctxGuards_map_searchL] using h

/-- **The fused ite rule is subsumed**: `iteBranchSearch_t`'s exact conclusion is the
    depth-2 mixed telescope (`iteL` over `searchL`) — definitional instance. -/
theorem iteBranchSearch_from_ctxChain (g : Nat) (z : Prog) (a' c0 c1 : Action)
    (ψ : Formula) (q me opponent : Prog)
    (hme : me = .ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q)
    (k : Nat)
    (hle : (Formula.impl (.plays opponent (.bot z) a')
      (.impl (.box g (ψ.subst me opponent)) (.plays me opponent c0))).size ≤ k) :
    Pf k (.impl (.plays opponent (.bot z) a')
      (.impl (.box g (ψ.subst me opponent)) (.plays me opponent c0))) :=
  Pf.ctxChain (.iteL z a' q) [.searchL g ψ (.const c1)] c0 me opponent hme hle

/-! ## The `.sim` composition certificates (Family A's sim dimension, 2026-07-28)

`.sim` needs no telescope: `simStep` is fully general at depth 1 (any body), and
DEEPER nestings COMPOSE — a reading that concludes the substituted body's play
chains through the wrapper by `implTrans`. These certify the composition principle,
closing the audit's remainder (d): any `(sim ∘ search ∘ ite ∘ …)` nesting whose
inner layers are readable is readable, by iterating these over the inner readings
(`ctxChain` conclusions, `simStep` instances, or further compositions). -/

/-- **The generic reading composition**: readings chain — `A → B` and `B → C` give
    `A → C` at the summed transcript. The `.sim`/`.bot` closure lemmas below are its
    instances against the step leaves; deeper nestings iterate it. -/
theorem read_compose {A B C : Formula} {m n : Nat}
    (h1 : Pf m (.impl A B)) (h2 : Pf n (.impl B C)) :
    Pf (m + n + (Formula.impl A C).size) (.impl A C) :=
  .implTrans A B C m n h1 h2 (Nat.le_refl _)

/-- **`.sim` composes**: a reading of the substituted body's play lifts through the
    `.sim` wrapper. Depth-`n` sim-nesting is `n` applications of this lemma. -/
theorem simStep_compose (me p q opponent : Prog) (a : Action) (A : Formula) (m : Nat)
    (hme : me = .sim p q)
    (h : Pf m (.impl A (.plays (p.subst me opponent) (q.subst me opponent) a))) :
    ∃ K, Pf K (.impl A (.plays me opponent a)) :=
  ⟨_, read_compose h (.simStep me p q opponent a hme (Nat.le_refl _))⟩

/-- **`.bot`-wrapped `.sim` composes** — the `botSimStep` twin. -/
theorem botSimStep_compose (me p q opponent : Prog) (a : Action) (A : Formula) (m : Nat)
    (hme : me = .bot (.sim p q))
    (h : Pf m (.impl A (.plays (p.subst me opponent) (q.subst me opponent) a))) :
    ∃ K, Pf K (.impl A (.plays me opponent a)) :=
  ⟨_, read_compose h (.botSimStep me p q opponent a hme (Nat.le_refl _))⟩

/-! ## THE ADMISSIBLE DEDUCTION THEOREM (Family-B completion, 2026-07-28)

With K (`implK`) and S (`implS`) as object formulas and `mp`, Family B carries the
full basis of the POSITIVE implicational fragment. The deduction theorem is proven
here as a META-theorem ABOUT `S` — `Deriv` (single-hypothesis Hilbert derivations)
never enters the object system, so the transcript-cost model stays honest: every
discharge step maps to `implRefl`/`weakenImpl`/`impS2` at computable budgets.

The scope boundaries, both principled (recorded in `FAMILY_COMPLETION_DESIGN.md`):
* PEIRCE'S LAW (classical →) is SOUND and census-safe but blocked by the TREE
  SUBSTRATE: its crossing is `call/cc`, and T49's `boxInvGo` walker is a constructive
  (λ-calculus) evaluator — `fundamental`'s totality would be falsified. The proof-term
  substrate is intrinsically INTUITIONISTIC; classical implicational reasoning stays
  at the RULE level (`contrapose`, `negElim` — soundness is classical, the TERMS are
  not).
* The classical NEGATION axiom-forms are census-blocked (the false-antecedent wall,
  same as the ite-ELSE frontier). Negation stays rule-based. -/

/-- Hilbert-style derivations from ONE hypothesis: the hypothesis itself, any
    `S`-theorem, and modus ponens. -/
inductive Deriv (hyp : Formula) : Formula → Prop
  | hypo : Deriv hyp hyp
  | thm {φ : Formula} {k : Nat} : Pf k φ → Deriv hyp φ
  | mp {φ ψ : Formula} : Deriv hyp (.impl φ ψ) → Deriv hyp φ → Deriv hyp ψ

/-- **THE DEDUCTION THEOREM, admissible**: `hyp ⊢ ψ` yields `⊢ hyp → ψ`. The three
    cases are exactly `implRefl` / `weakenImpl` / `impS2` — the S-combinator rule IS
    the deduction theorem's `mp`-case, which is why Family B never needed the
    constructor form. -/
theorem deduction_theorem {hyp ψ : Formula} (d : Deriv hyp ψ) :
    ∃ K, Pf K (.impl hyp ψ) := by
  induction d with
  | hypo => exact ⟨_, .implRefl hyp (Nat.le_refl _)⟩
  | thm h => exact ⟨_, .weakenImpl _ _ _ h (Nat.le_refl _)⟩
  | mp d1 d2 ih1 ih2 =>
      obtain ⟨K1, h1⟩ := ih1
      obtain ⟨K2, h2⟩ := ih2
      exact ⟨_, .impS2 _ _ _ _ _ _ h1 h2 (Nat.le_refl _)⟩

/-- **SKK = I**: identity is derivable from K and S alone — `implRefl` joins
    `weakenImpl` as a transcript-convenience, not expressiveness. -/
theorem identity_from_KS (φ : Formula) : ∃ K, Pf K (.impl φ φ) := by
  have hS := Pf.implS φ (.impl φ φ) φ (k := (Formula.impl (.impl φ (.impl (.impl φ φ) φ))
    (.impl (.impl φ (.impl φ φ)) (.impl φ φ))).size) (Nat.le_refl _)
  have hK1 := Pf.implK φ (.impl φ φ)
    (k := (Formula.impl φ (.impl (.impl φ φ) φ)).size) (Nat.le_refl _)
  have h1 := Pf.mp _ _ _ _ hS hK1 (Nat.le_refl _)
  have hK2 := Pf.implK φ φ (k := (Formula.impl φ (.impl φ φ)).size) (Nat.le_refl _)
  exact ⟨_, .mp _ _ _ _ h1 hK2 (Nat.le_refl _)⟩

end PD.BaseTheorems
