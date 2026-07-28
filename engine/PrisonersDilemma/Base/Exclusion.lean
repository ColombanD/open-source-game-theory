import PrisonersDilemma.Base.Soundness

/-!
# Base/Exclusion — structural exclusion: what `S` can NOT conclude

The positive layers certify plays; this file is the NEGATIVE direction, needed by the
honest outcome theorems for the floor-killed pairs: `¬Pf k φ` facts for TRUE formulas,
where soundness gives nothing and only cost accounting can close the guard.

**THE INVARIANT (Guarded form, 2026-07-28).** Every census here runs on

    TailTo T (.impl α ψ) := TailTo T ψ ∧ ¬ TailTo T α
    TailTo T φ           := (φ = T)            -- non-`.impl`

— "φ is an implication chain whose spine tail is `T`, reachable only through
UNFORBIDDEN antecedents." The former invariant was the bare spine-tail function
(`rightTail φ = T`), which is closed under the CURRENT rules only because every
implication-producing rule carries a premise containing its conclusion's tail. The
planned Family-B leaves (`implRefl : ⊢ φ → φ`, `implK : ⊢ φ → (ψ → φ)`) are
premise-free with an arbitrary tail and FALSIFY that census as stated (machine-checked:
`Research/Spikes/family_completion/FamilyCompletionSpike.lean` §2). Under `TailTo` the
reflexive/K shapes self-destruct (`⟨h, hn⟩` with `hn h`), and every premise-carrying
rule closes via `by_cases` on the antecedent — see `no_provable_tailTo_floor`. This
file is therefore ALREADY closed under the Family-B extension; new constructors add
one arm per census, nothing more. (Design: `Research/Notes/FAMILY_COMPLETION_DESIGN.md`.)

Contents:
* `Formula.size_pos` — every formula costs at least one character.
* `rightTail` — the bare spine-tail function (kept for reference/compat; the census
  theorems no longer use it).
* `TailTo` — the guarded spine-tail predicate (the census invariant).
* `ReadableMe` — the six player shapes whose plays the `Pf` source-transparency
  bridge can conclude.
* `tail_plays_readable` — THE CENSUS: a `Pf`'d formula with a guarded plays-atom
  spine tail names a bridge-readable player.
* `no_provable_tailTo_floor` — the generic budget-strong-induction kernel: the
  `search_f` floor as a cost lower bound, parameterized by an atom-killer and the
  player's shape disequalities. The three pair-shaped floor lemmas
  (`no_provable_probeFirst_tail`, `…_botOpp`, `no_provable_searcherPlay_tail`) are
  INSTANCES.
* `no_provable_tailTo_unreadable` — the budget-FREE census for fully-unreadable
  target players (the CIMCIC/DIMCID Gödelian-guard pattern): certificates impossible
  at every budget + player unreadable ⇒ no `Pf` at any budget.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-- Every formula costs at least one character. -/
theorem _root_.PD.Formula.size_pos : ∀ φ : Formula, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp only [Formula.size] <;> omega

/-- The final consequent of a right-nested implication chain — the "spine tail".
    `rightTail (φ₁ → (φ₂ → … → ψ))` is `ψ` for non-`.impl` `ψ`.

    **Superseded as a census invariant** by `TailTo` (see the header): kept because it
    remains the honest *reading* of "what the chain concludes", and for compatibility. -/
def rightTail : Formula → Formula
  | .impl _ ψ => rightTail ψ
  | φ => φ

@[simp] theorem rightTail_impl (φ ψ : Formula) :
    rightTail (.impl φ ψ) = rightTail ψ := rfl
@[simp] theorem rightTail_plays (p q : Prog) (a : Action) :
    rightTail (.plays p q a) = .plays p q a := rfl
@[simp] theorem rightTail_neg (φ : Formula) : rightTail (.neg φ) = .neg φ := rfl
@[simp] theorem rightTail_box (n : Nat) (φ : Formula) :
    rightTail (.box n φ) = .box n φ := rfl
@[simp] theorem rightTail_eq (p q : Prog) : rightTail (.eq p q) = .eq p q := rfl
@[simp] theorem rightTail_diag (g : Nat) (φ : Formula) :
    rightTail (.diag g φ) = .diag g φ := rfl

/-- **The census invariant**: `TailTo T φ` — φ is a right-nested implication chain
    whose spine tail is `T` and whose antecedents never themselves reach `T`. The
    second conjunct is what survives premise-free implication leaves (`implRefl`,
    `implK`): on `⊢ T → T` the two conjuncts annihilate. See the file header. -/
def TailTo (T : Formula) : Formula → Prop
  | .impl α ψ => TailTo T ψ ∧ ¬ TailTo T α
  | φ => φ = T

@[simp] theorem TailTo_impl (T φ ψ : Formula) :
    TailTo T (.impl φ ψ) ↔ (TailTo T ψ ∧ ¬ TailTo T φ) := Iff.rfl
@[simp] theorem TailTo_plays (T : Formula) (p q : Prog) (a : Action) :
    TailTo T (.plays p q a) ↔ (Formula.plays p q a = T) := Iff.rfl
@[simp] theorem TailTo_neg (T φ : Formula) :
    TailTo T (.neg φ) ↔ (Formula.neg φ = T) := Iff.rfl
@[simp] theorem TailTo_box (T : Formula) (n : Nat) (φ : Formula) :
    TailTo T (.box n φ) ↔ (Formula.box n φ = T) := Iff.rfl
@[simp] theorem TailTo_eq (T : Formula) (p q : Prog) :
    TailTo T (.eq p q) ↔ (Formula.eq p q = T) := Iff.rfl
@[simp] theorem TailTo_diag (T : Formula) (g : Nat) (φ : Formula) :
    TailTo T (.diag g φ) ↔ (Formula.diag g φ = T) := Iff.rfl

/-- A bare plays-atom trivially satisfies its own `TailTo`. -/
theorem TailTo_self (T : Formula) : TailTo T T ∨ True := Or.inr trivial

/-! ### The SET-valued census invariant (the ite frontier, 2026-07-28)

`ctxChain` makes probe-implication chains provable premise-free: for an
`.ite`-simulator target `P` (DBot's shape), `.impl (.plays O (.bot z) r) (P plays
aTgt)` is a `ctxChain` conclusion — IN the singleton `TailTo` class and PROVABLE, so
the singleton census statement is FALSE for such targets. The repair prices the probe:
widen the forbidden tail-SET from `{T}` to `{T} ∪ {the decomposition's probe atoms}`
and supply atom-killers for every member (the probes are Gödelian-uncertifiable or
floor-priced in every zoo instance — kernel-checked audit:
`Research/Spikes/family_completion/ProvenanceSpike.lean`). Inside the widened class
the `ctxChain` conclusion's head antecedent IS a forbidden atom, so the chain falls
OUT of the class (`¬TailToS` on antecedents), while `mp`-extraction through it dies on
the priced probe. All rule-kill hypotheses become ACTION-refined, because the probe
atoms' players are searchers whose then-plays ARE readable — only the action mismatch
(probes record else-plays) closes those arms. -/

def TailToS (S : Formula → Prop) : Formula → Prop
  | .impl α ψ => TailToS S ψ ∧ ¬ TailToS S α
  | φ => S φ

@[simp] theorem TailToS_impl (S : Formula → Prop) (φ ψ : Formula) :
    TailToS S (.impl φ ψ) ↔ (TailToS S ψ ∧ ¬ TailToS S φ) := Iff.rfl
@[simp] theorem TailToS_plays (S : Formula → Prop) (p q : Prog) (a : Action) :
    TailToS S (.plays p q a) ↔ S (.plays p q a) := Iff.rfl
@[simp] theorem TailToS_neg (S : Formula → Prop) (φ : Formula) :
    TailToS S (.neg φ) ↔ S (.neg φ) := Iff.rfl
@[simp] theorem TailToS_box (S : Formula → Prop) (n : Nat) (φ : Formula) :
    TailToS S (.box n φ) ↔ S (.box n φ) := Iff.rfl
@[simp] theorem TailToS_eq (S : Formula → Prop) (p q : Prog) :
    TailToS S (.eq p q) ↔ S (.eq p q) := Iff.rfl
@[simp] theorem TailToS_diag (S : Formula → Prop) (g : Nat) (φ : Formula) :
    TailToS S (.diag g φ) ↔ S (.diag g φ) := Iff.rfl

/-- The singleton set recovers the original invariant. -/
theorem TailToS_singleton (T : Formula) : ∀ φ, TailToS (· = T) φ ↔ TailTo T φ
  | .impl α ψ => by
      rw [TailToS_impl, TailTo_impl, TailToS_singleton T ψ, TailToS_singleton T α]
  | .plays _ _ _ => Iff.rfl
  | .neg _ => Iff.rfl
  | .box _ _ => Iff.rfl
  | .eq _ _ => Iff.rfl
  | .diag _ _ => Iff.rfl

/-- `TailToS` through a folded guard chain (the `searchChain`/`ctxChain` conclusion
    shape) — the set-valued twin of `TailTo_implChain`. -/
theorem TailToS_implChain (S : Formula → Prop) : ∀ (gs : List Formula) (tgt : Formula),
    TailToS S (implChain gs tgt) ↔ (TailToS S tgt ∧ ∀ g ∈ gs, ¬ TailToS S g) := by
  intro gs
  induction gs with
  | nil => intro tgt; simp [implChain]
  | cons g gs ih =>
      intro tgt
      show TailToS S (.impl g (implChain gs tgt)) ↔ _
      rw [TailToS_impl, ih]
      simp only [List.forall_mem_cons]
      tauto

/-- A search telescope is a mixed telescope (all-`searchL` layers). -/
theorem searchPlug_eq_ctxPlug : ∀ (L : List (Nat × Formula × Prog)) (p : Prog),
    searchPlug L p = ctxPlug (L.map fun t => .searchL t.1 t.2.1 t.2.2) p := by
  intro L
  induction L with
  | nil => intro p; rfl
  | cons hd tl ih =>
      intro p
      obtain ⟨g, ψ, e⟩ := hd
      simp only [searchPlug, List.map, ctxPlug, ih]

/-- A constant is never a (differently-actioned) mixed-telescope plug. -/
theorem const_ne_ctxPlug {c c' : Action} (hne : c ≠ c') :
    ∀ (L : List CtxLayer), Prog.const c ≠ ctxPlug L (.const c') := by
  intro L
  cases L with
  | nil => simp only [ctxPlug]; exact fun h => hne (by injection h)
  | cons hd tl =>
      cases hd with
      | searchL g ψ e => simp [ctxPlug]
      | iteL z aT other => simp [ctxPlug]

/-- `TailTo` through a folded guard chain (the `searchChain` conclusion shape). -/
theorem TailTo_implChain (T : Formula) : ∀ (gs : List Formula) (tgt : Formula),
    TailTo T (implChain gs tgt) ↔ (TailTo T tgt ∧ ∀ g ∈ gs, ¬ TailTo T g) := by
  intro gs
  induction gs with
  | nil => intro tgt; simp [implChain]
  | cons g gs ih =>
      intro tgt
      show TailTo T (.impl g (implChain gs tgt)) ↔ _
      rw [TailTo_impl, ih]
      simp only [List.forall_mem_cons]
      tauto

/-- The SIX player shapes whose plays the source-transparency bridge rules can conclude
    (`searchBranch`, `simStep`, `botSimStep`, `botSearchStep`, `iteBranchSearch_t`,
    `searchThenSearch_t` — one disjunct each, in that order). A player of any OTHER shape has no
    source-transparency route to its play atoms (`tail_plays_readable`).

    **Pf-only note (Phase 2)**: the sixth disjunct (the STACKED search — PrudentBot's canonical
    shape) is NEW here. It was always a readable shape, but `searchThenSearch_t` lived on the
    `Prop`-valued `Provable`, so the old `Type`-valued `Derivation` census structurally could not
    see it: each `Provable` census had to kill that rule in its own `cases` arm instead. With one
    proof system there is one census, and the shape must be listed. Every `not_readable_*` below
    refutes it the same way it refutes the others — by syntactic distinctness. -/
def ReadableMe (me : Prog) : Prop :=
  (∃ k ψ a b, me = .search k ψ (.const a) (.const b)) ∨
  (∃ p q, me = .sim p q) ∨
  (∃ p q, me = .bot (.sim p q)) ∨
  (∃ k ψ a b, me = .bot (.search k ψ (.const a) (.const b))) ∨
  (∃ z a' k ψ c0 c1 q,
    me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q) ∨
  (∃ k₁ ψ₁ k₂ ψ₂ c0 c1 q,
    me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)

/-- **The census of `S`**: if a `Pf`'s conclusion has a guarded plays-atom spine tail, the
    player is bridge-readable. One induction (`Pf.induct`), over the WHOLE proof system.

    **Guarded-invariant note (2026-07-28)**: the tail hypothesis is `TailTo`, not a bare
    `rightTail` equation — the logical-core arms now `by_cases` on the antecedent and use
    BOTH premise IHs, which is exactly the shape that stays closed under the premise-free
    Family-B implication leaves. -/
theorem tail_plays_readable
    (hatom : ∀ {k : Nat} {φ : Formula}, AtomProvable k φ →
      ∀ {me oppo : Prog} {a : Action}, TailTo (.plays me oppo a) φ → ReadableMe me) :
    ∀ {k : Nat} {φ : Formula}, Pf k φ →
      ∀ {me oppo : Prog} {a : Action},
        TailTo (.plays me oppo a) φ →
        ReadableMe me ∨ (∃ hd L a', me = searchPlug (hd :: L) (.const a')) ∨
          (∃ (hd : CtxLayer) (L : List CtxLayer) (a' : Action),
            me = ctxPlug (hd :: L) (.const a')) := by
  intro k φ d
  induction d using Pf.induct with
  | atom k' φ' h => exact fun {me oppo a} ht => Or.inl (hatom h ht)
  -- the logical core: `by_cases` on the antecedent — both IHs in play
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 ih2 =>
      intro me oppo a h
      by_cases hφ : TailTo (.plays me oppo a) φ'
      · exact ih2 hφ
      · exact ih1 ⟨h, hφ⟩
  | implTrans k' φ' ψ χ a b h1 h2 hle ih1 ih2 =>
      intro me oppo a' h
      obtain ⟨hχ, hφn⟩ := h
      by_cases hψ : TailTo (.plays me oppo a') ψ
      · exact ih1 ⟨hψ, hφn⟩
      · exact ih2 ⟨hχ, hψ⟩
  | weakenImpl k' φ' ψ m hψ hle ih =>
      intro me oppo a h
      obtain ⟨hψt, -⟩ := h
      exact ih hψt
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 ih2 =>
      intro me oppo a h
      obtain ⟨hχ, hφn⟩ := h
      by_cases hψ : TailTo (.plays me oppo a) ψ
      · exact ih2 ⟨hψ, hφn⟩
      · exact ih1 ⟨⟨hχ, hψ⟩, hφn⟩
  | diagF pm fb g K tgt hgate hle ih =>
      intro me oppo a h
      obtain ⟨⟨htgt, -⟩, -⟩ := h
      exact ih ⟨htgt, by simp⟩
  -- the premise-free Family-B implication leaves: the Guarded invariant self-annihilates
  | implRefl k' φ' hle =>
      intro me oppo a h
      obtain ⟨h1, h2⟩ := h
      exact absurd h1 h2
  | implK k' φ' ψ hle =>
      intro me oppo a h
      obtain ⟨⟨h1, -⟩, h2⟩ := h
      exact absurd h1 h2
  | implS k' φ' ψ χ hle =>
      intro me oppo a h
      obtain ⟨⟨⟨hχ, hnφ⟩, hnφψ⟩, hnA⟩ := h
      exact absurd ⟨⟨hχ, fun hψ => hnφψ ⟨hψ, hnφ⟩⟩, hnφ⟩ hnA
  -- contrapose's spine tail is a `.neg` — no plays-atom census matches it
  | contrapose k' φ' ψ m h hle ih =>
      intro me oppo a hT
      simp at hT
  -- negElim never fires: its premises are contradictory by soundness
  | negElim k' φ' ψ m₁ m₂ h1 h2 hle ih1 ih2 =>
      intro me oppo a hT
      exact absurd (Pf_sound _ _ h2) (Pf_sound _ _ h1)
  -- each bridge rule's tail names its own (readable) `me`
  | searchBranch k' g ψ a b me' oppo' hme hle =>
      intro me oppo a' h
      obtain ⟨h1, -⟩ := h
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl (Or.inl ⟨g, ψ, _, _, hme⟩)
  | simStep k' me' p q oppo' a hme hle =>
      intro me oppo a' h
      obtain ⟨h1, -⟩ := h
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl (Or.inr (Or.inl ⟨p, q, hme⟩))
  | botSimStep k' me' p q oppo' a hme hle =>
      intro me oppo a' h
      obtain ⟨h1, -⟩ := h
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨p, q, hme⟩)))
  | botSearchStep k' g ψ a b me' oppo' hme hle =>
      intro me oppo a' h
      obtain ⟨h1, -⟩ := h
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨g, ψ, _, _, hme⟩))))
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me' oppo' hme hle =>
      intro me oppo a'' h
      obtain ⟨⟨h1, -⟩, -⟩ := h
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨z, a', g, ψ, c0, c1, q, hme⟩)))))
  | searchThenSearch_t k' k₁ k₂ m ψ₁ ψ₂ c0 c1 q me' oppo' hme hprud hmk hle _ih =>
      -- the STACKED-search player (PrudentBot's shape) — the sixth readable disjunct
      intro me oppo a h
      obtain ⟨h1, -⟩ := h
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k₁, ψ₁, k₂, ψ₂, c0, c1, q, hme⟩)))))
  | searchChain k' g₁ ψ₁ e₁ L a me' opponent' hme hle =>
      -- the telescope player is a (nonempty) search plug
      intro me oppo a' h
      obtain ⟨h1, -⟩ := h
      rw [TailTo_implChain] at h1
      obtain ⟨h1, -⟩ := h1
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inr (Or.inl ⟨(g₁, ψ₁, e₁), L, _, hme⟩)
  | ctxChain k' hd L a me' opponent' hme hle =>
      -- the mixed-telescope player is a (nonempty) context plug
      intro me oppo a' h
      have h' : TailTo (.plays me oppo a')
          (implChain (ctxGuards me' opponent' (hd :: L)) (.plays me' opponent' a)) := h
      rw [TailTo_implChain] at h'
      obtain ⟨h1, -⟩ := h'
      simp only [TailTo_plays, Formula.plays.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact Or.inr (Or.inr ⟨hd, L, _, hme⟩)
  -- non-plays tails (`.eq`, `.neg`, `.box`, `.diag`): the hypothesis is absurd
  | eqRefl k' p hle => intro me oppo a h; simp at h
  | eqNeg k' p q hne hle => intro me oppo a h; simp at h
  | atomNeg k' p q b aN m hcert hne hle => intro me oppo a h; simp at h
  | atomBoxImpl k' kBox p q a hcert hle => intro me oppo a' h; simp at h
  | boxIntro kIn K φ' hprem hle _ih => intro me oppo a h; simp at h
  | axK a b c m K φ' α hprem hgate hle _ih => intro me oppo a' h; simp at h
  | box4 a b K φ' hgate hsz => intro me oppo a' h; simp at h
  | diagB pm fb g K tgt hgate hle _ih => intro me oppo a h; simp at h
  | axKf a b c K φ' α hgate hsz => intro me oppo a' h; simp at h
  | boxMono a b K φ' hab hsz => intro me oppo a' h; simp at h

/-- The probe-first simulator shape is never bridge-readable, provided its then-branch
    is not a const-branched `.search` (true of every zoo simulator: the branch is a
    `.const` or a nested `.ite`). `iteBranchSearch_t` — the only `.ite` bridge — needs
    a `.search` then-branch. -/
theorem not_readable_probeFirst (z p q : Prog) (aT : Action)
    (hshape : ∀ k' ψ c0 c1, p ≠ .search k' ψ (.const c0) (.const c1)) :
    ¬ ReadableMe (.ite (.sim .opp (.bot z)) aT p q) := by
  rintro (⟨k', ψ, a, b, h⟩ | ⟨p', r, h⟩ | ⟨p', r, h⟩ | ⟨k', ψ, a, b, h⟩ |
          ⟨w, a', k', ψ, c0, c1, r, h⟩ | ⟨k₁, ψ₁, k₂, ψ₂, c0, c1, r, h⟩)
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp only [Prog.ite.injEq] at h
    exact hshape _ _ _ _ h.2.2.1
  · -- the stacked-search shape is a `.search`, never an `.ite`
    simp at h

set_option maxHeartbeats 1000000 in
/-- **THE SET-VALUED FLOOR KERNEL** (the ite frontier, 2026-07-28): no proof of ≤ k
    characters concludes any formula in the `TailToS S` class, for a forbidden set `S`
    of plays-atoms with
    * `hatom` — no member has a certificate at any budget ≤ k;
    * ACTION-refined kills, one per source-transparency rule, each stated on the
      S-member the rule would conclude (`hsb`/`hsim`/`hbotsim`/`hbotsearch`/`hsts`/
      `hplug`/`hctx`) — action refinement is what lets searcher-players carry
      forbidden ELSE-plays while their readable THEN-plays stay untouched;
    * `hibs` — S-closure through the fused ite rule: if its conclusion tail is
      forbidden, its probe is too (vacuous by shape in every zoo instance);
    * `hctx` — THE ite-frontier discipline: any mixed-telescope decomposition of a
      forbidden player must expose a forbidden guard (its probe), which the class then
      excludes via `¬TailToS` on antecedents.

    Strong induction on the budget: the logical-core regress descends because
    transcript cumulativity makes every premise budget strictly smaller; the
    `by_cases`-on-antecedent arms are the Guarded-invariant pattern (file header). -/
theorem no_provable_tailToS_floor (k : Nat) (S : Formula → Prop)
    (hplays : ∀ φ, S φ → ∃ p q c, φ = Formula.plays p q c)
    (hatom : ∀ K, K ≤ k → ∀ φ, S φ → ¬ AtomProvable K φ)
    (hsb : ∀ me oppo c, S (.plays me oppo c) →
      ∀ g ψ b, me ≠ .search g ψ (.const c) (.const b))
    (hsim : ∀ me oppo c, S (.plays me oppo c) → ∀ p q, me ≠ .sim p q)
    (hbotsim : ∀ me oppo c, S (.plays me oppo c) → ∀ p q, me ≠ .bot (.sim p q))
    (hbotsearch : ∀ me oppo c, S (.plays me oppo c) →
      ∀ g ψ b, me ≠ .bot (.search g ψ (.const c) (.const b)))
    (hibs : ∀ z a' g ψ c0 c1 q oppo,
      S (.plays (.ite (.sim .opp (.bot z)) a'
        (.search g ψ (.const c0) (.const c1)) q) oppo c0) →
      S (.plays oppo (.bot z) a'))
    (hsts : ∀ me oppo c, S (.plays me oppo c) →
      ∀ k₁ ψ₁ k₂ ψ₂ c1 q, me ≠ .search k₁ ψ₁ (.search k₂ ψ₂ (.const c) (.const c1)) q)
    (hplug : ∀ me oppo c, S (.plays me oppo c) →
      ∀ (L : List (Nat × Formula × Prog)), me ≠ searchPlug L (.const c))
    (hctx : ∀ me oppo c, S (.plays me oppo c) →
      ∀ (hd : CtxLayer) (L : List CtxLayer), me = ctxPlug (hd :: L) (.const c) →
      ∃ g ∈ ctxGuards me oppo (hd :: L), S g) :
    ∀ K φ, Pf K φ → K ≤ k → TailToS S φ → False := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro φ hp hK htail
    cases hp with
    -- the five simple bridge rules: each names its own `me`, killed action-refined
    | searchBranch gg psi aa bb me oppo hme hsz =>
        obtain ⟨h1, -⟩ := htail
        exact hsb me oppo aa h1 gg psi bb hme
    | simStep me pp qq oppo aa hme hsz =>
        obtain ⟨h1, -⟩ := htail
        exact hsim me oppo aa h1 pp qq hme
    | botSimStep me pp qq oppo aa hme hsz =>
        obtain ⟨h1, -⟩ := htail
        exact hbotsim me oppo aa h1 pp qq hme
    | botSearchStep gg psi aa bb me oppo hme hsz =>
        obtain ⟨h1, -⟩ := htail
        exact hbotsearch me oppo aa h1 gg psi bb hme
    | iteBranchSearch_t gg zz aa' cc0 cc1 psi qq me oppo hme hsz =>
        -- the probe joins `S` via `hibs`, contradicting the class's `¬TailToS` probe slot
        obtain ⟨⟨h1, -⟩, hprobe⟩ := htail
        exact hprobe (hibs zz aa' gg psi cc0 cc1 qq oppo (hme ▸ h1))
    -- the stacked-search bridge: the action-refined kill
    | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q' me oppo hme hpre hm hsz =>
        obtain ⟨h1, -⟩ := htail
        exact hsts me oppo c0 h1 _ _ _ _ _ _ hme
    -- the depth-general search telescope: killed by the plug disequality
    | searchChain g₁ ψ₁ e₁ L a me oppo hme hsz =>
        obtain ⟨h1, -⟩ := htail
        rw [TailToS_implChain] at h1
        obtain ⟨h1, -⟩ := h1
        exact hplug me oppo a h1 ((g₁, ψ₁, e₁) :: L) hme
    -- THE MIXED TELESCOPE: the decomposition's forbidden probe is one of the chain's
    -- own antecedents, which the class forbids
    | ctxChain hd L a me oppo hme hsz =>
        have htail' : TailToS S
            (implChain (ctxGuards me oppo (hd :: L)) (.plays me oppo a)) := htail
        rw [TailToS_implChain] at htail'
        obtain ⟨h1, hall⟩ := htail'
        obtain ⟨gG, hgmem, hgS⟩ := hctx me oppo a h1 hd L hme
        refine hall gG hgmem ?_
        obtain ⟨p', q', c', rfl⟩ := hplays gG hgS
        exact hgS
    -- the atom entry: killed by the supplied certificate-impossibility
    | atom h =>
        cases h with
        | mk hpp hn =>
          exact hatom K hK _ htail (.mk hpp hn)
    -- the logical-core regress: strictly smaller premise budgets, Guarded `by_cases`
    | weakenImpl φ' ψ m hψ hsz =>
        obtain ⟨hψt, -⟩ := htail
        simp only [Formula.size] at hsz
        exact ih m (by omega) ψ hψ (by omega) hψt
    | implTrans φ' ψ χ a b h1 h2 hsz =>
        obtain ⟨hχ, hφn⟩ := htail
        simp only [Formula.size] at hsz
        by_cases hψt : TailToS S ψ
        · exact ih a (by omega) _ h1 (by omega) ⟨hψt, hφn⟩
        · exact ih b (by omega) _ h2 (by omega) ⟨hχ, hψt⟩
    | mp m₁ m₂ φ' α h1 h2 hsz =>
        have hα := Formula.size_pos φ
        by_cases hφt : TailToS S φ'
        · exact ih m₂ (by omega) _ h2 (by omega) hφt
        · exact ih m₁ (by omega) _ h1 (by omega) ⟨htail, hφt⟩
    | impS2 φ' ψ χ m₁ m₂ K' h1 h2 hsz =>
        obtain ⟨hχ, hφn⟩ := htail
        simp only [Formula.size] at hsz
        by_cases hψt : TailToS S ψ
        · exact ih m₂ (by omega) _ h2 (by omega) ⟨hψt, hφn⟩
        · exact ih m₁ (by omega) _ h1 (by omega) ⟨⟨hχ, hψt⟩, hφn⟩
    | diagF pm fb g' K' tgt hpre hsz =>
        obtain ⟨⟨htgt, -⟩, -⟩ := htail
        simp only [Formula.size] at hsz
        refine ih pm (by omega) _ hpre (by omega) ⟨htgt, fun hbox => ?_⟩
        obtain ⟨p', q', c', h⟩ := hplays _ hbox
        simp at h
    -- the premise-free Family-B implication leaves: the Guarded invariant self-annihilates
    | implRefl φ' hsz =>
        obtain ⟨h1, h2⟩ := htail
        exact h2 h1
    | implK φ' ψ hsz =>
        obtain ⟨⟨h1, -⟩, h2⟩ := htail
        exact h2 h1
    | implS φ' ψ χ hsz =>
        obtain ⟨⟨⟨hχ, hnφ⟩, hnφψ⟩, hnA⟩ := htail
        exact hnA ⟨⟨hχ, fun hψ => hnφψ ⟨hψ, hnφ⟩⟩, hnφ⟩
    -- contrapose's spine tail is a `.neg` ∉ S; negElim's premises are contradictory
    | contrapose φ' ψ m' h hsz =>
        obtain ⟨h1, -⟩ := htail
        obtain ⟨p', q', c', h⟩ := hplays _ h1
        simp at h
    | negElim =>
        rename_i φ' m₁ m₂ h1 h2 hsz
        exact absurd (Pf_sound _ _ h2) (Pf_sound _ _ h1)
    -- non-plays tails: killed by `hplays`
    | eqRefl pp hsz =>
        obtain ⟨p', q', c', h⟩ := hplays _ htail; simp at h
    | eqNeg pp qq hne hsz =>
        obtain ⟨p', q', c', h⟩ := hplays _ htail; simp at h
    | atomBoxImpl kBox p' q' a hcert hsz =>
        obtain ⟨h1, -⟩ := htail
        obtain ⟨p'', q'', c'', h⟩ := hplays _ h1; simp at h
    | boxIntro kIn K' φ' hpre hsz =>
        obtain ⟨p', q', c', h⟩ := hplays _ htail; simp at h
    | axK a b c m K' φ' α hpre hab hsz =>
        obtain ⟨h1, -⟩ := htail
        obtain ⟨p', q', c', h⟩ := hplays _ h1; simp at h
    | box4 a b K' φ' h1 h2 =>
        obtain ⟨hb1, -⟩ := htail
        obtain ⟨p', q', c', h⟩ := hplays _ hb1; simp at h
    | diagB pm fb g' K' tgt hpre hsz =>
        obtain ⟨h1, -⟩ := htail
        obtain ⟨p', q', c', h⟩ := hplays _ h1; simp at h
    | axKf a b c K' φ' α h1 h2 =>
        obtain ⟨⟨hb1, -⟩, -⟩ := htail
        obtain ⟨p', q', c', h⟩ := hplays _ hb1; simp at h
    | boxMono a b K' φ' hab hsz =>
        obtain ⟨h1, -⟩ := htail
        obtain ⟨p', q', c', h⟩ := hplays _ h1; simp at h
    | atomNeg p' q' b aN m hcert hne hsz =>
        obtain ⟨p'', q'', c'', h⟩ := hplays _ htail; simp at h

/-- **The singleton floor census** (compatibility wrapper over the set kernel): the
    pre-frontier statement, now requiring the ONE extra `hctx` disequality — the
    target player must not be a mixed-telescope plug of its target action. Targets
    that ARE such plugs (probe-first `.ite` simulators) must use the set kernel with
    their probe atoms priced into `S` (see `no_provable_probeFirst_tail`). -/
theorem no_provable_tailTo_floor (k : Nat) (P O : Prog) (aTgt : Action)
    (hatom : ∀ K, K ≤ k → ¬ AtomProvable K (.plays P O aTgt))
    (hread5 : ¬ ((∃ k' ψ a b, P = .search k' ψ (.const a) (.const b)) ∨
       (∃ p q, P = .sim p q) ∨
       (∃ p q, P = .bot (.sim p q)) ∨
       (∃ k' ψ a b, P = .bot (.search k' ψ (.const a) (.const b))) ∨
       (∃ z a' k' ψ c0 c1 q,
         P = .ite (.sim .opp (.bot z)) a' (.search k' ψ (.const c0) (.const c1)) q)))
    (hsts : ∀ k₁ ψ₁ k₂ ψ₂ c1 q,
      P ≠ .search k₁ ψ₁ (.search k₂ ψ₂ (.const aTgt) (.const c1)) q)
    (hplug : ∀ (L : List (Nat × Formula × Prog)), P ≠ searchPlug L (.const aTgt))
    (hctx : ∀ (hd : CtxLayer) (L : List CtxLayer), P ≠ ctxPlug (hd :: L) (.const aTgt)) :
    ∀ K φ, Pf K φ → K ≤ k → TailTo (.plays P O aTgt) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays P O aTgt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' hφ'
    cases hφ'
    exact hatom K' hK'
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    exact hread5 (Or.inl ⟨g, ψ, _, _, hme⟩)
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    exact hread5 (Or.inr (Or.inl ⟨p, q, hme⟩))
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    exact hread5 (Or.inr (Or.inr (Or.inl ⟨p, q, hme⟩)))
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    exact hread5 (Or.inr (Or.inr (Or.inr (Or.inl ⟨g, ψ, _, _, hme⟩))))
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    exact absurd h1.symm
      (fun h => hread5 (Or.inr (Or.inr (Or.inr (Or.inr ⟨z, a', g, ψ, c0, c1, q, h⟩)))))
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exact hsts _ _ _ _ _ _ hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exact hplug L hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exact absurd hme (hctx hd L)

/-- **The `search_f` floor as a cost lower bound** (probe-first instance): no proof of
    ≤ k characters concludes any formula whose guarded spine tail is "the probe-first
    simulator plays `aTgt` against the budget-`k` searcher" — in particular (spine of
    length zero) the searcher's own guard instance is unprovable at its own budget.

    FULLY GENERAL in the simulator's `.ite` (test action, both branches): the kill
    happens at the GUARD certificate, which both `ite` polarities must carry — the
    searcher's probe play, where `search_t` is refuted by `hfalse` + soundness and
    `search_f` charges the literal floor summand `k`. -/
theorem no_provable_probeFirst_tail (k : Nat) (z p q : Prog) (aT aTgt : Action)
    (g : Formula) (pT pE : Prog)
    (hfalse : ¬ (g.subst (.search k g pT pE) (.bot z)).interp)
    (hshape : ∀ k' ψ c0 c1, p ≠ .search k' ψ (.const c0) (.const c1))
    (hpthen : ∀ (L : List CtxLayer), p ≠ ctxPlug L (.const aTgt)) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.ite (.sim .opp (.bot z)) aT p q) (.search k g pT pE) aTgt) φ →
      False := by
  refine no_provable_tailTo_floor k _ _ _ ?_ ?_ ?_ ?_ ?_
  · -- atom killer: the probe replay — `search_t` by soundness, `search_f` by the floor
    intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | ite_t hg hr hbr =>
          cases hg with
          | sim hin =>
            simp only [Prog.subst] at hin
            cases hin with
            | search_t hProv hbr2 => exact hfalse (Pf_sound _ _ hProv)
            | search_f hneg hbr2 => simp only [c_node] at hn; omega
      | ite_f hg hr hbr =>
          cases hg with
          | sim hin =>
            simp only [Prog.subst] at hin
            cases hin with
            | search_t hProv hbr2 => exact hfalse (Pf_sound _ _ hProv)
            | search_f hneg hbr2 => simp only [c_node] at hn; omega
  · -- the five simple bridge shapes
    rintro (⟨k', ψ, a, b, h⟩ | ⟨p', r, h⟩ | ⟨p', r, h⟩ | ⟨k', ψ, a, b, h⟩ |
            ⟨w, a', k', ψ, c0, c1, r, h⟩)
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp only [Prog.ite.injEq] at h
      exact hshape _ _ _ _ h.2.2.1
  · -- an `.ite` is never a stacked `.search`
    intro k₁ ψ₁ k₂ ψ₂ c1 q' h
    simp at h
  · -- an `.ite` is never a search plug
    intro L h
    cases L with
    | nil => simp [searchPlug] at h
    | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug] at h
  · -- a mixed-telescope decomposition would go through the then-branch: `hpthen`
    intro hd L h
    cases hd with
    | searchL g' ψ' e' => simp [ctxPlug] at h
    | iteL z' aT' other' =>
        simp only [ctxPlug, Prog.ite.injEq] at h
        exact hpthen L h.2.2.1

/-- `no_provable_probeFirst_tail` for a `.bot`-WRAPPED searcher opponent (JustBot's
    frozen `.bot (DupocBot k)` guard target): identical cascade with one extra `.bot`
    unwrap inside the probe replay. -/
theorem no_provable_probeFirst_tail_botOpp (k : Nat) (z p q : Prog) (aT aTgt : Action)
    (g : Formula) (pT pE : Prog)
    (hfalse : ¬ (g.subst (.bot (.search k g pT pE)) (.bot z)).interp)
    (hshape : ∀ k' ψ c0 c1, p ≠ .search k' ψ (.const c0) (.const c1))
    (hpthen : ∀ (L : List CtxLayer), p ≠ ctxPlug L (.const aTgt)) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.ite (.sim .opp (.bot z)) aT p q) (.bot (.search k g pT pE)) aTgt) φ →
      False := by
  refine no_provable_tailTo_floor k _ _ _ ?_ ?_ ?_ ?_ ?_
  · intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | ite_t hg hr hbr =>
          cases hg with
          | sim hin =>
            simp only [Prog.subst] at hin
            cases hin with
            | bot hin2 =>
              cases hin2 with
              | search_t hProv hbr2 => exact hfalse (Pf_sound _ _ hProv)
              | search_f hneg hbr2 => simp only [c_node] at hn; omega
      | ite_f hg hr hbr =>
          cases hg with
          | sim hin =>
            simp only [Prog.subst] at hin
            cases hin with
            | bot hin2 =>
              cases hin2 with
              | search_t hProv hbr2 => exact hfalse (Pf_sound _ _ hProv)
              | search_f hneg hbr2 => simp only [c_node] at hn; omega
  · rintro (⟨k', ψ, a, b, h⟩ | ⟨p', r, h⟩ | ⟨p', r, h⟩ | ⟨k', ψ, a, b, h⟩ |
            ⟨w, a', k', ψ, c0, c1, r, h⟩)
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp only [Prog.ite.injEq] at h
      exact hshape _ _ _ _ h.2.2.1
  · intro k₁ ψ₁ k₂ ψ₂ c1 q' h
    simp at h
  · intro L h
    cases L with
    | nil => simp [searchPlug] at h
    | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug] at h
  · intro hd L h
    cases hd with
    | searchL g' ψ' e' => simp [ctxPlug] at h
    | iteL z' aT' other' =>
        simp only [ctxPlug, Prog.ite.injEq] at h
        exact hpthen L h.2.2.1

/-! ## The floor at the searcher's own doorstep

The probe-first lemmas price a SIMULATOR's play against a searcher. A third shape
remains: the searcher's OWN play as the target atom — e.g. PrudentBot's self-prudence
"I defect vs `.bot DefectBot`", which is the else-play of its own budget-`k` search.
Here the target atom reaches the floor DIRECTLY (no simulator detour): `search_t` dies
by soundness of the false guard instance, `search_f` IS the floor. Two extra shape
hypotheses close the census (`hshape`: the searcher's branches are not both `.const`,
else `searchBranch` could read it) and the stacked-search bridge (`hinner`: the
then-branch is not an inner search whose then-action is the target — else
`searchThenSearch_t` could conclude the target-tailed implication). -/

/-- A search bot whose branches are not both `.const` matches none of the FIVE
    source-transparency bridge shapes.

    **Pf-only note**: deliberately NOT stated as `¬ ReadableMe` — `ReadableMe`'s sixth disjunct
    (the STACKED search) is genuinely SATISFIED by e.g. `PrudentBot k`, whose then-branch is a
    const-branched `.search`. That disjunct belongs to `searchThenSearch_t`, which the floor
    kernel discharges in its OWN arm (via the action-specific `hinner`: the stacked rule
    concludes a play of the INNER THEN-action, never the else-action the floor is about). The
    five bridge arms can only ever produce the first five disjuncts, so this is exactly the
    strength they need. -/
theorem not_readable_searchNonConst (k : Nat) (g : Formula) (pT pE : Prog)
    (hshape : ∀ c0 c1, ¬ (pT = .const c0 ∧ pE = .const c1)) :
    ¬ ((∃ k' ψ a b, (Prog.search k g pT pE) = .search k' ψ (.const a) (.const b)) ∨
       (∃ p q, (Prog.search k g pT pE) = .sim p q) ∨
       (∃ p q, (Prog.search k g pT pE) = .bot (.sim p q)) ∨
       (∃ k' ψ a b, (Prog.search k g pT pE) = .bot (.search k' ψ (.const a) (.const b))) ∨
       (∃ z a' k' ψ c0 c1 q,
         (Prog.search k g pT pE) = .ite (.sim .opp (.bot z)) a'
           (.search k' ψ (.const c0) (.const c1)) q)) := by
  rintro (⟨k', ψ, a, b, h⟩ | ⟨p', r, h⟩ | ⟨p', r, h⟩ | ⟨k', ψ, a, b, h⟩ |
          ⟨w, a', k', ψ, c0, c1, r, h⟩)
  · simp only [Prog.search.injEq] at h
    exact hshape a b ⟨h.2.2.1, h.2.2.2⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h

/-- **The floor at the searcher's own play**: no proof of ≤ k characters concludes any
    formula whose guarded spine tail is "the budget-`k` searcher plays `aTgt` against
    `O`", when the searcher's guard instance vs `O` is false. The self-referential
    shape: PrudentBot's same-`k` self-prudence is the canonical instance. -/
theorem no_provable_searcherPlay_tail (k : Nat) (g : Formula) (pT pE O : Prog)
    (aTgt : Action)
    (hfalse : ¬ (g.subst (.search k g pT pE) O).interp)
    (hshape : ∀ c0 c1, ¬ (pT = .const c0 ∧ pE = .const c1))
    (hinner : ∀ k₂ ψ₂ c1, pT ≠ .search k₂ ψ₂ (.const aTgt) (.const c1))
    (hplug : ∀ (L : List (Nat × Formula × Prog)),
      Prog.search k g pT pE ≠ searchPlug L (.const aTgt))
    (hctxT : ∀ (L : List CtxLayer), pT ≠ ctxPlug L (.const aTgt)) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.search k g pT pE) O aTgt) φ → False := by
  refine no_provable_tailTo_floor k _ _ _ ?_ ?_ ?_ hplug ?_
  · -- atom killer: `search_t` by soundness of the false guard, `search_f` IS the floor
    intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | search_t hProv hbr => exact hfalse (Pf_sound _ _ hProv)
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · exact not_readable_searchNonConst k g pT pE hshape
  · intro k₁ ψ₁ k₂ ψ₂ c1 q' h
    simp only [Prog.search.injEq] at h
    exact hinner _ _ _ h.2.2.1
  · -- a mixed-telescope decomposition would go through the then-branch: `hctxT`
    intro hd L h
    cases hd with
    | searchL g' ψ' e' =>
        simp only [ctxPlug, Prog.search.injEq] at h
        exact hctxT L h.2.2.1
    | iteL z' aT' other' => simp [ctxPlug] at h

/-! ## The budget-free census for unreadable players

The floor lemmas above price certificates OUT of a bounded budget. The CIMCIC/DIMCID
pattern is stronger: the target atom has NO certificate at ANY budget (a Gödelian
fall-through or a semantically false consequent), and the player is fully
bridge-unreadable — so nothing `TailTo`-tailed at it is provable at any budget. -/

theorem no_provable_tailTo_unreadable (P O : Prog) (A : Action)
    (hcert : ∀ n, ¬ AtomProvable n (.plays P O A))
    (hread : ¬ ReadableMe P)
    (hplug : ∀ (L : List (Nat × Formula × Prog)), P ≠ searchPlug L (.const A))
    (hctx : ∀ (hd : CtxLayer) (L : List CtxLayer), P ≠ ctxPlug (hd :: L) (.const A)) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ TailTo (.plays P O A) φ := by
  intro m φ h hT
  refine no_provable_tailTo_floor m P O A ?_ ?_ ?_ hplug hctx m φ h le_rfl hT
  · exact fun K _ => hcert K
  · exact fun h5 => hread (h5.imp id (Or.imp id (Or.imp id (Or.imp id Or.inl))))
  · intro k₁ ψ₁ k₂ ψ₂ c1 q hst
    exact hread (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k₁, ψ₁, k₂, ψ₂, A, c1, q, hst⟩)))))

end PD.BaseTheorems
