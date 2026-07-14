import PrisonersDilemma.Base.Soundness

/-!
# Base/Exclusion — structural exclusion: what `S` can NOT conclude

The positive layers certify plays; this file starts the NEGATIVE direction, needed by
the honest outcome theorems for the floor-killed pairs (the tombstones in
`Theorems/DupocBot.lean` / `Theorems/LlmGenerations/PrudentBot.lean`): `¬Pf k φ`
facts for TRUE formulas, where soundness gives nothing and only cost accounting can
close the guard.

Contents:
* `Formula.size_pos` — every formula costs at least one character.
* `rightTail` — the final consequent of a right-nested implication chain (the spine
  tail; `modusPonens`/`app` peel it, `hypSyll`/`implTrans`/`impS2` preserve it).
* `ReadableMe` — the five player shapes whose plays the `Derivation` source-transparency
  bridge can conclude.
* `Derivation.tail_plays_readable` — THE CENSUS: if a `Derivation`'s conclusion has a
  plays-atom spine tail, the player is one of the readable shapes. Contrapositive: a
  bot whose source is not bridge-readable (e.g. DBot — an `.ite` with a `.const`
  then-branch) has NO `Derivation` route to any formula ending in its play atoms,
  which closes the `struct` entry point of `Pf` in one stroke.

Consumers combine the census with a budget strong-induction over `Pf` (the
`app`/`weakenImpl`/`implTrans`/`diagF`/`impS2` regress descends because transcript
cumulativity makes every premise budget strictly smaller) and kill the `atom` entry by
the `search_f` floor arithmetic — blueprint: `no_provable_DBot_C_tail` in
`Theorems/DupocBot.lean`.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-- Every formula costs at least one character. -/
theorem _root_.PD.Formula.size_pos : ∀ φ : Formula, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp only [Formula.size] <;> omega

/-- The final consequent of a right-nested implication chain — the "spine tail".
    `rightTail (φ₁ → (φ₂ → … → ψ))` is `ψ` for non-`.impl` `ψ`. -/
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

/-- **The census of `S`**: if a `Pf`'s conclusion has a plays-atom spine tail, the player is
    bridge-readable. One induction (`Pf.induct`), over the WHOLE proof system.

    **Pf-only note (Phase 2)**: this used to be TWO theorems — a `Derivation` census
    (`tail_plays_readable`, over the structural half) plus a `struct` arm in each `Provable`
    census that reached through the glue into it. The merge collapses them: the bridge rules are
    now `Pf` constructors, so their arms sit beside `mp`/`implTrans` in a single induction. The
    modal/box rules and `atom`/`atomNeg` have non-plays tails (`.box`/`.neg`/`.diag`), so they
    close by `simp` — EXCEPT `atom` itself, whose tail IS a plays-atom: it is handled by the
    CALLERS (they inspect the certificate; a certificate is not a source-transparency route), so
    the census takes it as a hypothesis `hatom` on the atom arm. -/
theorem tail_plays_readable
    (hatom : ∀ {k : Nat} {φ : Formula}, AtomProvable k φ →
      ∀ {me oppo : Prog} {a : Action}, rightTail φ = .plays me oppo a → ReadableMe me) :
    ∀ {k : Nat} {φ : Formula}, Pf k φ →
      ∀ {me oppo : Prog} {a : Action},
        rightTail φ = .plays me oppo a → ReadableMe me := by
  intro k φ d
  induction d using Pf.induct with
  | atom k' φ' h => exact fun {me oppo a} ht => hatom h ht
  -- the logical core preserves the spine tail
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 =>
      intro me oppo a h
      exact ih1 (by simpa using h)
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 =>
      intro me oppo a' h
      exact ih2 (by simpa using h)
  | weakenImpl k' φ' ψ m hψ hle ih =>
      intro me oppo a h
      exact ih (by simpa using h)
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 =>
      intro me oppo a h
      exact ih1 (by simpa using h)
  | diagF pm fb g K tgt hgate hle ih =>
      intro me oppo a h
      exact ih (by simpa using h)
  -- each bridge rule's tail names its own (readable) `me`
  | searchBranch k' g ψ a b me' oppo' hme hle =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨g, ψ, _, _, hme⟩
  | simStep k' me' p q oppo' a hme hle =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨p, q, hme⟩)
  | botSimStep k' me' p q oppo' a hme hle =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨p, q, hme⟩))
  | botSearchStep k' g ψ a b me' oppo' hme hle =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g, ψ, _, _, hme⟩)))
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me' oppo' hme hle =>
      intro me oppo a'' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨z, a', g, ψ, c0, c1, q, hme⟩))))
  | searchThenSearch_t k' k₁ k₂ m ψ₁ ψ₂ c0 c1 q me' oppo' hme hprud hmk hle _ih =>
      -- the STACKED-search player (PrudentBot's shape) — the sixth readable disjunct
      intro me oppo a h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k₁, ψ₁, k₂, ψ₂, c0, c1, q, hme⟩))))
  -- non-plays tails (`.eq`, `.neg`, `.box`, `.diag`): the hypothesis is absurd
  | eqRefl k' p hle => intro me oppo a h; simp [rightTail] at h
  | eqNeg k' p q hne hle => intro me oppo a h; simp [rightTail] at h
  | atomNeg k' p q b aN m hcert hne hle => intro me oppo a h; simp [rightTail] at h
  | atomBoxImpl k' kBox p q a hcert hle => intro me oppo a' h; simp [rightTail] at h
  | boxIntro kIn K φ' hprem hle _ih => intro me oppo a h; simp [rightTail] at h
  | axK a b c m K φ' α hprem hgate hle _ih => intro me oppo a' h; simp [rightTail] at h
  | box4 a b K φ' hgate hsz => intro me oppo a' h; simp [rightTail] at h
  | diagB pm fb g K tgt hgate hle _ih => intro me oppo a h; simp [rightTail] at h
  | axKf a b c K φ' α hgate hsz => intro me oppo a' h; simp [rightTail] at h
  | boxMono a b K φ' hab hsz => intro me oppo a' h; simp [rightTail] at h

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
/-- **The `search_f` floor as a cost lower bound** (generalized): no proof of ≤ k
    characters concludes any formula whose implication-spine tail is "the probe-first
    simulator plays `aTgt` against the budget-`k` searcher" — in particular (spine of
    length zero) the searcher's own guard instance is unprovable at its own budget.

    FULLY GENERAL in the simulator's `.ite` (test action, both branches): the kill
    happens at the GUARD certificate, which both `ite` polarities must carry — the
    searcher's probe play, where `search_t` is refuted by `hfalse` + soundness and
    `search_f` charges the literal floor summand `k`. Strong induction on the budget:
    `struct` dies by the census (`not_readable_probeFirst`); the
    `app`/`weakenImpl`/`implTrans`/`diagF`/`impS2` regress descends because transcript
    cumulativity makes every premise budget strictly smaller. The non-cumulative budget
    citations (`search_t`, `searchThenSearch_t`) never enter the induction — killed
    semantically / by shape — which is exactly why this pair-shaped bound is provable
    while the universal closure stays open. -/
theorem no_provable_probeFirst_tail (k : Nat) (z p q : Prog) (aT aTgt : Action)
    (g : Formula) (pT pE : Prog)
    (hfalse : ¬ (g.subst (.search k g pT pE) (.bot z)).interp)
    (hshape : ∀ k' ψ c0 c1, p ≠ .search k' ψ (.const c0) (.const c1)) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ =
        .plays (.ite (.sim .opp (.bot z)) aT p q) (.search k g pT pE) aTgt →
      False := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro φ hp hK htail
    cases hp with
    -- the SIX source-transparency bridge rules (formerly reached via `struct` + the
    -- `Derivation` census): each names its own readable `me`, which `not_readable_probeFirst z p q aT hshape` refutes.
    | searchBranch gg psi aa bb me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inl ⟨gg, psi, _, _, hme⟩)
    | simStep me pp qq oppo aa hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inl ⟨pp, qq, hme⟩))
    | botSimStep me pp qq oppo aa hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inr (Or.inl ⟨pp, qq, hme⟩)))
    | botSearchStep gg psi aa bb me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inr (Or.inr (Or.inl ⟨gg, psi, _, _, hme⟩))))
    | iteBranchSearch_t gg zz aa' cc0 cc1 psi qq me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨zz, aa', gg, psi, cc0, cc1, qq, hme⟩)))))
    | eqRefl pp hsz => simp [rightTail] at htail
    | eqNeg pp qq hne hsz => simp [rightTail] at htail
    | atom h =>
        cases h with
        | mk hpp hn =>
          simp only [rightTail_plays, Formula.plays.injEq] at htail
          obtain ⟨rfl, rfl, rfl⟩ := htail
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
    | weakenImpl φ' ψ m hψ hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih m (by omega) ψ hψ (by omega) htail
    | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q' me oppo hme hpre hm hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        simp at hme
    | implTrans φ' ψ χ a b h1 h2 hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih b (by omega) _ h2 (by omega) (by simpa using htail)
    | atomBoxImpl kBox p' q' a hcert hsz => simp at htail
    | boxIntro kIn K' φ' hpre hsz => simp at htail
    | mp m₁ m₂ φ' α h1 h2 hsz =>
        have hα := Formula.size_pos φ
        exact ih m₁ (by omega) _ h1 (by omega) (by simpa using htail)
    | axK a b c m K' φ' α hpre hab hsz => simp at htail
    | box4 a b K' φ' h1 h2 => simp at htail
    | diagF pm fb g' K' tgt hpre hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih pm (by omega) _ hpre (by omega) (by simpa using htail)
    | diagB pm fb g' K' tgt hpre hsz => simp at htail
    | axKf a b c K' φ' α h1 h2 => simp at htail
    | impS2 φ' ψ χ m₁ m₂ K' h1 h2 hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih m₁ (by omega) _ h1 (by omega) (by simpa using htail)
    | boxMono a b K' φ' hab hsz => simp at htail
    | atomNeg p' q' b aN m hcert hne hsz => simp at htail

set_option maxHeartbeats 1000000 in
/-- `no_provable_probeFirst_tail` for a `.bot`-WRAPPED searcher opponent (JustBot's
    frozen `.bot (DupocBot k)` guard target): identical cascade with one extra `.bot`
    unwrap inside the probe replay. -/
theorem no_provable_probeFirst_tail_botOpp (k : Nat) (z p q : Prog) (aT aTgt : Action)
    (g : Formula) (pT pE : Prog)
    (hfalse : ¬ (g.subst (.bot (.search k g pT pE)) (.bot z)).interp)
    (hshape : ∀ k' ψ c0 c1, p ≠ .search k' ψ (.const c0) (.const c1)) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ =
        .plays (.ite (.sim .opp (.bot z)) aT p q) (.bot (.search k g pT pE)) aTgt →
      False := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro φ hp hK htail
    cases hp with
    -- the SIX source-transparency bridge rules (formerly reached via `struct` + the
    -- `Derivation` census): each names its own readable `me`, which `not_readable_probeFirst z p q aT hshape` refutes.
    | searchBranch gg psi aa bb me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inl ⟨gg, psi, _, _, hme⟩)
    | simStep me pp qq oppo aa hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inl ⟨pp, qq, hme⟩))
    | botSimStep me pp qq oppo aa hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inr (Or.inl ⟨pp, qq, hme⟩)))
    | botSearchStep gg psi aa bb me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inr (Or.inr (Or.inl ⟨gg, psi, _, _, hme⟩))))
    | iteBranchSearch_t gg zz aa' cc0 cc1 psi qq me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_probeFirst z p q aT hshape (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨zz, aa', gg, psi, cc0, cc1, qq, hme⟩)))))
    | eqRefl pp hsz => simp [rightTail] at htail
    | eqNeg pp qq hne hsz => simp [rightTail] at htail
    | atom h =>
        cases h with
        | mk hpp hn =>
          simp only [rightTail_plays, Formula.plays.injEq] at htail
          obtain ⟨rfl, rfl, rfl⟩ := htail
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
    | weakenImpl φ' ψ m hψ hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih m (by omega) ψ hψ (by omega) htail
    | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q' me oppo hme hpre hm hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        simp at hme
    | implTrans φ' ψ χ a b h1 h2 hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih b (by omega) _ h2 (by omega) (by simpa using htail)
    | atomBoxImpl kBox p' q' a hcert hsz => simp at htail
    | boxIntro kIn K' φ' hpre hsz => simp at htail
    | mp m₁ m₂ φ' α h1 h2 hsz =>
        have hα := Formula.size_pos φ
        exact ih m₁ (by omega) _ h1 (by omega) (by simpa using htail)
    | axK a b c m K' φ' α hpre hab hsz => simp at htail
    | box4 a b K' φ' h1 h2 => simp at htail
    | diagF pm fb g' K' tgt hpre hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih pm (by omega) _ hpre (by omega) (by simpa using htail)
    | diagB pm fb g' K' tgt hpre hsz => simp at htail
    | axKf a b c K' φ' α h1 h2 => simp at htail
    | impS2 φ' ψ χ m₁ m₂ K' h1 h2 hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih m₁ (by omega) _ h1 (by omega) (by simpa using htail)
    | boxMono a b K' φ' hab hsz => simp at htail
    | atomNeg p' q' b aN m hcert hne hsz => simp at htail


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
    const-branched `.search`. That disjunct belongs to `searchThenSearch_t`, which every floor
    theorem discharges in its OWN arm (via the action-specific `hinner`: the stacked rule
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

set_option maxHeartbeats 1000000 in
/-- **The floor at the searcher's own play**: no proof of ≤ k characters concludes any
    formula whose spine tail is "the budget-`k` searcher plays `aTgt` against `O`",
    when the searcher's guard instance vs `O` is false. The self-referential shape:
    PrudentBot's same-`k` self-prudence is the canonical instance. -/
theorem no_provable_searcherPlay_tail (k : Nat) (g : Formula) (pT pE O : Prog)
    (aTgt : Action)
    (hfalse : ¬ (g.subst (.search k g pT pE) O).interp)
    (hshape : ∀ c0 c1, ¬ (pT = .const c0 ∧ pE = .const c1))
    (hinner : ∀ k₂ ψ₂ c1, pT ≠ .search k₂ ψ₂ (.const aTgt) (.const c1)) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays (.search k g pT pE) O aTgt → False := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro φ hp hK htail
    cases hp with
    -- the SIX source-transparency bridge rules (formerly reached via `struct` + the
    -- `Derivation` census): each names its own readable `me`, which `not_readable_searchNonConst k g pT pE hshape hinner` refutes.
    | searchBranch gg psi aa bb me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_searchNonConst k g pT pE hshape (Or.inl ⟨gg, psi, _, _, hme⟩)
    | simStep me pp qq oppo aa hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_searchNonConst k g pT pE hshape (Or.inr (Or.inl ⟨pp, qq, hme⟩))
    | botSimStep me pp qq oppo aa hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_searchNonConst k g pT pE hshape (Or.inr (Or.inr (Or.inl ⟨pp, qq, hme⟩)))
    | botSearchStep gg psi aa bb me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_searchNonConst k g pT pE hshape (Or.inr (Or.inr (Or.inr (Or.inl ⟨gg, psi, _, _, hme⟩))))
    | iteBranchSearch_t gg zz aa' cc0 cc1 psi qq me oppo hme hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, -, -⟩ := htail
        exact not_readable_searchNonConst k g pT pE hshape (Or.inr (Or.inr (Or.inr (Or.inr ⟨zz, aa', gg, psi, cc0, cc1, qq, hme⟩))))
    | eqRefl pp hsz => simp [rightTail] at htail
    | eqNeg pp qq hne hsz => simp [rightTail] at htail
    | atom h =>
        cases h with
        | mk hpp hn =>
          simp only [rightTail_plays, Formula.plays.injEq] at htail
          obtain ⟨rfl, rfl, rfl⟩ := htail
          cases hpp with
          | search_t hProv hbr => exact hfalse (Pf_sound _ _ hProv)
          | search_f hneg hbr => simp only [c_node] at hn; omega
    | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q' me oppo hme hpre hm hsz =>
        simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at htail
        obtain ⟨rfl, rfl, rfl⟩ := htail
        simp only [Prog.search.injEq] at hme
        exact hinner _ _ _ hme.2.2.1
    | weakenImpl φ' ψ m hψ hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih m (by omega) ψ hψ (by omega) htail
    | implTrans φ' ψ χ a b h1 h2 hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih b (by omega) _ h2 (by omega) (by simpa using htail)
    | atomBoxImpl kBox p' q' a hcert hsz => simp at htail
    | boxIntro kIn K' φ' hpre hsz => simp at htail
    | mp m₁ m₂ φ' α h1 h2 hsz =>
        have hα := Formula.size_pos φ
        exact ih m₁ (by omega) _ h1 (by omega) (by simpa using htail)
    | axK a b c m K' φ' α hpre hab hsz => simp at htail
    | box4 a b K' φ' h1 h2 => simp at htail
    | diagF pm fb g' K' tgt hpre hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih pm (by omega) _ hpre (by omega) (by simpa using htail)
    | diagB pm fb g' K' tgt hpre hsz => simp at htail
    | axKf a b c K' φ' α h1 h2 => simp at htail
    | impS2 φ' ψ χ m₁ m₂ K' h1 h2 hsz =>
        simp only [rightTail_impl] at htail
        simp only [Formula.size] at hsz
        exact ih m₁ (by omega) _ h1 (by omega) (by simpa using htail)
    | boxMono a b K' φ' hab hsz => simp at htail
    | atomNeg p' q' b aN m hcert hne hsz => simp at htail

end PD.BaseTheorems
