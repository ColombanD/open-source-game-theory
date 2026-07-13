import PrisonersDilemma.Base.Soundness

/-!
# Base/Exclusion — structural exclusion: what `S` can NOT conclude

The positive layers certify plays; this file starts the NEGATIVE direction, needed by
the honest outcome theorems for the floor-killed pairs (the tombstones in
`Theorems/DupocBot.lean` / `Theorems/LlmGenerations/PrudentBot.lean`): `¬Provable k φ`
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
  which closes the `struct` entry point of `Provable` in one stroke.

Consumers combine the census with a budget strong-induction over `Provable` (the
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

/-- The five player shapes whose plays the source-transparency bridge rules can
    conclude (`searchBranch`, `simStep`, `botSimStep`, `botSearchStep`,
    `iteBranchSearch_t` — one disjunct each, in that order). A player of any OTHER
    shape has no `Derivation` route to its play atoms (`tail_plays_readable`). -/
def ReadableMe (me : Prog) : Prop :=
  (∃ k ψ a b, me = .search k ψ (.const a) (.const b)) ∨
  (∃ p q, me = .sim p q) ∨
  (∃ p q, me = .bot (.sim p q)) ∨
  (∃ k ψ a b, me = .bot (.search k ψ (.const a) (.const b))) ∨
  (∃ z a' k ψ c0 c1 q,
    me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q)

/-- **The Derivation census**: if a `Derivation`'s conclusion has a plays-atom spine
    tail, the player is bridge-readable. Induction: the logical core (`modusPonens`,
    `hypSyll`) preserves the spine tail; each bridge rule's tail names its own (readable)
    `me`; `eqRefl`/`eqNeg` have non-plays tails. -/
theorem tail_plays_readable :
    ∀ {φ : Formula}, Derivation φ →
      ∀ {me oppo : Prog} {a : Action},
        rightTail φ = .plays me oppo a → ReadableMe me := by
  intro φ d
  induction d with
  | modusPonens φ ψ d1 d2 ih1 ih2 =>
      intro me oppo a h
      exact ih1 (by simpa using h)
  | hypSyll φ ψ χ d1 d2 ih1 ih2 =>
      intro me oppo a h
      exact ih2 (by simpa using h)
  | searchBranch k ψ a b me' oppo' hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨k, ψ, _, _, hme⟩
  | simStep me' p q oppo' a hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨p, q, hme⟩)
  | botSimStep me' p q oppo' a hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨p, q, hme⟩))
  | botSearchStep k ψ a b me' oppo' hme =>
      intro me oppo a' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, ψ, _, _, hme⟩)))
  | iteBranchSearch_t k z a' c0 c1 ψ q me' oppo' hme =>
      intro me oppo a'' h
      simp only [rightTail_impl, rightTail_plays, Formula.plays.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨z, a', k, ψ, c0, c1, q, hme⟩)))
  | eqRefl p =>
      intro me oppo a h
      simp at h
  | eqNeg p q hne =>
      intro me oppo a h
      simp at h

/-! ## The floor lower bound, generalized

The three floor-killed pairs (DBot×DupocBot, EBot×DupocBot, EBot×PrudentBot) share one
shape: the SIMULATOR is a probe-first `.ite` — `me = .ite (.sim .opp (.bot z)) .C
(.const .D) q` (DBot: `q = .const .C`; EBot: `q` = its inner probe cascade) — and the
OPPONENT is a top-level search bot `.search k g pT pE` whose guard instance against the
probe `.bot z` is semantically FALSE. Any certificate of "simulator plays C vs the
searcher" must replay the probe, i.e. certify the searcher's play against `.bot z`:
`search_t` dies by soundness (the guard instance is false), `search_f` charges the
literal floor summand `k` — so every certificate costs > k, the searcher's own budget. -/

/-- The probe-first simulator shape is never bridge-readable: its then-branch is a
    `.const`, and `iteBranchSearch_t` (the only `.ite` bridge) needs a `.search`
    then-branch. -/
theorem not_readable_probeFirst (z q : Prog) :
    ¬ ReadableMe (.ite (.sim .opp (.bot z)) .C (.const .D) q) := by
  rintro (⟨k, ψ, a, b, h⟩ | ⟨p, r, h⟩ | ⟨p, r, h⟩ | ⟨k, ψ, a, b, h⟩ |
          ⟨w, a', k, ψ, c0, c1, r, h⟩) <;> simp at h

set_option maxHeartbeats 1000000 in
/-- **The `search_f` floor as a cost lower bound** (generalized): no proof of ≤ k
    characters concludes any formula whose implication-spine tail is "the probe-first
    simulator plays C against the budget-`k` searcher" — in particular (spine of
    length zero) the searcher's own guard instance is unprovable at its own budget.

    Strong induction on the budget: `struct` dies by the census
    (`not_readable_probeFirst`); `atom` dies inside the `PlaysProof` replay (the
    simulator's guard forces the searcher's probe play, where `search_t` is refuted by
    `hfalse` + soundness and `search_f` carries the literal floor summand `k`); the
    `app`/`weakenImpl`/`implTrans`/`diagF`/`impS2` regress descends because transcript
    cumulativity makes every premise budget strictly smaller. The non-cumulative budget
    citations (`search_t`, `searchThenSearch_t`) never enter the induction — killed
    semantically / by shape — which is exactly why this pair-shaped bound is provable
    while the universal closure stays open. -/
theorem no_provable_probeFirst_C_tail (k : Nat) (z q : Prog) (g : Formula)
    (pT pE : Prog)
    (hfalse : ¬ (g.subst (.search k g pT pE) (.bot z)).interp) :
    ∀ K φ, Provable K φ → K ≤ k →
      rightTail φ =
        .plays (.ite (.sim .opp (.bot z)) .C (.const .D) q) (.search k g pT pE) .C →
      False := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro φ hp hK htail
    cases hp with
    | struct h =>
        obtain ⟨d, _⟩ := h
        exact not_readable_probeFirst z q (tail_plays_readable d htail)
    | atom h =>
        cases h with
        | mk hpp hn =>
          simp only [rightTail_plays, Formula.plays.injEq] at htail
          obtain ⟨rfl, rfl, rfl⟩ := htail
          cases hpp with
          | ite_t hg hr hbr => cases hbr
          | ite_f hg hr hbr =>
              cases hg with
              | sim hin =>
                simp only [Prog.subst] at hin
                cases hin with
                | search_t hProv hbr2 =>
                    exact hfalse (Provable_sound _ _ hProv)
                | search_f hneg hbr2 =>
                    simp only [c_node] at hn
                    omega
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
    | app k' m₁ m₂ φ' α h1 h2 hsz =>
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
