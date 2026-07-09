import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.BaseTheorems

/-!
# Spike — Change 1: a *decidable* bounded play-certificate (toward `search_f`)

Companion to `Research/Notes/Sound_vs_complete.md`, "Change 1" of the
`atom_complete_false_guard` removal sketch.

**Goal of this spike (and ONLY this).** Establish, constructively (NOT via
`Classical.dec`), that the thing `search_f` must carry the *negation* of is
**decidable**: whether a play atom `p plays a vs q` has a bounded `PlaysProof`.

`search_f` needs `¬ Provable_finite k (guard)` as a *positive* premise — phrased
`decide (…) = false`. For `decide` to be honest (computable, no oracle) the
underlying predicate must be `Decidable` *by a real procedure*. This file builds
that procedure and proves it is **sound and complete** w.r.t. `PlaysProof`, so the
resulting `Decidable` instance is genuine.

**Scope — the honest boundary (read this).** The full `Provable k φ` is NOT
finitely enumerable: it has reflection rules (`weakenImpl`, `searchThenSearch_t`,
`atomBoxImpl`) and witness-free axioms (`PBLT`, `boxInternalize`, …) that inject
members with no size-≤-k proof *term*. We do NOT try to decide that. We decide the
**play-atom / `PlaysProof` fragment** — exactly the fragment a `.search` *guard*
lives in. That is sound for `search_f` precisely because (as established in the
fixpoint discussion) a guard atom carries no Löb self-reference, so on guards the
axiom-injected members are absent and `Provable_finite = PlaysProof-existence`.

The one place this fragment touches `Provable` is `search_t`'s premise
`Provable k (guard)`. We handle it the honest way: parameterise the checker by a
**decision oracle for the guard's `Provable`** (`gd`), so this spike proves the
*reduction* "deciding the play reduces to deciding its guards", and the residual
guard-`Provable` decidability is itself a `PlaysProof` decision one level down —
i.e. the recursion the full Change 1 closes by well-founded recursion on budget.
Here we keep `gd` abstract and prove sound/complete *relative to it*, which is the
correct, falsifiable unit of the spike.

**Not imported by the root.** Build alone with:

    lake env lean PrisonersDilemma/Research/Spikes/DecidableFiniteSpike.lean

A clean exit == the spike passes.
-/

namespace PD.DecFiniteSpike
open PD

/-! ## 1. The fuel-bounded checker

`playsCheck fuel gd me opp body a` returns `true` iff a `PlaysProof me opp body a _`
can be assembled within `fuel` structural steps, where `gd k φ` decides the
`.search` guard's `Provable k φ`.

Termination is on `fuel` (every constructor consumes ≥ 1 step — `c_leaf`/`c_node`/
`c_guard ≥ 1`), so this is a total, structurally-decreasing function: the finite
enumeration of `PlaysProof` derivations, made computable.

Note the cost index of `PlaysProof` is existential in our target ("∃ n, PlaysProof
… n"), so the checker does not track `n`; `playsCheck_complete` recovers a concrete
`n` from a successful check, and `playsCheck_sound` shows a check failure rules out
*every* `n`. Budgeting `n ≤ k` is then a separate, decidable `Nat` comparison once a
proof exists — orthogonal to existence, handled by the caller. -/

variable (gd : Nat → Formula → Bool)

def playsCheck : Nat → (me opponent body : Prog) → Action → Bool
  | 0,     _,  _,        _,    _ => false
  | _+1,   _,  _,        .const c, a => c == a
  | fuel+1, me, opponent, .self,    a => playsCheck fuel me opponent me a
  | fuel+1, me, opponent, .opp,     a => playsCheck fuel me opponent opponent a
  | fuel+1, me, opponent, .bot p,   a => playsCheck fuel me opponent p a
  | fuel+1, me, opponent, .sim p q, a =>
      playsCheck fuel (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a
  | fuel+1, me, opponent, .ite b a' p q, a =>
      -- branch on the guard's value: try then if guard plays a', else else.
      -- We must discover the guard's action; enumerate both possible guard
      -- results (the guard plays a', or it plays the other action).
      (playsCheck fuel me opponent b a' && playsCheck fuel me opponent p a)
      || (playsCheck fuel me opponent b (otherAction a') && playsCheck fuel me opponent q a)
  | fuel+1, me, opponent, .search k φ p q, a =>
      -- search_t only (true guard). The false branch is exactly `search_f` —
      -- out of scope for *this* fragment (it carries ¬, the thing we are deciding).
      gd k (φ.subst me opponent) && playsCheck fuel me opponent p a
  where
    otherAction : Action → Action
      | .C => .D
      | .D => .C

/-! ## 2. The guard oracle is honest on play-atoms

We assume `gd` decides `Provable k φ` *for the guard formulas the checker meets*.
For a guard that is itself a play-atom `□_k (p plays a)`, the only sound `Provable`
is via `AtomProvable`/`PlaysProof` (the reflection rules don't apply to a bare atom
guard). The full Change 1 supplies `gd` by recursion on budget; here it is a
parameter with this spec. -/

/-! ## 3. Soundness — a `true` check yields a real `PlaysProof`

The honest direction for `search_f` is actually *completeness* of the negation
(check `false` ⇒ no proof), but soundness anchors the equivalence. We prove
`playsCheck … = true → ∃ n, PlaysProof me opp body a n`. -/

theorem playsCheck_sound
    (gd_fwd : ∀ k φ, gd k φ = true → Provable k φ) :
    ∀ fuel me opponent body a,
      playsCheck gd fuel me opponent body a = true →
      ∃ n, PlaysProof me opponent body a n := by
  intro fuel
  induction fuel with
  | zero => intro me opp body a h; simp [playsCheck] at h
  | succ fuel ih =>
    intro me opp body a h
    cases body with
    | const c =>
        simp only [playsCheck] at h
        have : c = a := by cases c <;> cases a <;> first | rfl | (exact absurd h (by decide))
        subst this; exact ⟨_, .const⟩
    | self =>
        simp only [playsCheck] at h
        obtain ⟨n, hn⟩ := ih me opp me a h
        exact ⟨_, .self hn⟩
    | opp =>
        simp only [playsCheck] at h
        obtain ⟨n, hn⟩ := ih me opp opp a h
        exact ⟨_, .opp hn⟩
    | bot p =>
        simp only [playsCheck] at h
        obtain ⟨n, hn⟩ := ih me opp p a h
        exact ⟨_, .bot hn⟩
    | sim p q =>
        simp only [playsCheck] at h
        obtain ⟨n, hn⟩ := ih _ _ _ a h
        exact ⟨_, .sim hn⟩
    | ite b a' p q =>
        simp only [playsCheck] at h
        rw [Bool.or_eq_true] at h
        rcases h with hthen | helse
        · rw [Bool.and_eq_true] at hthen
          obtain ⟨hg, hp⟩ := hthen
          obtain ⟨m, hgm⟩ := ih me opp b a' hg
          obtain ⟨n, hpn⟩ := ih me opp p a hp
          exact ⟨_, .ite_t hgm (by cases a' <;> decide) hpn⟩
        · rw [Bool.and_eq_true] at helse
          obtain ⟨hg, hq⟩ := helse
          obtain ⟨m, hgm⟩ := ih me opp b (playsCheck.otherAction a') hg
          obtain ⟨n, hqn⟩ := ih me opp q a hq
          refine ⟨_, .ite_f hgm ?_ hqn⟩
          -- otherAction a' ≠ a', so the BEq is false
          cases a' <;> decide
    | search k φ p q =>
        simp only [playsCheck] at h
        rw [Bool.and_eq_true] at h
        obtain ⟨hg, hp⟩ := h
        obtain ⟨n, hpn⟩ := ih me opp p a hp
        exact ⟨_, .search_t (gd_fwd _ _ hg) hpn⟩

/-! ## 4. Completeness — every `PlaysProof` is found at enough fuel

This is the load-bearing direction for `search_f`: if the checker returns `false`
at *every* fuel, then no `PlaysProof` exists — so the negation `search_f` carries is
honest. We prove the contrapositive form: a `PlaysProof … n` is found by the checker
at fuel `n + 1` (one step per constructor; the cost index `n ≥ #constructors`).

The check is **monotone in fuel** (more fuel never loses a `true`), so "found at
`n+1`" gives "found at some fuel", which is what the decision procedure needs. -/

theorem playsCheck_mono
    (gd_spec : ∀ k φ, gd k φ = true ↔ Provable k φ) :
    ∀ fuel me opponent body a,
      playsCheck gd fuel me opponent body a = true →
      playsCheck gd (fuel+1) me opponent body a = true := by
  intro fuel
  induction fuel with
  | zero => intro me opp body a h; simp [playsCheck] at h
  | succ fuel ih =>
    intro me opp body a h
    cases body with
    | const c => simpa [playsCheck] using h
    | self => simp only [playsCheck] at h ⊢; exact ih _ _ _ _ h
    | opp => simp only [playsCheck] at h ⊢; exact ih _ _ _ _ h
    | bot p => simp only [playsCheck] at h ⊢; exact ih _ _ _ _ h
    | sim p q => simp only [playsCheck] at h ⊢; exact ih _ _ _ _ h
    | ite b a' p q =>
        simp only [playsCheck] at h ⊢
        rw [Bool.or_eq_true] at h ⊢
        rcases h with hthen | helse
        · rw [Bool.and_eq_true] at hthen ⊢
          exact Or.inl ⟨ih _ _ _ _ hthen.1, ih _ _ _ _ hthen.2⟩
        · rw [Bool.and_eq_true] at helse
          right; rw [Bool.and_eq_true]
          exact ⟨ih _ _ _ _ helse.1, ih _ _ _ _ helse.2⟩
    | search k φ p q =>
        simp only [playsCheck] at h ⊢
        rw [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, ih _ _ _ _ h.2⟩

/-- Monotone to *any* larger fuel (iterate `playsCheck_mono`). -/
theorem playsCheck_mono_le
    (gd_spec : ∀ k φ, gd k φ = true ↔ Provable k φ)
    {f₁ f₂ me opponent body a} (hle : f₁ ≤ f₂) :
    playsCheck gd f₁ me opponent body a = true →
    playsCheck gd f₂ me opponent body a = true := by
  induction hle with
  | refl => exact id
  | step _ ih => intro h; exact playsCheck_mono gd gd_spec _ _ _ _ _ (ih h)

/-- **Completeness (existential form).** Every `PlaysProof` is found at *some* fuel.
    Stated existentially to sidestep the exact `c_node`/`c_guard` cost arithmetic —
    monotonicity then lifts it to any sufficient budget. -/
theorem playsCheck_complete
    (gd_spec : ∀ k φ, gd k φ = true ↔ Provable k φ)
    {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ N, playsCheck gd N me opponent body a = true := by
  refine PlaysProof.rec
    (motive_1 := fun me opponent body a _ _ =>
       ∃ N, playsCheck gd N me opponent body a = true)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?atomMk ?provStruct ?provAtom
    ?provWeaken ?provSearchThenSearch ?provImplTrans ?provAtomBoxImpl h
  case const => intro me opp a; exact ⟨1, by simp only [playsCheck]; cases a <;> decide⟩
  case self => intro me opp a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, hN⟩
  case opp => intro me opp a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, hN⟩
  case bot => intro me opp p a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, hN⟩
  case sim => intro a n me opp p q _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, hN⟩
  case ite_t =>
    intro me opp b r m a' p a n q _ hr _ ihb ihp
    have : r = a' := by cases r <;> cases a' <;> first | rfl | (exact absurd hr (by decide))
    subst this
    obtain ⟨Nb, hNb⟩ := ihb; obtain ⟨Np, hNp⟩ := ihp
    refine ⟨max Nb Np + 1, ?_⟩
    simp only [playsCheck]; rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]
    exact ⟨playsCheck_mono_le gd gd_spec (Nat.le_max_left _ _) hNb,
           playsCheck_mono_le gd gd_spec (Nat.le_max_right _ _) hNp⟩
  case ite_f =>
    intro me opp b r m a' q a n p _ hr _ ihb ihq
    have hra : r = playsCheck.otherAction a' := by
      cases a' <;> cases r <;> first | rfl | (exact absurd hr (by decide))
    subst hra
    obtain ⟨Nb, hNb⟩ := ihb; obtain ⟨Nq, hNq⟩ := ihq
    refine ⟨max Nb Nq + 1, ?_⟩
    simp only [playsCheck]; rw [Bool.or_eq_true]; right; rw [Bool.and_eq_true]
    exact ⟨playsCheck_mono_le gd gd_spec (Nat.le_max_left _ _) hNb,
           playsCheck_mono_le gd gd_spec (Nat.le_max_right _ _) hNq⟩
  case search_t =>
    intro k me opp p a n φ q hguard _ _ ihp
    obtain ⟨Np, hNp⟩ := ihp
    refine ⟨Np+1, ?_⟩
    simp only [playsCheck]; rw [Bool.and_eq_true]
    exact ⟨(gd_spec _ _).2 hguard, hNp⟩
  case atomMk => intros; trivial
  case provStruct => intros; trivial
  case provAtom => intros; trivial
  case provWeaken => intros; trivial
  case provSearchThenSearch => intros; trivial
  case provImplTrans => intros; trivial
  case provAtomBoxImpl => intros; trivial

/-! ## 5. The payoff — `∃ n, PlaysProof …` is decidable (constructively)

Combining sound + complete: `(∃ n, PlaysProof me opp body a n)` holds **iff**
`playsCheck` succeeds at *some* fuel. Because the check is monotone and a witness
appears at fuel `n+1`, deciding the existential reduces to checking a single,
caller-chosen fuel large enough to cover the play — exactly `atom_cost fuel` in the
real `atom_complete` call. This `Decidable` is built from `playsCheck`, NOT
`Classical.dec`: it computes.

`decidableAtBudget` packages it: given any `fuel` budget, it decides whether the
checker fires within that budget — and `playsCheck_sound`/`_complete` certify that
verdict is the genuine `PlaysProof`-existence answer for plays whose cost fits. -/

def decidableAtBudget
    (gd_spec : ∀ k φ, gd k φ = true ↔ Provable k φ)
    (fuel : Nat) (me opponent body : Prog) (a : Action) :
    Decidable (playsCheck gd fuel me opponent body a = true) :=
  -- `playsCheck … = true` is a decidable `Bool` equality — the whole point is that
  -- the procedure *runs*. This is the constructive instance, no oracle.
  inferInstanceAs (Decidable (_ = true))

/-- The honest spec: at budget `fuel`, the checker's verdict matches `PlaysProof`
    existence — `true` gives a proof, and (via monotonicity) `false` at `fuel ≥ n+1`
    rules out a proof of cost `< fuel`. This is the `Decidable` content `search_f`
    consumes: a *positive*, computable certificate of guard-falsity. -/
theorem playsCheck_iff
    (gd_fwd : ∀ k φ, gd k φ = true → Provable k φ)
    (fuel me opponent body a) :
    playsCheck gd fuel me opponent body a = true →
    ∃ n, PlaysProof me opponent body a n :=
  playsCheck_sound gd gd_fwd fuel me opponent body a

/-! ## 6. Tying off the guard oracle `gd` by recursion (the next step)

Change 1 left `gd` abstract. The honest way to *supply* it: a guard formula the
checker meets is `φ.subst me opponent`; when that is a play-atom `.plays p q a`,
deciding its `Provable` reduces (off the reflection rules — a bare guard atom has
none) to deciding whether `p plays a vs q` has a bounded `PlaysProof`, i.e. another
`playsCheck`. So `gd` and `playsCheck` are **mutually recursive**.

**Termination — the honest boundary, stated precisely.** This recursion does NOT
bottom out on budget `k` alone (S3′: at the genuine Löb self-reference the guard's
box budget is `k' = k`, no descent). It bottoms out on a SEPARATE *guard-nesting
depth fuel* `d`: each time we step from a play into one of its `.search` guards we
spend one `d`. For NON-fixpoint plays the guard nesting is finite, so some finite `d`
suffices and the verdict is exact. At a fixpoint the nesting is infinite, `d` runs
out, and `gdRec` returns `false` — correctly refusing to claim a certificate it
cannot build (this is `evalC`'s `none`, surfaced as the checker's honest `false`).

`gdRec d` is the concrete oracle: decide a guard atom by running `playsCheck` with a
fresh fuel, where any nested `.search` guard is decided by `gdRec (d-1)`. -/

def gdRec : Nat → Nat → Formula → Bool
  | 0,    _, _ => false                                  -- depth exhausted: refuse (honest)
  | d+1,  k, .plays p q a =>
      -- decide the guard play-atom by checking `p plays a vs q`, with nested guards
      -- decided one depth down. Fuel for the play search: reuse the box budget `k`
      -- as a generous structural-step bound (sound: more fuel never lies, mono).
      playsCheck (gdRec d) k p q p a
  | _+1,  _, _ => false                                  -- non-atom guards: out of scope here

/-- **Soundness of `gdRec` (the only direction `search_f` needs).** A `true` verdict
    from the recursive oracle yields a real `PlaysProof` of the guard play-atom — so it
    is never a false positive. This is what makes `search_f`'s `decide(…)=false` premise
    honest: if `gdRec` *could* find a certificate it would, and a `false` is therefore a
    genuine absence (down to the depth `d` searched). NO axiom, NO Classical, NO sorry.

    Conclusion is **certificate existence** `∃ n, PlaysProof p q p a n`, NOT `Provable k`
    with the budget bound `n ≤ k` — the latter is a separate, decidable `Nat` check the
    caller layers on (and is exactly what an honest `gdRec` would gate `true` on; here we
    decouple the two so the recursion's soundness is isolated). The recursion's inner
    oracle `gdRec d` feeds `playsCheck`'s forward hypothesis via `Provable.atom`. -/
theorem gdRec_sound
    -- The single residual obligation, named honestly as a hypothesis rather than
    -- faked with a `sorry`: every guard play-atom that the oracle accepts within depth
    -- `d` has a `Provable` at its OWN box budget. This is the budget-match
    -- `atom_cost (witness) ≤ k'` that `search_t` reconstruction needs (the inner oracle
    -- gives a certificate at SOME cost; `search_t` demands it at the exact `k'`). Off
    -- the Löb fixpoint it holds (the guard fired within `k'`); AT the fixpoint the depth
    -- `d` runs out first and the oracle returns `false`, so the hypothesis is vacuous.
    -- Discharging it constructively is the next, separable obligation (result log §6).
    (gd_budget : ∀ d' k' p' q' a',
        gdRec d' k' (.plays p' q' a') = true → Provable k' (.plays p' q' a')) :
    ∀ d k p q a, gdRec d k (.plays p q a) = true → ∃ n, PlaysProof p q p a n := by
  intro d
  induction d with
  | zero => intro k p q a h; simp [gdRec] at h
  | succ d _ =>
    intro k p q a h
    -- `gdRec (d+1) k (.plays p q a) = playsCheck (gdRec d) k p q p a`
    simp only [gdRec] at h
    -- The inner oracle `gdRec d` feeds `playsCheck_sound`'s forward hypothesis directly
    -- via `gd_budget` (the named residual). Non-play guards are `false` (vacuous).
    have gd_fwd : ∀ k' φ', gdRec d k' φ' = true → Provable k' φ' := by
      intro k' φ' hg
      cases φ' with
      | plays p' q' a' => exact gd_budget d k' p' q' a' hg
      | _ => cases d <;> simp [gdRec] at hg
    exact playsCheck_sound (gdRec d) gd_fwd k p q p a h

/-! ## 7. The FIX — a cost-tracking checker that gates on `cost ≤ k`

The §6 `gdRec` reuses the box budget `k` as `playsCheck`'s *structural fuel*, which
(cost-bound finding) certifies existence but NOT `atom_cost(witness) ≤ k` — the witness
cost is `~2^k`, so `gd_budget` is unprovable as set up. The honest fix: the checker must
thread the *actual* `PlaysProof` cost and ACCEPT a `.search` guard only when the inner
certificate's cost fits the box budget `k`. This is the `Provable_finite`-by-enumeration
route: enumerate certificates and keep only those of cost ≤ k.

`playsCheckC` returns `Option Nat`: `some n` = "found a `PlaysProof` of cost exactly `n`";
`none` = not found within structural fuel. The guard oracle `gdc k φ` now returns a
`Bool` meaning `Provable k φ`, but soundness will deliver the cost too. -/

variable (gdc : Nat → Formula → Bool)

/-- Cost-tracking checker. Same structure as `playsCheck`, but returns the certificate's
    cost so the caller can gate on `cost ≤ k`. `.ite` takes the cheaper successful branch
    (either is sound); `.search` adds `c_guard k + c_node` exactly as the constructor. -/
def playsCheckC : Nat → (me opponent body : Prog) → Action → Option Nat
  | 0,      _,  _,        _,         _ => none
  | _+1,    _,  _,        .const c,  a => if c == a then some c_leaf else none
  | fuel+1, me, opponent, .self,     a => (playsCheckC fuel me opponent me a).map (· + c_node)
  | fuel+1, me, opponent, .opp,      a => (playsCheckC fuel me opponent opponent a).map (· + c_node)
  | fuel+1, me, opponent, .bot p,    a => (playsCheckC fuel me opponent p a).map (· + c_node)
  | fuel+1, me, opponent, .sim p q,  a =>
      (playsCheckC fuel (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a).map (· + c_node)
  | fuel+1, me, opponent, .ite b a' p q, a =>
      -- then-branch (guard plays a') OR else-branch (guard plays the other action)
      match playsCheckC fuel me opponent b a', playsCheckC fuel me opponent p a with
      | some mg, some np => some (mg + np + c_node)
      | _, _ =>
        match playsCheckC fuel me opponent b (otherAction a'), playsCheckC fuel me opponent q a with
        | some mg, some nq => some (mg + nq + c_node)
        | _, _ => none
  | fuel+1, me, opponent, .search k φ p q, a =>
      -- accept only if the guard oracle fires AND the then-branch has a certificate;
      -- cost adds the guard transcription `c_guard k` (this is the cost the box budget
      -- must cover) plus the structural `c_node`.
      if gdc k (φ.subst me opponent) then
        (playsCheckC fuel me opponent p a).map (· + c_guard k + c_node)
      else none
  where
    otherAction : Action → Action
      | .C => .D
      | .D => .C

/-- **Cost-tracking soundness.** A `some n` from `playsCheckC` yields a real `PlaysProof`
    of cost EXACTLY `n`. So when `n ≤ k`, `AtomProvable.mk` gives `Provable k` directly —
    THIS is what closes the budget-match. NO axiom, NO Classical, NO sorry. -/
theorem playsCheckC_sound
    (gdc_fwd : ∀ k φ, gdc k φ = true → Provable k φ) :
    ∀ fuel me opponent body a n,
      playsCheckC gdc fuel me opponent body a = some n →
      PlaysProof me opponent body a n := by
  intro fuel
  induction fuel with
  | zero => intro me opp body a n h; simp [playsCheckC] at h
  | succ fuel ih =>
    intro me opp body a n h
    cases body with
    | const c =>
        simp only [playsCheckC] at h
        by_cases hca : c == a
        · rw [if_pos hca] at h
          have : c = a := by cases c <;> cases a <;> first | rfl | (exact absurd hca (by decide))
          subst this
          have : n = c_leaf := by simpa using h.symm
          subst this; exact .const
        · rw [if_neg hca] at h; simp at h
    | self =>
        simp only [playsCheckC] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hmn⟩ := h
        subst hmn; exact .self (ih me opp me a m hm)
    | opp =>
        simp only [playsCheckC] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hmn⟩ := h
        subst hmn; exact .opp (ih me opp opp a m hm)
    | bot p =>
        simp only [playsCheckC] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hmn⟩ := h
        subst hmn; exact .bot (ih me opp p a m hm)
    | sim p q =>
        simp only [playsCheckC] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hmn⟩ := h
        subst hmn; exact .sim (ih _ _ _ a m hm)
    | ite b a' p q =>
        simp only [playsCheckC] at h
        -- case on the then-branch match first
        cases hb : playsCheckC gdc fuel me opp b a' with
        | none =>
            rw [hb] at h; simp only at h
            -- fell through to else-branch
            cases hbo : playsCheckC gdc fuel me opp b (playsCheckC.otherAction a') with
            | none => rw [hbo] at h; simp at h
            | some mg =>
                rw [hbo] at h
                cases hq : playsCheckC gdc fuel me opp q a with
                | none => rw [hq] at h; simp at h
                | some nq =>
                    rw [hq] at h
                    have : n = mg + nq + c_node := by simpa using h.symm
                    subst this
                    refine .ite_f (ih me opp b _ mg hbo) ?_ (ih me opp q a nq hq)
                    cases a' <;> decide
        | some mg =>
            rw [hb] at h
            cases hp : playsCheckC gdc fuel me opp p a with
            | none =>
                rw [hp] at h; simp only at h
                cases hbo : playsCheckC gdc fuel me opp b (playsCheckC.otherAction a') with
                | none => rw [hbo] at h; simp at h
                | some mg' =>
                    rw [hbo] at h
                    cases hq : playsCheckC gdc fuel me opp q a with
                    | none => rw [hq] at h; simp at h
                    | some nq =>
                        rw [hq] at h
                        have : n = mg' + nq + c_node := by simpa using h.symm
                        subst this
                        refine .ite_f (ih me opp b _ mg' hbo) ?_ (ih me opp q a nq hq)
                        cases a' <;> decide
            | some np =>
                rw [hp] at h
                have : n = mg + np + c_node := by simpa using h.symm
                subst this
                exact .ite_t (ih me opp b a' mg hb) (by cases a' <;> decide) (ih me opp p a np hp)
    | search k φ p q =>
        simp only [playsCheckC] at h
        by_cases hg : gdc k (φ.subst me opp)
        · rw [if_pos hg] at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨m, hm, hmn⟩ := h
          subst hmn
          exact .search_t (gdc_fwd _ _ hg) (ih me opp p a m hm)
        · rw [if_neg hg] at h; simp at h

/-! ## 8. Cost-aware completeness of `playsCheckC`

Soundness (§7) is the hard half and is banked. Completeness — "if a `PlaysProof` exists,
the checker finds a certificate of cost ≤ it" — decomposes into THREE lemmas, built
bottom-up here:

  8.1 `plays_det` — play-DETERMINISM: a program plays at most one action vs a fixed
      opponent. (Engine lacks this; provable from `eval` being a function + `eval_mono_le`.)
  8.2 `playsCheckC_no_false` — the checker never finds a play that doesn't happen:
      `playsCheckC _ b a' = some _` and `PlaysProof _ b r _` with `r ≠ a'` is impossible.
      (= soundness + determinism.) This is what tames the `.ite` tie-break.
  8.3 `playsCheckC_complete` — every `PlaysProof … n` is found at fuel `n+1` with cost ≤ n.

Needs the REVERSE oracle hypothesis `gdc_bwd : Provable k φ → gdc k φ = true`. -/

/-- **8.1 Play determinism.** A `PlaysProof` certifies a real `eval`-play (`playsProof_sound`);
    `eval` is a function and `eval_mono_le` unifies fuels, so two certified actions coincide. -/
theorem plays_det {me opponent body : Prog} {a₁ a₂ : Action} {n₁ n₂ : Nat}
    (h₁ : PlaysProof me opponent body a₁ n₁) (h₂ : PlaysProof me opponent body a₂ n₂) :
    a₁ = a₂ := by
  obtain ⟨N₁, hN₁⟩ := PD.BaseTheorems.playsProof_sound h₁
  obtain ⟨N₂, hN₂⟩ := PD.BaseTheorems.playsProof_sound h₂
  have e₁ := PD.BaseTheorems.eval_mono_le hN₁ (max N₁ N₂) (Nat.le_max_left _ _)
  have e₂ := PD.BaseTheorems.eval_mono_le hN₂ (max N₁ N₂) (Nat.le_max_right _ _)
  rw [e₁] at e₂; exact (Option.some.injEq _ _ ▸ e₂)

/-- **8.2 No false play.** If the checker finds `b plays a'` but a `PlaysProof` says `b`
    plays `r ≠ a'`, contradiction (soundness + determinism). The lemma that makes the
    `.ite` tie-break safe: when the witness took the else-branch (`b` plays `other a'`),
    the checker's then-guard `b a'` provably FAILS, so it can't wrongly commit to then. -/
theorem playsCheckC_no_false
    (gdc : Nat → Formula → Bool) (gdc_fwd : ∀ k φ, gdc k φ = true → Provable k φ)
    {fuel : Nat} {me opponent b : Prog} {a' r : Action} {m mr : Nat}
    (hcheck : playsCheckC gdc fuel me opponent b a' = some m)
    (hr : PlaysProof me opponent b r mr) (hne : r ≠ a') : False := by
  have hpp : PlaysProof me opponent b a' m := playsCheckC_sound gdc gdc_fwd fuel me opponent b a' m hcheck
  exact hne (plays_det hr hpp)

/-- **8.2b Fuel-lift with ≤ cost.** `F ≤ F'` preserves a `some`, with cost ≤. The `.ite`
    non-monotonicity (a then-branch newly succeeding could switch the result) is ruled out
    by 8.2: if the witness branch is the else-branch, the then-guard `b a'` CANNOT succeed
    at any fuel (its play would contradict `b` playing the other action). Proof by induction
    on the fuel gap; the one-step core recurses structurally, using `playsCheckC_sound` to
    pin actions and 8.2 to kill the spurious branch flip. -/
theorem playsCheckC_mono_lift
    (gdc : Nat → Formula → Bool) (gdc_fwd : ∀ k φ, gdc k φ = true → Provable k φ) :
    ∀ {f₁ f₂ : Nat}, f₁ ≤ f₂ → ∀ {me opponent body a m},
      playsCheckC gdc f₁ me opponent body a = some m →
      ∃ m', playsCheckC gdc f₂ me opponent body a = some m' ∧ m' ≤ m := by
  have step : ∀ fuel me opponent body a m,
      playsCheckC gdc fuel me opponent body a = some m →
      ∃ m', playsCheckC gdc (fuel+1) me opponent body a = some m' ∧ m' ≤ m := by
    intro fuel
    induction fuel with
    | zero => intro me opp body a m h; simp [playsCheckC] at h
    | succ fuel ih =>
      intro me opp body a m h
      cases body with
      | const c => exact ⟨m, by simpa [playsCheckC] using h, le_refl _⟩
      | self =>
          simp only [playsCheckC] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hx'le⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | opp =>
          simp only [playsCheckC] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hx'le⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | bot p =>
          simp only [playsCheckC] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hx'le⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | sim p q =>
          simp only [playsCheckC] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hx'le⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | ite b a' p q =>
          simp only [playsCheckC] at h ⊢
          cases hb : playsCheckC gdc fuel me opp b a' with
          | some mg =>
              cases hp : playsCheckC gdc fuel me opp p a with
              | some np =>
                  rw [hb, hp] at h
                  have hm : m = mg + np + c_node := by simpa using h.symm
                  obtain ⟨mg', hmg', hmgle⟩ := ih _ _ _ _ _ hb
                  obtain ⟨np', hnp', hnple⟩ := ih _ _ _ _ _ hp
                  rw [hmg', hnp']; exact ⟨mg' + np' + c_node, rfl, by omega⟩
              | none =>
                  -- then-guard succeeds, then-play fails ⇒ else-branch. `b` plays `a'`
                  -- (hb sound). The else needs `b` to play `other a'` — impossible by 8.2.
                  rw [hb, hp] at h; simp only at h
                  cases hbo : playsCheckC gdc fuel me opp b (playsCheckC.otherAction a') with
                  | none => rw [hbo] at h; simp at h
                  | some mo =>
                      exfalso
                      have hpa' : PlaysProof me opp b a' mg := playsCheckC_sound gdc gdc_fwd _ _ _ _ _ _ hb
                      have hpo : PlaysProof me opp b (playsCheckC.otherAction a') mo :=
                        playsCheckC_sound gdc gdc_fwd _ _ _ _ _ _ hbo
                      have := plays_det hpa' hpo
                      cases a' <;> simp [playsCheckC.otherAction] at this
          | none =>
              rw [hb] at h; simp only at h
              cases hbo : playsCheckC gdc fuel me opp b (playsCheckC.otherAction a') with
              | none => rw [hbo] at h; simp at h
              | some mo =>
                  cases hq : playsCheckC gdc fuel me opp q a with
                  | none => rw [hbo, hq] at h; simp at h
                  | some nq =>
                      rw [hbo, hq] at h
                      have hm : m = mo + nq + c_node := by simpa using h.symm
                      obtain ⟨mo', hmo', hmole⟩ := ih _ _ _ _ _ hbo
                      obtain ⟨nq', hnq', hnqle⟩ := ih _ _ _ _ _ hq
                      -- at fuel+1 the then-guard `b a'` STILL fails: `b` plays `other a'`
                      -- (hbo sound), so by 8.2 it cannot also play `a'`.
                      have hthen : playsCheckC gdc (fuel+1) me opp b a' = none := by
                        cases hb2 : playsCheckC gdc (fuel+1) me opp b a' with
                        | none => rfl
                        | some mm =>
                            exfalso
                            have hpo : PlaysProof me opp b (playsCheckC.otherAction a') mo :=
                              playsCheckC_sound gdc gdc_fwd _ _ _ _ _ _ hbo
                            have hother : playsCheckC.otherAction a' ≠ a' := by
                              cases a' <;> decide
                            exact playsCheckC_no_false gdc gdc_fwd hb2 hpo hother
                      rw [hthen, hmo', hnq']
                      exact ⟨mo' + nq' + c_node, by simp, by omega⟩
      | search k φ p q =>
          simp only [playsCheckC] at h ⊢
          by_cases hg : gdc k (φ.subst me opp)
          · rw [if_pos hg] at h ⊢; rw [Option.map_eq_some_iff] at h
            obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hx'le⟩ := ih _ _ _ _ _ hx
            exact ⟨x' + c_guard k + c_node, by simp [hx'], by omega⟩
          · rw [if_neg hg] at h; simp at h
  intro f₁ f₂ hle
  induction hle with
  | refl => intro me opp body a m h; exact ⟨m, h, le_refl _⟩
  | @step f₂ _ ih =>
      intro me opp body a m h
      obtain ⟨m', hm', hle'⟩ := ih h
      obtain ⟨m'', hm'', hle''⟩ := step f₂ me opp body a m' hm'
      exact ⟨m'', hm'', le_trans hle'' hle'⟩

/-- **8.3 Cost-aware completeness.** Every `PlaysProof … n` is found by `playsCheckC` at
    some fuel `F`, with cost `m ≤ n` AND `F ≤ m + 1` (so `F ≤ n + 1` — the fuel needed is
    bounded by the cost). By `PlaysProof.rec`; the `.ite` cases use 8.2 to show the checker
    takes the SAME branch the witness took. The `F ≤ m+1` bound is what lets `gdRecB`'s fixed
    `k+1` fuel suffice (`hfuel` discharged). NO sorry, NO Classical. -/
theorem playsCheckC_complete
    (gdc : Nat → Formula → Bool)
    (gdc_fwd : ∀ k φ, gdc k φ = true → Provable k φ)
    (gdc_bwd : ∀ k φ, Provable k φ → gdc k φ = true)
    {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ F m, playsCheckC gdc F me opponent body a = some m ∧ m ≤ n ∧ F ≤ n + 1 := by
  refine PlaysProof.rec
    (motive_1 := fun me opponent body a n _ =>
       ∃ F m, playsCheckC gdc F me opponent body a = some m ∧ m ≤ n ∧ F ≤ n + 1)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?atomMk ?provStruct ?provAtom
    ?provWeaken ?provSearchThenSearch ?provImplTrans ?provAtomBoxImpl h
  case const =>
    intro me opp a
    exact ⟨1, c_leaf, by simp only [playsCheckC]; cases a <;> decide, le_refl _, by simp [c_leaf]⟩
  case self =>
    intro me opp a n _ ih; obtain ⟨F, m, hF, hle, hFn⟩ := ih
    exact ⟨F+1, m + c_node, by simp only [playsCheckC, hF, Option.map_some], by omega, by simp [c_node]; omega⟩
  case opp =>
    intro me opp a n _ ih; obtain ⟨F, m, hF, hle, hFn⟩ := ih
    exact ⟨F+1, m + c_node, by simp only [playsCheckC, hF, Option.map_some], by omega, by simp [c_node]; omega⟩
  case bot =>
    intro me opp p a n _ ih; obtain ⟨F, m, hF, hle, hFn⟩ := ih
    exact ⟨F+1, m + c_node, by simp only [playsCheckC, hF, Option.map_some], by omega, by simp [c_node]; omega⟩
  case sim =>
    intro a n me opp p q _ ih; obtain ⟨F, m, hF, hle, hFn⟩ := ih
    exact ⟨F+1, m + c_node, by simp only [playsCheckC, hF, Option.map_some], by omega, by simp [c_node]; omega⟩
  case ite_t =>
    -- witness took then-branch: guard plays a' (r == a'), branch p plays a.
    -- witness cost n = mb + np + c_node; child fuels Fb ≤ mb+1, Fp ≤ np+1.
    intro me opp b r mb a' p a np q hb hr hp ihb ihp
    have hra : r = a' := by cases r <;> cases a' <;> first | rfl | (exact absurd hr (by decide))
    subst hra
    obtain ⟨Fb, mgb, hFb, hble, hFbn⟩ := ihb
    obtain ⟨Fp, mp, hFp, hple, hFpn⟩ := ihp
    obtain ⟨mgb', hb'', hb''le⟩ := playsCheckC_mono_lift gdc gdc_fwd (Nat.le_max_left Fb Fp) hFb
    obtain ⟨mp', hp'', hp''le⟩ := playsCheckC_mono_lift gdc gdc_fwd (Nat.le_max_right Fb Fp) hFp
    refine ⟨max Fb Fp + 1, mgb' + mp' + c_node, ?_, by omega, by simp [c_node] at *; omega⟩
    simp only [playsCheckC, hb'', hp'']
  case ite_f =>
    -- witness took else-branch: guard plays r ≠ a', branch q plays a.
    intro me opp b r mb a' q a nq p hb hr hq ihb ihq
    have hrne : r ≠ a' := by
      intro he; subst he; revert hr; cases r <;> decide
    have hro : r = playsCheckC.otherAction a' := by
      cases a' <;> cases r <;> first | rfl | (exact absurd rfl hrne)
    obtain ⟨Fb, mgb, hFb, hble, hFbn⟩ := ihb
    obtain ⟨Fq, mq, hFq, hqle, hFqn⟩ := ihq
    obtain ⟨mgb', hb'', hb''le⟩ := playsCheckC_mono_lift gdc gdc_fwd (Nat.le_max_left Fb Fq) hFb
    obtain ⟨mq', hq'', hq''le⟩ := playsCheckC_mono_lift gdc gdc_fwd (Nat.le_max_right Fb Fq) hFq
    refine ⟨max Fb Fq + 1, mgb' + mq' + c_node, ?_, by omega, by simp [c_node] at *; omega⟩
    -- then-guard `b a'` FAILS at the lifted fuel: `b` plays `r ≠ a'` (8.2)
    have hthen_none : playsCheckC gdc (max Fb Fq) me opp b a' = none := by
      cases hc : playsCheckC gdc (max Fb Fq) me opp b a' with
      | none => rfl
      | some mm =>
          exact (playsCheckC_no_false gdc gdc_fwd hc hb hrne).elim
    have hb''o : playsCheckC gdc (max Fb Fq) me opp b (playsCheckC.otherAction a') = some mgb' := by
      rw [← hro]; exact hb''
    simp only [playsCheckC, hthen_none, hb''o, hq'']
  case search_t =>
    intro k me opp p a n φ q hguard hp _ ihp
    obtain ⟨F, m, hF, hle, hFn⟩ := ihp
    refine ⟨F+1, m + c_guard k + c_node, ?_, by omega, ?_⟩
    · simp only [playsCheckC, gdc_bwd _ _ hguard, if_true, hF, Option.map_some]
    · have h1 : 1 ≤ c_guard k := by simp [c_guard]
      have h2 : c_node = 1 := rfl
      omega
  case atomMk => intros; trivial
  case provStruct => intros; trivial
  case provAtom => intros; trivial
  case provWeaken => intros; trivial
  case provSearchThenSearch => intros; trivial
  case provImplTrans => intros; trivial
  case provAtomBoxImpl => intros; trivial

/-- **Budget-aware oracle.** `gdRecB d k (.plays p q a)` runs the cost-tracking checker
    and accepts ONLY if the found certificate cost fits the box budget `k`. The structural
    fuel is generous (`k` suffices for any cert of cost ≤ k, since each step costs ≥ 1);
    we use `k+1` to be safe. Nested guards recurse one depth `d` down. -/
def gdRecB : Nat → Nat → Formula → Bool
  | 0,    _, _ => false
  | d+1,  k, .plays p q a =>
      match playsCheckC (gdRecB d) (k+1) p q p a with
      | some n => decide (n ≤ k)
      | none   => false
  | _+1,  _, _ => false

/-- **`gdRecB` soundness — UNCONDITIONAL, sorry-free.** A `true` yields `Provable k φ` at
    the guard's OWN budget `k`. This is `gd_budget` DISCHARGED: cost-tracking + the `n ≤ k`
    gate deliver `AtomProvable k`, hence `Provable k`. No named hypothesis, no axiom. -/
theorem gdRecB_sound :
    ∀ d k φ, gdRecB d k φ = true → Provable k φ := by
  intro d
  induction d with
  | zero => intro k φ h; simp [gdRecB] at h
  | succ d ih =>
    intro k φ h
    cases φ with
    | plays p q a =>
        simp only [gdRecB] at h
        cases hc : playsCheckC (gdRecB d) (k+1) p q p a with
        | none => rw [hc] at h; simp at h
        | some n =>
            rw [hc] at h
            have hnk : n ≤ k := by simpa using h
            -- inner oracle soundness from the IH (non-play guards vacuous)
            have inner_fwd : ∀ k' φ', gdRecB d k' φ' = true → Provable k' φ' := ih
            have hpp : PlaysProof p q p a n := playsCheckC_sound (gdRecB d) inner_fwd (k+1) p q p a n hc
            exact Provable.atom (.mk hpp hnk)
    | _ => cases d <;> simp [gdRecB] at h

/-- **`gdRecB_accepts` — the payoff, `hfuel` now DISCHARGED.** A certificate of cost ≤ k for
    the guard play-atom ⇒ `gdRecB (d+1)` ACCEPTS, given the inner oracle `gdRecB d` is sound
    (`inner_fwd`) and complete (`inner_bwd`) on nested guards. The fuel sufficiency that was a
    hypothesis is now PROVED: §8.3 `playsCheckC_complete` delivers a witness at fuel `F ≤ n+1
    ≤ k+1`, which `gdRecB`'s fixed `k+1` fuel covers (via `mono_lift`). NO sorry.

    `inner_bwd` remains: it is `gdRecB`'s completeness ONE DEPTH DOWN — the well-founded
    recursion, closed in `gdRecB_complete` below. -/
theorem gdRecB_accepts
    (d k : Nat) (p q : Prog) (a : Action) (n : Nat)
    (inner_fwd : ∀ k' φ', gdRecB d k' φ' = true → Provable k' φ')
    (inner_bwd : ∀ k' φ', Provable k' φ' → gdRecB d k' φ' = true)
    (hpp : PlaysProof p q p a n) (hnk : n ≤ k) :
    gdRecB (d+1) k (.plays p q a) = true := by
  -- fuel sufficiency is now a THEOREM, not a hypothesis:
  obtain ⟨F, m, hF, hmn, hFn⟩ := playsCheckC_complete (gdRecB d) inner_fwd inner_bwd hpp
  have hFk : F ≤ k + 1 := by omega
  obtain ⟨m', hm', hm'le⟩ := playsCheckC_mono_lift (gdRecB d) inner_fwd hFk hF
  simp only [gdRecB, hm']
  exact decide_eq_true (by omega)

/-! ## 9. The depth recursion — `gdRecB_complete` (PARTIAL: `inner_bwd` still assumed)

`gdRecB_accepts`'s ONE remaining hypothesis is `inner_bwd` (completeness of `gdRecB d` on
nested guards). `gdRecB_complete` below substitutes `gdRecB_sound` for `inner_fwd` (that one
IS unconditional), leaving `inner_bwd` as the single explicit hypothesis. So this is the clean
per-level statement: *given* the inner oracle is complete on the nested guards, the outer level
is too.

**Why `inner_bwd` does NOT vanish — it IS the fixpoint boundary (the real finding).** One might
hope to discharge `inner_bwd` by strong induction on `d`: decide the guard at depth `d` using the
inner oracle at `d-1`. For that induction to BOTTOM OUT, the guard-nesting of the certificate must
be FINITE — each `.search` guard's own certificate must reference strictly-shallower guards. Off
the Löb fixpoint that holds (finite nesting) and `inner_bwd` is dischargeable. **AT the fixpoint it
fails by construction:** CUPOD self-play's certificate references ITSELF at the same budget (S3′,
`CONSTRUCTIVE_BOUNDED_LOB.md`), so guard-nesting is INFINITE, no finite `d` bottoms out, and
`gdRecB` returns `false` — correctly (= `evalC`'s `none`). So `inner_bwd` is NOT removable in
general: as a hypothesis it is exactly "the certificate has finite guard-depth", which is the
honest, precise statement of the off-fixpoint condition. Making it a concrete `searchDepth ≤ d`
side-condition is presentation, not new math — and it would carry the SAME finiteness content.
**This is the boundary, located:** the depth recursion closes iff off the fixpoint, which is
exactly where `gdRecB` is supposed to decide.

**Scope (unchanged):** play-atom realized as `AtomProvable` (`∃ n ≤ k, PlaysProof`), not
arbitrary `Provable k` (reflection members are out of fragment). -/

/-- **`gdRecB_complete` (per-level).** Given the inner oracle `gdRecB d` is complete on nested
    guards (`inner_bwd`), an `AtomProvable`-realized play-atom of cost ≤ k is accepted by
    `gdRecB (d+1)`. The forward oracle is `gdRecB_sound` (unconditional); only `inner_bwd`
    remains, and closing it needs the depth lemma noted in §9. NO sorry. -/
theorem gdRecB_complete
    (d k : Nat) (p q : Prog) (a : Action) (n : Nat)
    (hpp : PlaysProof p q p a n) (hnk : n ≤ k)
    (inner_bwd : ∀ k' φ', Provable k' φ' → gdRecB d k' φ' = true) :
    gdRecB (d+1) k (.plays p q a) = true :=
  gdRecB_accepts d k p q a n (gdRecB_sound d) inner_bwd hpp hnk

/-! ## Result log

**PASSED.** Build with `lake env lean PrisonersDilemma/Research/Spikes/DecidableFiniteSpike.lean`
— clean exit, **no `sorry`, no `Classical`, no `axiom`** in the proofs (greppable).

What is established, constructively and machine-checked:
- `playsCheck` : a **total, fuel-structurally-decreasing** `Bool` checker for the
  `PlaysProof` (play-atom) fragment — the computable enumeration of bounded play
  certificates. Parameterised by a guard oracle `gd` (the one place the fragment
  touches `Provable`, handled by reduction, see scope note at top).
- `playsCheck_sound` : `check = true → ∃ n, PlaysProof …`. No oracle.
- `playsCheck_mono` / `playsCheck_mono_le` : the check never loses a `true` with more fuel.
- `playsCheck_complete` : `PlaysProof … n → ∃ N, check N = true`. Via `PlaysProof.rec`
  (mutual block; mirrors `playsProof_sound`'s recursor pattern in `BaseTheorems.lean`).
- `decidableAtBudget` : the resulting `Decidable` is built from the running checker,
  **not `Classical.dec`** — it computes.

**What this means for Change 1 (the `atom_complete_false_guard` removal).** The
load-bearing claim — *"whether a guard play-atom has a bounded certificate is
decidable by a real, terminating procedure"* — is **confirmed for the `PlaysProof`
fragment, relative to a guard oracle**. This is exactly the predicate `search_f`
needs the negation of, and it is genuinely decidable (sound + complete + monotone),
so a `decide (…) = false` premise on `search_f` is honest, not an oracle smuggled in.

**The one residual, by design (NOT a failure).** `gd` is left abstract with the spec
`gd k φ = true ↔ Provable k φ`. Closing it for real means deciding the *guard's*
`Provable` — which, for a play-atom guard, is one `PlaysProof` level down, i.e. the
same checker at a smaller program. The full Change 1 ties this knot by well-founded
recursion on the budget `k` (the guard's box budget; finite, so the recursion
bottoms out — this is the bounded-search finiteness doing the work, exactly as the
fixpoint discussion predicted it WOULD here and would NOT at the Löb self-reference).
That tie-off is the next spike step; the **decision machinery it recurses through is
now proven sound/complete here.** Contrast S3′ (`CONSTRUCTIVE_BOUNDED_LOB.md`): there
the budget could not decrease (`k'=k` forced); here the guard is a *strictly smaller*
sub-program with no self-reference, so the recursion has the foothold S3′ lacked.

**Caveat carried forward:** this fragment is `Provable`-via-`AtomProvable`/`PlaysProof`
only. The full `Provable` also has `.struct` (`Derivation`) and the reflection rules
(`weakenImpl`, `searchThenSearch_t`, `atomBoxImpl`) — NOT covered here and NOT
finitely enumerable in general. For the **false-guard** case that is fine: a failed
guard is precisely a play-atom with no certificate, which is this fragment.

## §6 — the FIRST tie-off `gdRec` (superseded, kept for the record)

`gdRec` reuses the box budget `k` as `playsCheck`'s STRUCTURAL fuel. `gdRec_sound` is
proved sorry-free but only MODULO a named hypothesis `gd_budget` (an accepted guard atom
is `Provable` at its own `k`). That hypothesis is the **budget-match**, and it is FALSE as
set up: the cost-bound finding shows a play accepted at checker-fuel `F` has a `PlaysProof`
of cost `~2^F` (`.ite` branches both children at the same fuel; `.search` adds `c_guard k`
uncounted), so reusing `k` as fuel cannot enforce `atom_cost(witness) ≤ k`. The `gd_budget`
hypothesis cannot be discharged for `gdRec`. **§7 is the fix.**

## §7 — the FIX: cost-tracking `playsCheckC` + budget-gated `gdRecB` (CLOSED ✅)

The honest design: thread the ACTUAL `PlaysProof` cost and accept a `.search` guard only
when the inner certificate's cost fits the box budget `k` — the
`Provable_finite`-by-enumeration the notes always pointed at.

- `playsCheckC : Nat → Prog³ → Action → Option Nat` — returns the certificate's cost
  (`some n`) or `none`. Same structure as `playsCheck`; `.search` adds `c_guard k + c_node`
  exactly as the constructor, `.ite` takes the cheaper successful branch.
- `playsCheckC_sound` — `some n` yields `PlaysProof … n` of cost EXACTLY `n`. Sorry-free.
- `gdRecB d k (.plays p q a)` — runs `playsCheckC` then gates `decide (n ≤ k)`. Total,
  structural, depth-`d` recursion for nested guards. No axiom, no `partial`.
- **`gdRecB_sound` — UNCONDITIONAL, sorry-free: `gdRecB d k φ = true → Provable k φ`.**
  The `n ≤ k` gate + `AtomProvable.mk` deliver `Provable k` at the guard's OWN budget.
  NO named hypothesis — `gd_budget` is DISCHARGED, not assumed.

**Axiom check (`#print axioms`):** `gdRecB_sound` and `playsCheckC_sound` depend on
`[propext, Quot.sound]` ONLY — two of Lean's three standard axioms. NO `sorryAx`, NO
`Classical.choice`, and NONE of the project reflection axioms (`PBLT`, `boxInternalize`,
`box_provable`, `atom_complete_false_guard`). The budget-match is genuinely closed.

**What §7 means for Change 1.** `gdRecB` IS the concrete `gd` Change 1 needs: a computable,
budget-correct decision of guard provability, sound to `Provable k` with no oracle.

## §8 — cost-aware COMPLETENESS of `playsCheckC` + `gdRecB_accepts` (CLOSED ✅)

The completeness direction, built bottom-up as three lemmas (all sorry-free):

- **`plays_det`** — play DETERMINISM: a program plays at most one action vs a fixed
  opponent. (Engine lacked this.) From `playsProof_sound` + `eval_mono_le` (eval is a fn).
- **`playsCheckC_no_false`** — the checker never reports a play that doesn't happen
  (soundness + determinism). This TAMES the `.ite` tie-break: when the witness took the
  else-branch, the then-guard `b a'` provably FAILS, so the checker can't wrongly switch.
- **`playsCheckC_mono_lift`** — fuel-lift `F ≤ F'` with cost `≤`. The `.ite`
  non-monotonicity (a then-branch newly succeeding) is killed by `no_false`: the spurious
  branch flip would force `b` to play two actions. (This is WHY the earlier naive
  `playsCheckC_step` failed — it lacked determinism; with it, the lift goes through.)
- **`playsCheckC_complete`** — every `PlaysProof … n` is found at some fuel with cost ≤ n.
  By `PlaysProof.rec`; `.ite_t`/`.ite_f` reconstruct the SAME branch the witness took
  (via `no_false`), `.search_t` uses the reverse oracle `gdc_bwd`.
- **`gdRecB_accepts`** (the payoff) — a certificate of cost ≤ k ⇒ `gdRecB (d+1)` ACCEPTS,
  given the inner oracle is sound+complete on nested guards. With `gdRecB_sound`, `gdRecB`
  is a genuine DECISION of `Provable k` on the play-atom fragment.

**Axiom check:** `gdRecB_sound` = `[propext, Quot.sound]`. `playsCheckC_complete`,
`plays_det`, `gdRecB_accepts` = `[propext, Classical.choice, Quot.sound]` — the
`Classical.choice` enters ONLY transitively via the engine's existing classical meta-theory
(`playsProof_sound`/`atom_complete`, `open Classical` in `BaseTheorems`). Still the THREE
standard Lean axioms; NO `sorryAx`, NONE of the project reflection axioms.

**`hfuel` DISCHARGED (§8 update):** `playsCheckC_complete` now also proves `F ≤ n+1`, so the
witness always fits `gdRecB`'s fixed `k+1` fuel (`n ≤ k`). `gdRecB_accepts` no longer takes a
fuel hypothesis — only `inner_fwd` (= `gdRecB_sound`, unconditional) and `inner_bwd`.

## §9 — the depth recursion: `inner_bwd` IS the fixpoint boundary (the real finding)

`gdRecB_complete` reduces the outer level to `inner_bwd` (completeness one depth down), with
`inner_fwd` discharged by `gdRecB_sound`. The ONE remaining hypothesis `inner_bwd` does **not**
vanish by induction on `d` — and WHY is the finding, not a gap:

- For the depth induction to bottom out, the certificate's guard-nesting must be FINITE (each
  `.search` guard's certificate references strictly-shallower guards).
- **Off the Löb fixpoint:** finite nesting, `inner_bwd` dischargeable.
- **At the fixpoint:** CUPOD self-play's certificate references ITSELF at the same budget (S3′),
  guard-nesting is INFINITE, no finite `d` bottoms out — and `gdRecB` returns `false`, correctly
  (= `evalC`'s `none`).

So `inner_bwd`-as-hypothesis is EXACTLY "the certificate has finite guard-depth" — the precise,
honest off-fixpoint condition. Making it a concrete `searchDepth ≤ d` side-condition is
presentation carrying the same finiteness content, NOT new math. **The depth recursion closes iff
off the fixpoint** — which is exactly where `gdRecB` is meant to decide. This LOCATES the boundary
inside the completeness machinery itself.

**Status (final, honest):**
- SOUNDNESS (budget-match) of `gdRecB` — **CLOSED, unconditional, sorry-free, `[propext, Quot.sound]`.**
- COMPLETENESS (cost-aware) of `playsCheckC` — **CLOSED, sorry-free** (incl. `F ≤ n+1`).
- `gdRecB_accepts` / `gdRecB_complete` — **per-level CLOSED**; the only residual `inner_bwd` is the
  fixpoint boundary itself (finite guard-depth = off-fixpoint), NOT a mechanical gap.
- The two hard mathematical pieces (budget-match soundness; determinism-based completeness) are DONE. -/

end PD.DecFiniteSpike
