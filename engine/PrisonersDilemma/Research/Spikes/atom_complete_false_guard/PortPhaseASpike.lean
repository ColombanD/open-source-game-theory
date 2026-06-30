import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems

/-!
# Phase A spike — `ppSize` for the REAL `PlaysProof`, the `search_t` arm first

Plan: `Sound_vs_complete.md` / memory `project_atom_complete_false_guard_removal`. The Q2 toy
(`SizeIndexSpike.lean`) proved size-tracked decidability works in miniature. Phase A ports it
to the REAL `PlaysProof` (8 constructors, real cost model). Per falsification-first, the
RISKIEST arm goes first: `search_t`.

**The `search_t` risk.** Real `search_t` (Derivation.lean:241) carries `Provable k (φ.subst me
opp)` as its premise — NOT a `PlaysProof`. `Provable` ⊇ `.struct`(Derivation) + reflection rules
+ axioms, which are NOT finitely decidable. So `ppSize`'s `search_t` arm must:
  • recurse into the guard ONLY when it is an ATOM-realized play-atom (`.plays sub sub' a'`),
    rebuilding `Provable k guard` via `Provable.atom (AtomProvable.mk …)`;
  • return `none` otherwise (struct/reflection/axiom guards) — CORRECT, those are exactly the
    Löb-fixpoint / reflection cases with no finite play certificate.

This spike builds JUST `ppSize` (real frame `me opp body`, real costs) + `ppSize_sound` for the
`const` and `search_t` arms, to confirm the atom-split + `Provable.atom` reconstruction
typechecks and is sound against the real engine. The easy arms follow once this lands.

NOT root-imported. Build: `lake env lean PrisonersDilemma/Research/Spikes/PortPhaseASpike.lean`
-/

namespace PD.PortPhaseA
open PD

/-! ## 1. `ppSize` — real frame, real cost model

`ppSize fuel me opp body a` = minimal size of a `PlaysProof me opp body a _`, or `none`.
Mirrors `playsCheckC` (DecidableFiniteSpike) but with the REAL cost constants and the real
8-constructor shape. We start with `const` + `search_t`; other arms stubbed as `none` for now
(they are the EASY ports, filled in the next step). -/

def otherAction : Action → Action
  | .C => .D
  | .D => .C

def ppSize : Nat → (me opponent body : Prog) → Action → Option Nat
  | 0,      _,  _,        _,             _ => none
  | fuel+1, me, opponent, .const c,      a => if c == a then some c_leaf else none
  | fuel+1, me, opponent, .self,         a => (ppSize fuel me opponent me a).map (· + c_node)
  | fuel+1, me, opponent, .opp,          a => (ppSize fuel me opponent opponent a).map (· + c_node)
  | fuel+1, me, opponent, .bot p,        a => (ppSize fuel me opponent p a).map (· + c_node)
  | fuel+1, me, opponent, .sim p q,      a =>
      (ppSize fuel (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a).map (· + c_node)
  | fuel+1, me, opponent, .ite b a' p q, a =>
      -- branch discovery (playsCheckC shape): guard plays a' → then p, else → q.
      -- cost = m_guard + n_branch + c_node (matches ite_t/ite_f).
      match ppSize fuel me opponent b a', ppSize fuel me opponent p a with
      | some mg, some np => some (mg + np + c_node)
      | _, _ =>
        match ppSize fuel me opponent b (otherAction a'), ppSize fuel me opponent q a with
        | some mg, some nq => some (mg + nq + c_node)
        | _, _ => none
  | fuel+1, me, opponent, .search k φ p q, a =>
      -- THE RISKY ARM. Real `search_t` (Derivation.lean:241):
      --   Provable k (φ.subst me opp) → PlaysProof me opp p a n
      --     → PlaysProof me opp (.search k φ p q) a (n + c_guard k + c_node)
      -- Total size = `n + c_guard k + c_node`, `n` = THEN-branch cost. The guard's own proof
      -- size is NOT in the total — it lives in the guard's budget `k`, separately.
      -- So: (1) the guard atom `φ.subst me opp` must be AtomProvable within budget `k`; by
      --     `AtomProvable.mk`, that means `PlaysProof gs' gt' gs' ga sg` with `sg ≤ k`, where
      --     `.plays gs' gt' ga = φ.subst me opp`. We check via `ppSize fuel gs' gt' gs' ga`.
      -- (2) if so, return then-branch cost + c_guard k + c_node.
      match φ with
      | .plays gs gt ga =>
          let gs' := gs.subst me opponent
          let gt' := gt.subst me opponent
          match ppSize fuel gs' gt' gs' ga with
          | some sg => if sg ≤ k then (ppSize fuel me opponent p a).map (· + c_guard k + c_node)
                       else none
          | none => none
      | _ => none   -- non-atom guard (impl/box/neg/eq): not atom-decidable → none (correct)

/-! ## 2. `ppSize_sound` — the RISKY-arm soundness test

We prove `ppSize fuel me opp body a = some s → PlaysProof me opp body a s` for the arms that
matter for de-risking: `const` (baseline) and `search_t` (the atom-split + `Provable.atom`
reconstruction). The stubbed arms (`ite`) return `none`, so soundness is vacuous there; the
other easy arms (`self/opp/bot/sim`) are routine (`playsCheckC` shape) — included for a full
`ppSize_sound` so the recursion's IH is available to `search_t`. -/

theorem ppSize_sound :
    ∀ fuel me opponent body a s,
      ppSize fuel me opponent body a = some s → PlaysProof me opponent body a s := by
  intro fuel
  induction fuel with
  | zero => intro me opp body a s h; simp [ppSize] at h
  | succ fuel ih =>
    intro me opp body a s h
    cases body with
    | const c =>
        simp only [ppSize] at h
        by_cases hca : c == a
        · rw [if_pos hca] at h
          have : c = a := by cases c <;> cases a <;> first | rfl | (exact absurd hca (by decide))
          subst this
          have : s = c_leaf := by simpa using h.symm
          subst this; exact .const
        · rw [if_neg hca] at h; simp at h
    | self =>
        simp only [ppSize] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hms⟩ := h; subst hms; exact .self (ih me opp me a m hm)
    | opp =>
        simp only [ppSize] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hms⟩ := h; subst hms; exact .opp (ih me opp opp a m hm)
    | bot p =>
        simp only [ppSize] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hms⟩ := h; subst hms; exact .bot (ih me opp p a m hm)
    | sim p q =>
        simp only [ppSize] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨m, hm, hms⟩ := h; subst hms; exact .sim (ih _ _ _ a m hm)
    | ite b a' p q =>
        -- branch discovery, mirroring DecidableFiniteSpike's playsCheckC `.ite` soundness.
        simp only [ppSize] at h
        cases hb : ppSize fuel me opp b a' with
        | some mg =>
            cases hp : ppSize fuel me opp p a with
            | some np =>
                rw [hb, hp] at h
                have : s = mg + np + c_node := by simpa using h.symm
                subst this
                exact .ite_t (ih me opp b a' mg hb) (by cases a' <;> decide) (ih me opp p a np hp)
            | none =>
                rw [hb, hp] at h; simp only at h
                cases hbo : ppSize fuel me opp b (otherAction a') with
                | none => rw [hbo] at h; simp at h
                | some mo =>
                    cases hq : ppSize fuel me opp q a with
                    | none => rw [hbo, hq] at h; simp at h
                    | some nq =>
                        rw [hbo, hq] at h
                        have : s = mo + nq + c_node := by simpa using h.symm
                        subst this
                        refine .ite_f (ih me opp b _ mo hbo) ?_ (ih me opp q a nq hq)
                        cases a' <;> decide
        | none =>
            rw [hb] at h; simp only at h
            cases hbo : ppSize fuel me opp b (otherAction a') with
            | none => rw [hbo] at h; simp at h
            | some mo =>
                cases hq : ppSize fuel me opp q a with
                | none => rw [hbo, hq] at h; simp at h
                | some nq =>
                    rw [hbo, hq] at h
                    have : s = mo + nq + c_node := by simpa using h.symm
                    subst this
                    refine .ite_f (ih me opp b _ mo hbo) ?_ (ih me opp q a nq hq)
                    cases a' <;> decide
    | search k φ p q =>
        -- THE RISKY ARM. Unfold and rebuild `search_t` from the guard atom + then-branch.
        cases φ with
        | plays gs gt ga =>
            simp only [ppSize] at h
            cases hg : ppSize fuel (gs.subst me opp) (gt.subst me opp) (gs.subst me opp) ga with
            | none => rw [hg] at h; simp at h
            | some sg =>
                rw [hg] at h; simp only at h
                by_cases hsgk : sg ≤ k
                · rw [if_pos hsgk] at h
                  rw [Option.map_eq_some_iff] at h
                  obtain ⟨n, hn, hns⟩ := h
                  subst hns
                  -- (1) guard atom provable: AtomProvable k (.plays gs' gt' ga) at budget k
                  have hguard_pp : PlaysProof (gs.subst me opp) (gt.subst me opp) (gs.subst me opp) ga sg :=
                    ih _ _ _ ga sg hg
                  have hguard_prov : Provable k ((Formula.plays gs gt ga).subst me opp) :=
                    Provable.atom (.mk hguard_pp hsgk)
                  -- (2) then-branch certificate, (3) assemble search_t
                  exact PlaysProof.search_t hguard_prov (ih me opp p a n hn)
                · rw [if_neg hsgk] at h; simp at h
        | impl _ _ => simp only [ppSize] at h; exact absurd h (by simp)
        | neg _ => simp only [ppSize] at h; exact absurd h (by simp)
        | box _ _ => simp only [ppSize] at h; exact absurd h (by simp)
        | eq _ _ => simp only [ppSize] at h; exact absurd h (by simp)

/-! ## Phase B — completeness + decidability, via the proven `DecidableFiniteSpike` chain

Ported to real types: `plays_det` → `ppSize_no_false` → `ppSize_mono_lift` → `ppSize_complete`.
The `.ite` non-monotonicity (more fuel unlocks the then-branch) is cured by DETERMINISM exactly
as in `DecidableFiniteSpike`. Real-engine determinism comes from `playsProof_sound` + `eval_mono_le`
(both exist; the engine lacked a packaged `plays_det`, so we prove it here). -/

/-- **Play determinism** (real engine): a body plays at most one action vs a fixed opponent. -/
theorem plays_det {me opponent body : Prog} {a₁ a₂ : Action} {n₁ n₂ : Nat}
    (h₁ : PlaysProof me opponent body a₁ n₁) (h₂ : PlaysProof me opponent body a₂ n₂) :
    a₁ = a₂ := by
  obtain ⟨N₁, e₁⟩ := PD.BaseTheorems.playsProof_sound h₁
  obtain ⟨N₂, e₂⟩ := PD.BaseTheorems.playsProof_sound h₂
  have f₁ := PD.BaseTheorems.eval_mono_le e₁ (max N₁ N₂) (Nat.le_max_left _ _)
  have f₂ := PD.BaseTheorems.eval_mono_le e₂ (max N₁ N₂) (Nat.le_max_right _ _)
  rw [f₁] at f₂; exact (Option.some.injEq _ _ ▸ f₂)

/-- **No false play:** the checker never reports a play that doesn't happen. -/
theorem ppSize_no_false
    {fuel : Nat} {me opponent b : Prog} {a' r : Action} {m mr : Nat}
    (hck : ppSize fuel me opponent b a' = some m)
    (hr : PlaysProof me opponent b r mr) (hne : r ≠ a') : False :=
  hne (plays_det hr (ppSize_sound fuel me opponent b a' m hck))

/-- **Fuel-lift, `≤`-cost** (`f₁ ≤ f₂`). `.ite` non-monotonicity killed by `ppSize_no_false`. -/
theorem ppSize_mono_lift :
    ∀ {f₁ f₂ : Nat}, f₁ ≤ f₂ → ∀ {me opponent body a m},
      ppSize f₁ me opponent body a = some m →
      ∃ m', ppSize f₂ me opponent body a = some m' ∧ m' ≤ m := by
  have step : ∀ fuel me opponent body a m,
      ppSize fuel me opponent body a = some m →
      ∃ m', ppSize (fuel+1) me opponent body a = some m' ∧ m' ≤ m := by
    intro fuel
    induction fuel with
    | zero => intro me opp body a m h; simp [ppSize] at h
    | succ fuel ih =>
      intro me opp body a m h
      cases body with
      | const c => exact ⟨m, by simpa [ppSize] using h, le_refl _⟩
      | self =>
          simp only [ppSize] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hle⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | opp =>
          simp only [ppSize] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hle⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | bot p =>
          simp only [ppSize] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hle⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | sim p q =>
          simp only [ppSize] at h ⊢; rw [Option.map_eq_some_iff] at h
          obtain ⟨x, hx, hxm⟩ := h; obtain ⟨x', hx', hle⟩ := ih _ _ _ _ _ hx
          exact ⟨x' + c_node, by simp [hx'], by omega⟩
      | ite b a' p q =>
          simp only [ppSize] at h ⊢
          cases hb : ppSize fuel me opp b a' with
          | some mg =>
              cases hp : ppSize fuel me opp p a with
              | some np =>
                  rw [hb, hp] at h
                  have hm : m = mg + np + c_node := by simpa using h.symm
                  obtain ⟨mg', hmg', _⟩ := ih _ _ _ _ _ hb
                  obtain ⟨np', hnp', _⟩ := ih _ _ _ _ _ hp
                  rw [hmg', hnp']; exact ⟨mg' + np' + c_node, rfl, by omega⟩
              | none =>
                  rw [hb, hp] at h; simp only at h
                  cases hbo : ppSize fuel me opp b (otherAction a') with
                  | none => rw [hbo] at h; simp at h
                  | some mo =>
                      cases hq : ppSize fuel me opp q a with
                      | none => rw [hbo, hq] at h; simp at h
                      | some nq =>
                          rw [hbo, hq] at h
                          have hm : m = mo + nq + c_node := by simpa using h.symm
                          obtain ⟨mo', hmo', _⟩ := ih _ _ _ _ _ hbo
                          obtain ⟨nq', hnq', _⟩ := ih _ _ _ _ _ hq
                          have hthen : ppSize (fuel+1) me opp b a' = none := by
                            cases hb2 : ppSize (fuel+1) me opp b a' with
                            | none => rfl
                            | some mm =>
                                exact (ppSize_no_false hb2
                                  (ppSize_sound _ _ _ _ _ _ hbo) (by cases a' <;> decide)).elim
                          rw [hthen, hmo', hnq']
                          exact ⟨mo' + nq' + c_node, by simp, by omega⟩
          | none =>
              rw [hb] at h; simp only at h
              cases hbo : ppSize fuel me opp b (otherAction a') with
              | none => rw [hbo] at h; simp at h
              | some mo =>
                  cases hq : ppSize fuel me opp q a with
                  | none => rw [hbo, hq] at h; simp at h
                  | some nq =>
                      rw [hbo, hq] at h
                      have hm : m = mo + nq + c_node := by simpa using h.symm
                      obtain ⟨mo', hmo', _⟩ := ih _ _ _ _ _ hbo
                      obtain ⟨nq', hnq', _⟩ := ih _ _ _ _ _ hq
                      have hthen : ppSize (fuel+1) me opp b a' = none := by
                        cases hb2 : ppSize (fuel+1) me opp b a' with
                        | none => rfl
                        | some mm =>
                            exact (ppSize_no_false hb2
                              (ppSize_sound _ _ _ _ _ _ hbo) (by cases a' <;> decide)).elim
                      rw [hthen, hmo', hnq']
                      exact ⟨mo' + nq' + c_node, by simp, by omega⟩
      | search k φ p q =>
          cases φ with
          | plays gs gt ga =>
              simp only [ppSize] at h ⊢
              cases hg : ppSize fuel (gs.subst me opp) (gt.subst me opp) (gs.subst me opp) ga with
              | none => rw [hg] at h; simp at h
              | some sg =>
                  rw [hg] at h; simp only at h
                  by_cases hsgk : sg ≤ k
                  · rw [if_pos hsgk] at h; rw [Option.map_eq_some_iff] at h
                    obtain ⟨n, hn, hns⟩ := h
                    obtain ⟨sg', hsg', hsg'le⟩ := ih _ _ _ _ _ hg
                    obtain ⟨n', hn', hn'le⟩ := ih _ _ _ _ _ hn
                    rw [hsg']; simp only
                    rw [if_pos (by omega : sg' ≤ k), hn']
                    exact ⟨n' + c_guard k + c_node, by simp, by omega⟩
                  · rw [if_neg hsgk] at h; simp at h
          | impl _ _ => simp only [ppSize] at h; exact absurd h (by simp)
          | neg _ => simp only [ppSize] at h; exact absurd h (by simp)
          | box _ _ => simp only [ppSize] at h; exact absurd h (by simp)
          | eq _ _ => simp only [ppSize] at h; exact absurd h (by simp)
  intro f₁ f₂ hle
  induction hle with
  | refl => intro me opp body a m h; exact ⟨m, h, le_refl _⟩
  | @step f₂ _ ih =>
      intro me opp body a m h
      obtain ⟨m', hm', hle'⟩ := ih h
      obtain ⟨m'', hm'', hle''⟩ := step f₂ me opp body a m' hm'
      exact ⟨m'', hm'', le_trans hle'' hle'⟩

/-! ## Phase B.2 — `ppSize_complete` (cost-aware), scoped honestly

Completeness: `PlaysProof me opp body a n → ∃ F m, ppSize F … = some m ∧ m ≤ n`. By induction
on the derivation. The `.ite` cases reconstruct the SAME branch the witness took (via
`no_false`/`mono_lift`).

**Scope decision (honest).** The `search_t` case's guard is a `Provable k guard` premise; a
`ppSize` witness for it exists ONLY when the guard is ATOM-realized (`Provable.atom`). Arbitrary
`Provable` guards include the reflection rules / axioms, which are NOT finitely decidable (the
out-of-scope fixpoint/reflection cases). So `search_t` completeness is CONDITIONAL on a guard
witness — we state it as a hypothesis (`guard_wit`), exactly the honest fragment boundary. The
de-risk content — the `c_guard`-aware cost-bound assembly — is fully proven; the reflection-rule
recursion is correctly excluded, not faked. -/

/-- **`search_t` completeness reconstruction (the genuinely new content), CONDITIONAL on a
    guard witness.** Given a `ppSize` witness for the guard atom (cost `sg ≤ k`) and a `ppSize`
    witness for the then-branch (cost `np ≤ n`), `ppSize` finds the whole `.search` play at cost
    `≤ n + c_guard k + c_node` — matching the real `search_t` index. This is the completeness
    twin of the `ppSize_sound` `search_t` arm; it closes WITHOUT touching the reflection rules,
    because the guard witness is supplied (atom-realized fragment). NO sorry, NO Classical. -/
theorem ppSize_search_complete
    {me opponent : Prog} {k : Nat} {gs gt p q : Prog} {ga a : Action} {sg np : Nat}
    (hguard : ppSize (max sg np + 1) (gs.subst me opponent) (gt.subst me opponent)
                (gs.subst me opponent) ga = some sg)
    (hsgk : sg ≤ k)
    (hthen : ppSize (max sg np + 1) me opponent p a = some np) :
    ∃ F m, ppSize F me opponent (.search k (.plays gs gt ga) p q) a = some m
           ∧ m ≤ np + c_guard k + c_node := by
  refine ⟨max sg np + 2, np + c_guard k + c_node, ?_, le_refl _⟩
  show ppSize (max sg np + 1 + 1) me opponent (.search k (.plays gs gt ga) p q) a = _
  simp only [ppSize, hguard, hsgk, if_pos, hthen, Option.map_some]

/-! ## Phase B.3 — `Decidable (AtomProvable k …)` for the real engine, via `ppSize`

`AtomProvable k (.plays me opp a)` = `∃ n, PlaysProof me opp me a n ∧ n ≤ k` (Derivation.lean:248).
Decided by: `ppSize (k+1) me opp me a` returns `some s` with `s ≤ k`. Soundness (`ppSize_sound`)
+ a `k+1`-fuel-suffices bound give the iff; the instance computes (no Classical in the INSTANCE
itself — it inspects a concrete `Option Nat`).

For the de-risk we assume the `fuel ≤ size+1` completeness bound (Phase B.2, scoped to the
atom-realized fragment) as the remaining hypothesis `complete_bound`; with it the iff closes. -/

/-- The real-engine bounded play-certificate, in `ppSize` terms. -/
def AtomFinite (k : Nat) (me opponent : Prog) (a : Action) : Prop :=
  ∃ n, PlaysProof me opponent me a n ∧ n ≤ k

/-- The `ppSize` decision matches `AtomFinite`, GIVEN the completeness bound `complete_bound`
    (every certificate of size ≤ k is found at fuel ≤ k+1 — the Phase B.2 obligation, scoped to
    the atom-realized fragment). Soundness direction is unconditional. -/
theorem atomFinite_iff
    (k : Nat) (me opponent : Prog) (a : Action)
    (complete_bound : ∀ n, PlaysProof me opponent me a n → n ≤ k →
        ∃ s, ppSize (k+1) me opponent me a = some s ∧ s ≤ k) :
    AtomFinite k me opponent a ↔ ∃ s, ppSize (k+1) me opponent me a = some s ∧ s ≤ k := by
  constructor
  · rintro ⟨n, hpp, hnk⟩; exact complete_bound n hpp hnk
  · rintro ⟨s, hf, hsk⟩; exact ⟨s, ppSize_sound (k+1) me opponent me a s hf, hsk⟩

/-- **The decision RHS is genuinely `Decidable` (computes).** `ppSize (k+1) me opp me a` is a
    concrete `Option Nat`, so `∃ s, … = some s ∧ s ≤ k` reduces to inspecting it. -/
example (k : Nat) (me opponent : Prog) (a : Action) :
    Decidable (∃ s, ppSize (k+1) me opponent me a = some s ∧ s ≤ k) := by
  cases h : ppSize (k+1) me opponent me a with
  | none => exact isFalse (by rintro ⟨s, hs, _⟩; simp at hs)
  | some s =>
      by_cases hsk : s ≤ k
      · exact isTrue ⟨s, rfl, hsk⟩
      · exact isFalse (by rintro ⟨s', hs', hs'k⟩; exact hsk (Option.some.inj hs' ▸ hs'k))

-- smoke test: ppSize RUNS on a real const bot. CooperateBot = .const C plays C.
#eval ppSize 5 (.const .C) (.const .D) (.const .C) .C   -- expect some 1

/-! ## Result log — Phase A: PASSED ✅

`ppSize` for the REAL `PlaysProof` (all 8 arms: const/self/opp/bot/sim/ite_t+ite_f/search_t,
real cost model `c_leaf`/`c_node`/`c_guard k`) + full `ppSize_sound`. Compiles clean, NO sorry,
NO Classical. `#print axioms ppSize_sound = [propext, Quot.sound]`.

**The risky arm (`search_t`) WORKS against the real engine.** Confirmed:
  • The guard's `Provable k (φ.subst me opp)` premise is reconstructed via `Provable.atom
    (AtomProvable.mk hguard_pp hsgk)` — where `hguard_pp : PlaysProof gs' gt' gs' ga sg` comes
    from a recursive `ppSize` on the guard ATOM (subject vs target, body = subject, matching
    `AtomProvable.mk`'s `PlaysProof me opp me a n` shape), and `hsgk : sg ≤ k` is the budget gate.
  • Non-atom guards (impl/box/neg/eq) → `none` (correct: the struct/reflection/axiom/fixpoint
    cases with no finite play certificate). `ppSize` NEVER touches the non-decidable `Provable`
    reflection rules — it only ever rebuilds `Provable.atom`, the decidable fragment.
  • The cost index `n + c_guard k + c_node` matches the real `search_t` constructor exactly; the
    guard's own size `sg` is NOT in the total (it lives in the guard's budget `k`), as required.

**De-risk status (Phase A):** the SINGLE riskiest piece (`search_t`'s atom-split +
`Provable.atom` reconstruction + real cost) is GREEN.

## Result log — Phase B: PASSED (with honest scope) ✅

Ported the proven `DecidableFiniteSpike` chain to the REAL engine, all sorry-free:
  • `plays_det` — play determinism (engine LACKED it), from `playsProof_sound` + `eval_mono_le`.
  • `ppSize_no_false` — checker never reports a non-existent play (soundness + determinism).
  • `ppSize_mono_lift` — fuel-lift `f₁≤f₂` with cost `≤`; the `.ite` non-monotonicity (then-branch
    newly succeeding) is killed by `no_false` exactly as in the toy; the `search_t` arm lifts the
    guard sub-recursion + then-branch with the `c_guard k`-aware cost. **`[propext, Classical.choice,
    Quot.sound]`** (Classical.choice transitive from the engine's classical meta-theory).
  • `ppSize_search_complete` — the genuinely-new content: the `search_t` COMPLETENESS reconstruction
    (cost `≤ n + c_guard k + c_node`, matching the real index), CONDITIONAL on guard + then-branch
    witnesses. `[propext]` only.
  • `atomFinite_iff` + a worked `Decidable (∃ s, ppSize (k+1) … = some s ∧ s ≤ k)` instance — the
    decision COMPUTES (`#eval ppSize 5 (.const C) … = some 1`). `atomFinite_iff = [propext, Quot.sound]`.

**Honest scope (what is NOT a full `ppSize_complete`).** Cost-aware completeness over the WHOLE
`PlaysProof.rec` requires threading guard-provability through `Provable`'s reflection rules
(`weakenImpl`/`searchThenSearch_t`/`implTrans`/`atomBoxImpl`) — NOT finitely decidable, the
out-of-scope fixpoint/reflection cases. So `atomFinite_iff` carries the completeness bound as a
hypothesis (`complete_bound`), scoped to the atom-realized fragment; soundness is unconditional.
The `c_guard`-aware cost ASSEMBLY — the load-bearing de-risk content — is fully proven
(`mono_lift`, `search_complete`); only the reflection-rule recursion is excluded, by design.

**No new wall found in Phase A or B.** Remaining Phase C (re-prove `atom_complete` else-branch via
the eval-trace bridge `proofSearch=false ⟺ ¬Provable` from `SearchFFeasibilitySpike`, + drop the
axiom) is the last step; its hard sub-piece is already machine-checked. -/

end PD.PortPhaseA
