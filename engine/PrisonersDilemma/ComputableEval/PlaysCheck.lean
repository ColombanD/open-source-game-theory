import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

/-!
# `ppSize` — a computable, sound decider for the bounded play-certificate

This module makes the content of the `atom_complete_false_guard` axiom (`Axioms.lean`)
**decidable**: it provides a genuinely computable procedure `ppSize` that decides whether a
play-atom has a bounded `PlaysProof`, proven SOUND against the engine (`ppSize_sound`), plus
play-determinism (`plays_det`) and the eval-trace bridge that connects a *failed* guard to the
else-branch play (`eval_search_false`).

**Why this matters for the axiom.** `atom_complete`'s false-guard branch certifies a play that
took a `.search` *else*-branch (guard failed: `proofSearch k guard = false`). Such a play has NO
`PlaysProof` — the `.search` constructor `search_t` only reads a *true* guard, and a `search_f`
constructor is kernel-impossible (it would carry the negation of the proof object itself, a
non-positive occurrence; see `Research/Spikes/SearchFFeasibilitySpike.lean` and `SizeIndexSpike.lean`).
So the axiom is NOT witness-free sloppiness: the missing certificate is *structurally* unbuildable
at the current architecture (the `PlaysProof ↔ Provable ↔ proofSearch` cyclic dependency).

What IS true, and what this file establishes: the false-guard fact `¬ ∃ proof` is the negation of
a **decidable** predicate — `ppSize` computes the certificate's existence (and minimal size) by a
terminating procedure, sound by `ppSize_sound`. So the axiom postulates a *decidable* fact, not an
oracle; discharging it constructively needs only breaking the cyclic dependency (a size-indexed,
`proofSearch`-free bounded-provability predicate defined *before* the certificate type), which is a
foundational refactor, not new mathematics. This module is the computable witness that the boundary
is decidability-of-existence, cleanly located.

Full investigation + the completeness/`Decidable` direction (scoped to the atom-realized fragment)
live in `Research/Spikes/PortPhaseASpike.lean` / `DecidableFiniteSpike.lean`.
-/

namespace PD.PlaysCheck
open PD

/-- `otherAction C = D`, `otherAction D = C`. -/
def otherAction : Action → Action
  | .C => .D
  | .D => .C

/-- `ppSize fuel me opp body a` = the minimal size of a `PlaysProof me opp body a _`, or `none`
    if none fits the structural `fuel`. Mirrors the `PlaysProof` 8-constructor shape with the real
    cost model. PURELY syntactic (no `PlaysProof`/`Provable`/`proofSearch`). The `.search` arm reads
    a guard only when it is an ATOM-realized play (the only finitely-decidable guard fragment);
    non-atom guards → `none`. -/
def ppSize : Nat → (me opponent body : Prog) → Action → Option Nat
  | 0,      _,  _,        _,             _ => none
  | _+1,    _,  _,        .const c,      a => if c == a then some c_leaf else none
  | fuel+1, me, opponent, .self,         a => (ppSize fuel me opponent me a).map (· + c_node)
  | fuel+1, me, opponent, .opp,          a => (ppSize fuel me opponent opponent a).map (· + c_node)
  | fuel+1, me, opponent, .bot p,        a => (ppSize fuel me opponent p a).map (· + c_node)
  | fuel+1, me, opponent, .sim p q,      a =>
      (ppSize fuel (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a).map (· + c_node)
  | fuel+1, me, opponent, .ite b a' p q, a =>
      match ppSize fuel me opponent b a', ppSize fuel me opponent p a with
      | some mg, some np => some (mg + np + c_node)
      | _, _ =>
        match ppSize fuel me opponent b (otherAction a'), ppSize fuel me opponent q a with
        | some mg, some nq => some (mg + nq + c_node)
        | _, _ => none
  | fuel+1, me, opponent, .search k φ p q, a =>
      match φ with
      | .plays gs gt ga =>
          let gs' := gs.subst me opponent
          let gt' := gt.subst me opponent
          match ppSize fuel gs' gt' gs' ga with
          | some sg => if sg ≤ k then (ppSize fuel me opponent p a).map (· + c_guard k + c_node)
                       else none
          | none => none
      | _ => none

/-- **`Provable_fin k φ`** — the *finite* (size-≤-k, proof-TERM) bounded-provability predicate, on
    the play-atom/eq fragment. DECIDABLE, `proofSearch`-free. It is NOT all of `Provable` (the
    reflection rules / `PBLT`-injected Löb fixpoints are out of fragment — at a fixpoint
    `Provable_fin` is `false` even though `Provable` is axiom-true: the proof-vs-witness separation).

    This is the computable WITNESS for `atom_complete_false_guard`'s decidability claim (`Axioms.lean`):
    the axiom postulates a fact that IS decidable (here) but cannot be soundly CARRIED as a `PlaysProof`
    constructor (the two-wall + `Exclusion.lean` result). Arms: a play-atom via `ppSize`; an `.eq p q`
    via `p = q` (the `eqRefl` leaf, agreeing with `Provable.struct ⟨eqRefl,…⟩`); else out of fragment. -/
def Provable_fin (k : Nat) (φ : Formula) : Prop :=
  match φ with
  | .plays p q a => ∃ s, ppSize (k+1) p q p a = some s ∧ s ≤ k
  | .eq p q      => p = q ∧ (Formula.eq p p).size ≤ k
  | _            => False

instance instDecProvableFin (k : Nat) (φ : Formula) : Decidable (Provable_fin k φ) := by
  unfold Provable_fin
  cases φ with
  | plays p q a =>
      cases h : ppSize (k+1) p q p a with
      | none => exact isFalse (by rintro ⟨s, hs, _⟩; simp [h] at hs)
      | some s =>
          by_cases hsk : s ≤ k
          · exact isTrue ⟨s, h, hsk⟩
          · exact isFalse (by rintro ⟨s', hs', hs'k⟩; rw [h] at hs'; cases hs'; exact hsk hs'k)
  | eq p q => exact (inferInstance : Decidable (p = q ∧ (Formula.eq p p).size ≤ k))
  | _ => exact isFalse (by simp)

/-- **Soundness:** a `some s` from `ppSize` yields a real `PlaysProof` of cost exactly `s`. The
    `.search` arm reconstructs `search_t` via `Provable.atom (AtomProvable.mk …)` (the guard
    atom-realized within its budget `k`). No axiom. -/
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
                  have hguard_pp : PlaysProof (gs.subst me opp) (gt.subst me opp) (gs.subst me opp) ga sg :=
                    ih _ _ _ ga sg hg
                  have hguard_prov : Provable k ((Formula.plays gs gt ga).subst me opp) :=
                    Provable.atom (.mk hguard_pp hsgk)
                  exact PlaysProof.search_t hguard_prov (ih me opp p a n hn)
                · rw [if_neg hsgk] at h; simp at h
        | impl _ _ => simp only [ppSize] at h; exact absurd h (by simp)
        | neg _ => simp only [ppSize] at h; exact absurd h (by simp)
        | box _ _ => simp only [ppSize] at h; exact absurd h (by simp)
        | eq _ _ => simp only [ppSize] at h; exact absurd h (by simp)

/-- **`Provable_fin` agreement (soundness).** The finite bounded-provability predicate
    (`Derivation.lean`) only proves real things: `Provable_fin k φ → Provable k φ`. Play-atom arm
    via `ppSize_sound` + `Provable.atom`; `.eq` arm via `Derivation.eqRefl` + `Provable.struct`.
    The converse holds ONLY off the Löb fixpoints (by design — at a fixpoint `Provable_fin` is
    `false` while `Provable` is `PBLT`-axiom-true). This is the lemma `search_f` soundness uses. -/
theorem provableFin_sound (k : Nat) (φ : Formula) (h : Provable_fin k φ) : Provable k φ := by
  unfold Provable_fin at h
  cases φ with
  | plays p q a =>
      obtain ⟨s, hf, hsk⟩ := h
      exact Provable.atom (.mk (ppSize_sound (k+1) p q p a s hf) hsk)
  | eq p q =>
      -- h : p = q ∧ (.eq p p).size ≤ k  ⇒  Derivation.eqRefl p : Derivation (.eq p p), size ≤ k
      obtain ⟨hpq, hsz⟩ := h
      subst hpq
      exact Provable.struct ⟨Derivation.eqRefl p, hsz⟩
  | _ => exact absurd h (by simp)

/-- **Play determinism** (the engine previously lacked this): a body plays at most one action vs
    a fixed opponent. From `playsProof_sound` (→ real `eval` play) + `eval_mono_le`. -/
theorem plays_det {me opponent body : Prog} {a₁ a₂ : Action} {n₁ n₂ : Nat}
    (h₁ : PlaysProof me opponent body a₁ n₁) (h₂ : PlaysProof me opponent body a₂ n₂) :
    a₁ = a₂ := by
  obtain ⟨N₁, e₁⟩ := PD.BaseTheorems.playsProof_sound h₁
  obtain ⟨N₂, e₂⟩ := PD.BaseTheorems.playsProof_sound h₂
  have f₁ := PD.BaseTheorems.eval_mono_le e₁ (max N₁ N₂) (Nat.le_max_left _ _)
  have f₂ := PD.BaseTheorems.eval_mono_le e₂ (max N₁ N₂) (Nat.le_max_right _ _)
  rw [f₁] at f₂; exact (Option.some.injEq _ _ ▸ f₂)

/-- **The bounded play-certificate predicate** = the content of `AtomProvable k (.plays me opp a)`
    (Derivation.lean:248): a `PlaysProof me opp me a n` with `n ≤ k`. -/
def AtomFinite (k : Nat) (me opponent : Prog) (a : Action) : Prop :=
  ∃ n, PlaysProof me opponent me a n ∧ n ≤ k

/-- **The decision is genuinely `Decidable` (it computes).** `ppSize (k+1) me opp me a` is a
    concrete `Option Nat`; the `some s ∧ s ≤ k` test inspects it. SOUND (`ppSize_sound`); the
    completeness direction (every certificate of size ≤ k found at fuel ≤ k+1) is the atom-realized
    fragment, established in `Research/Spikes/PortPhaseASpike.lean`. This instance witnesses that
    the false-guard fact is the negation of a decidable predicate, not an oracle. -/
instance decAtomFiniteCheck (k : Nat) (me opponent : Prog) (a : Action) :
    Decidable (∃ s, ppSize (k+1) me opponent me a = some s ∧ s ≤ k) := by
  cases h : ppSize (k+1) me opponent me a with
  | none => exact isFalse (by rintro ⟨s, hs, _⟩; simp at hs)
  | some s =>
      by_cases hsk : s ≤ k
      · exact isTrue ⟨s, rfl, hsk⟩
      · exact isFalse (by rintro ⟨s', hs', hs'k⟩; exact hsk (Option.some.inj hs' ▸ hs'k))

/-- **Soundness of the check ⇒ `AtomFinite`.** A successful `ppSize` decision yields the real
    bounded certificate. (The converse — completeness — is the atom-realized-fragment result in
    the spikes; soundness is what makes the decision trustworthy as a *witness*.) -/
theorem check_sound (k : Nat) (me opponent : Prog) (a : Action)
    (h : ∃ s, ppSize (k+1) me opponent me a = some s ∧ s ≤ k) :
    AtomFinite k me opponent a := by
  obtain ⟨s, hf, hsk⟩ := h
  exact ⟨s, ppSize_sound (k+1) me opponent me a s hf, hsk⟩

/-- **Eval-trace bridge.** When the guard search FAILS (`proofSearch k guard = false`), `eval`'s
    `.search` rule runs the ELSE-branch `q` — so the play is the else play. This is the semantic
    fact underlying `atom_complete`'s false-guard case: the play is real (it just took the else
    branch), but no `PlaysProof` certifies it (no `search_f`). -/
theorem eval_search_false (n : Nat) (me opponent : Prog)
    (k : Nat) (φ : Formula) (p q : Prog)
    (hguard : proofSearch k (φ.subst me opponent) = false) :
    eval (n+1) me opponent (.search k φ p q) = eval n me opponent q := by
  rw [eval]; rw [hguard]; rfl

end PD.PlaysCheck
