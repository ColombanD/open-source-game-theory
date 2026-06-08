import PrisonersDilemma.Eval

namespace PDNew
open Classical

/-!
# The explicit derivation system `S`

This file makes the ambient proof system `S` *semi-explicit*. Instead of an
abstract `proofSearch` oracle bolted on as an axiom, we define a small
inductive `Derivation` whose rules are individually inspectable, prove its
soundness, and *define* `proofSearch` as decidable provability over it.

The only assumptions that survive are isolated to atomic `.plays` formulas
(σ₁-completeness and atom-soundness — see `AtomProvable` below); these cannot
be made constructive without recreating the cycle
`AtomProvable → play → proofSearch → Provable → AtomProvable`.
-/

-- 1. The derivation system: three syntactic shape-rules. No general
-- reflection, and crucially no atomic-`plays` rule (that would have to carry a
-- `play` hypothesis, recreating the cycle — atoms are handled by `AtomProvable`).
inductive Derivation : Formula → Type where
  /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
  | searchBranch (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .search k ψ (.const a) (.const b)) :
      Derivation (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
  /-- S can read a `.sim` body: `me` plays `a` iff its closed body does. -/
  | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
      Derivation (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                        (.plays me opponent a))
  /-- Hypothetical syllogism: a basic structural rule of any proof system. -/
  | hypSyll (φ ψ χ : Formula) :
      Derivation (.impl φ ψ) → Derivation (.impl ψ χ) → Derivation (.impl φ χ)

/-- Proof size; the budget measured by `proofSearch`. -/
def Derivation.size : {φ : Formula} → Derivation φ → Nat
  | _, .searchBranch ..   => 1
  | _, .simStep ..        => 1
  | _, .hypSyll _ _ _ d e => d.size + e.size + 1

-- 2. σ₁ atom-provability as an opaque predicate. It cannot reference `play`
-- (cycle), so it is opaque and pinned down only by the two atom axioms below,
-- stated after `play` exists. Budget-independent: an atom is σ₁-true (hence
-- provable at *some* size) or it is not — there is no tight size bound to track,
-- which makes proof-search budget-monotonicity automatic.
opaque AtomProvable : Formula → Prop

-- 3. Provability in S: derivable by the structural rules within budget `k`, OR
-- an atomic σ₁ fact. This is the truth condition the box modality refers to.
def Provable (k : Nat) (φ : Formula) : Prop :=
  (∃ d : Derivation φ, d.size ≤ k) ∨ AtomProvable φ

-- 4. The proof-search oracle is now a *definition*, not an axiom: bounded
-- provability, reflected into `Bool` for the evaluator's guard. Classical
-- (hence noncomputable), which is correct for a model of an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)

/-- The bridge `proofSearch ↔ Provable` is now a theorem, not an axiom. -/
theorem proofSearch_spec (k : Nat) (φ : Formula) :
    proofSearch k φ = true ↔ Provable k φ := by
  unfold proofSearch; exact decide_eq_true_iff

-- 5. Tie the knot: the canonical evaluator fixes the oracle to the real
-- `proofSearch`. We give `eval` its *own* native definition (recursing on
-- itself, with `proofSearch` inlined) rather than `evalWith proofSearch`, so
-- its generated equation lemmas fire under `simp [eval]` / `unfold eval`
-- exactly as before the reform — leaving all ~22 downstream `.search`-branch
-- reductions untouched. (It is propositionally `evalWith proofSearch`; see
-- `eval_eq_evalWith` below.)
noncomputable def eval : Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none
  | n+1, me, opponent, body => match body with
    | .const a        => some a
    | .self           => eval n me opponent me
    | .opp            => eval n me opponent opponent
    | .bot p          => eval n me opponent p
    | .sim p q        =>
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        eval n p' q' p'
    | .ite b a p q    => do
        let r ← eval n me opponent b
        if r == a then eval n me opponent p else eval n me opponent q
    | .search k φ p q =>
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q

/-- `eval` is the parametric `evalWith` with the real oracle plugged in. -/
theorem eval_eq_evalWith : eval = evalWith proofSearch := by
  funext n; induction n with
  | zero => rfl
  | succ n ih => funext me opponent body; cases body <;> simp [eval, evalWith, ih]

noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)

-- 6. Denotational semantics. The box clause now refers to `Provable` directly
-- — the semantics no longer quotes a black-box oracle.
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => Provable n φ

-- 7. Soundness of the structural rules. Each `Derivation` yields a true
-- formula. The interesting cases (`searchBranch`, `simStep`) are exactly the
-- semantic content the old transparency axioms asserted for free.
theorem Derivation.sound : ∀ {φ}, Derivation φ → φ.interp := by
  intro φ d
  induction d with
  | searchBranch k ψ a b me opponent hme =>
      -- `me` is a `.search` node; a provable guard makes `eval` take the
      -- `.const a` branch, so `me` plays `a` against `opponent`.
      subst hme
      intro hguard
      have hps : proofSearch k (ψ.subst (.search k ψ (.const a) (.const b)) opponent) = true :=
        (proofSearch_spec _ _).2 hguard
      exact ⟨2, by simp only [play, eval, hps, if_true]⟩
  | simStep me p q opponent a hme =>
      -- `me` is a `.sim` node; by the `.sim` eval rule, `me` plays `a` iff its
      -- closed body `p'` plays `a` against `q'`.
      subst hme
      intro h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by show eval (n+1) (.sim p q) opponent (.sim p q) = some a
                       simp only [eval]; exact hn⟩
  | hypSyll φ ψ χ _ _ ih1 ih2 =>
      exact fun h => ih2 (ih1 h)

-- 8. Atom axioms (the one deliberately-kept assumption, isolated to `.plays`).
-- They mention `play`/`interp`, so they come after those are defined.

/-- σ₁-completeness for atoms: a true atomic play is provable in S.
    critch22 uses this implicitly (e.g. "CUPOD(10⁹)(DB.source) will find the
    proof and return D"); it is decidable Σ₁ truth, no Gödel obstruction. -/
axiom atom_complete :
  ∀ p q a, (∃ n, play n p q = some a) → AtomProvable (.plays p q a)

/-- S is sound on atoms. Companion to `atom_complete`; the atomic analogue of
    `Derivation.sound`, needed because `AtomProvable` is opaque. -/
axiom AtomProvable_sound : ∀ φ, AtomProvable φ → φ.interp

-- 9. Transparency lemmas, now *theorems*. Kept in `PDNew.Axioms` so the
-- existing `open PDNew.Axioms` in the bot theorem files resolves them
-- unqualified — zero edits to their ~20 call sites.
namespace Axioms

/-- A derivation of size `m` witnesses `proofSearch m φ = true` (structural
    disjunct of `Provable`). -/
theorem derives {φ : Formula} (d : Derivation φ) : ∃ m, proofSearch m φ = true :=
  ⟨d.size, (proofSearch_spec _ _).2 (Or.inl ⟨d, Nat.le_refl _⟩)⟩

/--
S can read source code: if an agent `me` is literally
`.search k ψ (.const a) (.const b)`, then S proves
`□_k ψ' → me plays a against opponent`, where `ψ' = ψ.subst me opponent`.

Was an axiom; now a theorem, witnessed by `Derivation.searchBranch`.
-/
theorem proof_system_verifies_search_branch :
    ∀ (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog),
      me = .search k ψ (.const a) (.const b) →
      ∃ m, proofSearch m
        (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a)) = true :=
  fun k ψ a b me opponent hme => derives (.searchBranch k ψ a b me opponent hme)

/--
S can read `.sim` nodes: if `me = .sim p q`, then S proves
`(p' plays a vs q') → (me plays a vs opponent)`.

Was an axiom; now a theorem, witnessed by `Derivation.simStep`.
-/
theorem proof_system_verifies_sim :
    ∀ (me p q opponent : Prog) (a : Action),
      me = .sim p q →
      ∃ m, proofSearch m
        (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
               (.plays me opponent a)) = true :=
  fun me p q opponent a hme => derives (.simStep me p q opponent a hme)

end Axioms

end PDNew
