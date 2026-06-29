import PrisonersDilemma.Derivation
import PrisonersDilemma.ComputableEval.PlaysCheck

/-!
# Exclusion — the else-play's certificate type is provably empty

This module promotes, into the root-imported engine, the machine-checked structural reason that
`atom_complete_false_guard` (`Axioms.lean`) is **irreducible**: a `.search`-bot playing its
*else*-action has NO finite proof TERM, only a true `interp`. The axiom postulates that true
consequence; the certificate it would need does not exist as a term.

Two deliverables, both `[propext]`-only (verify with `#print axioms`), NEITHER depending on
`atom_complete_false_guard`:

1. **`provable_else_isAtom`** — for the false-guard shape `me = .search k ψ (.const aT) (.const aE)`
   with `aT ≠ aE`, any `Provable k (.plays me opp aE)` reduces to `AtomProvable` (the `Provable_fin`
   fragment). The `struct`/`Derivation` path is excluded by `no_deriv_else` (no `Derivation`
   concludes the else-action); the four reflection rules conclude `.impl`, type-incompatible. And
   `AtomProvable.mk` needs a `PlaysProof` of the else-play, which `search_t` (the only `.search`
   `PlaysProof` rule, concluding the THEN-action) never produces — so the certificate type is empty.

2. **`decidablePred_provableFin`** — the finite (size-≤-k, proof-TERM) bounded-provability predicate
   is a `DecidablePred`. Witness shipped (`PlaysCheck.instDecProvableFin`), surfaced here as a named
   lemma. This is the positive half of the same boundary: bounded provability of a *term* is
   decidable; what the axiom asserts is the *negative*, witness-free fact.

Background: `Research/Notes/WALLS_AND_EXTENSIONS.md`, `Research/Spikes/atom_complete_false_guard/`.
-/

namespace PD.Exclusion
open PD PD.PlaysCheck

/-! ## 1. The exclusion lemmas (the else-play has no `Derivation`, hence no struct proof) -/

/-- `Forbidden meS opp aE φ` := `φ` is the else-play `.plays meS opp aE`, or an implication whose
    consequent (transitively) is. The combined "neither shape" motive carries the induction through
    the recursive `modusPonens`/`hypSyll` rules, which preserve the forbidden consequent shape. -/
def Forbidden (meS oppP : Prog) (aE : Action) : Formula → Prop
  | .plays p q a   => p = meS ∧ q = oppP ∧ a = aE
  | .impl _ ψ      => Forbidden meS oppP aE ψ
  | _              => False

/-- A `.search`-bot's ELSE-action is concluded by NO `Derivation` — neither as a bare play-atom nor
    as the consequent of an implication. By induction on `Derivation`: `modusPonens`/`hypSyll`
    recurse (the consequent shape is preserved); the source-transparency rules (`searchBranch` etc.)
    all conclude the THEN-action `aT ≠ aE`, contradiction. -/
theorem no_deriv_else (k : Nat) (ψ0 : Formula) (aT aE : Action) (q : Prog) (hne : aT ≠ aE) :
    ∀ {φ}, Derivation φ → ¬ Forbidden (.search k ψ0 (.const aT) (.const aE)) q aE φ := by
  intro φ d
  induction d with
  | modusPonens φ' ψ' _ _ ihimpl _ =>
      intro hF; exact ihimpl hF
  | hypSyll φ' ψ' χ' _ _ _ ihbc =>
      intro hF; exact ihbc hF
  | searchBranch k2 ψ2 a2 b2 me2 opp2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, ha⟩ := hF
      simp_all
  | simStep me2 p2 q2 opp2 a2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | botSimStep me2 p2 q2 opp2 a2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | botSearchStep k2 ψ2 a2 b2 me2 opp2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | iteBranchSearch_t k2 z2 a2' c0 c1 ψ2 q2 me2 opp2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | eqRefl p2 => intro hF; simp only [Forbidden] at hF

/-- The else-play has NO `Derivation` (bare-atom corollary of `no_deriv_else`). -/
theorem isEmpty_deriv_else (k : Nat) (ψ0 : Formula) (aT aE : Action) (q : Prog) (hne : aT ≠ aE) :
    IsEmpty (Derivation (.plays (.search k ψ0 (.const aT) (.const aE)) q aE)) :=
  ⟨fun d => no_deriv_else k ψ0 aT aE q hne d ⟨rfl, rfl, rfl⟩⟩

/-- **The exclusion payoff.** `Provable k (else-play) ⟹ AtomProvable k (else-play)`: `cases` on
    `Provable` — `struct` is excluded by `isEmpty_deriv_else`; the four reflection rules conclude
    `.impl`, type-incompatible with a bare `.plays`; only `atom` survives. PBLT/`boxInternalize` are
    no obstacle — they ASSERT `Provable` terms, but `Provable` is inductive, so any inhabitant IS a
    constructor application, all excluded but `atom`. -/
theorem provable_else_isAtom (k : Nat) (ψ0 : Formula) (aT aE : Action) (q : Prog) (hne : aT ≠ aE)
    (h : Provable k (.plays (.search k ψ0 (.const aT) (.const aE)) q aE)) :
    AtomProvable k (.plays (.search k ψ0 (.const aT) (.const aE)) q aE) := by
  cases h with
  | struct hd => obtain ⟨d, _⟩ := hd; exact ((isEmpty_deriv_else k ψ0 aT aE q hne).false d).elim
  | atom hatom => exact hatom

/-! ## 2. The positive half — `Provable_fin` is a `DecidablePred`

The finite (size-≤-k, proof-TERM) bounded-provability predicate is genuinely decidable, witnessed
by `PlaysCheck.instDecProvableFin` (which computes). Surfaced here as a named `DecidablePred`. -/

/-- The finite bounded-provability predicate is a `DecidablePred` (it computes, via
    `PlaysCheck.instDecProvableFin`). -/
def decidablePred_provableFin (k : Nat) : DecidablePred (Provable_fin k) :=
  fun _ => inferInstance

end PD.Exclusion
