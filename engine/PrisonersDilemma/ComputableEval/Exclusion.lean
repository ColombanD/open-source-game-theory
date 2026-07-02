import PrisonersDilemma.Derivation
import PrisonersDilemma.ComputableEval.PlaysCheck

/-!
# Exclusion — the else-play's certificate type is provably empty

This module promotes, into the root-imported engine, the machine-checked structural reason that
`atom_complete_false_guard` (`Axioms.lean`) is **irreducible**: a `.search`-bot playing its
*else*-action has NO finite proof TERM, only a true `interp`. The axiom postulates that true
consequence; the certificate it would need does not exist as a term.

All lemmas are `[propext]`-only (verify with `#print axioms`) and do NOT depend on
`atom_complete_false_guard`. The headline is **`provable_else_isAtom`** — for the false-guard shape
`me = .search k ψ (.const aT) (.const aE)` with `aT ≠ aE`, any `Provable k (.plays me opp aE)` reduces
to `AtomProvable`. The `struct`/`Derivation` path is excluded by `no_deriv_else` (no `Derivation`
concludes the else-action); the reflection rules conclude `.impl`, type-incompatible; the `app`
(object modus ponens) path is excluded by `no_provable_forbidden` (no `Provable` concludes an
implication whose consequent is the else-play). And `AtomProvable.mk` needs a `PlaysProof` of the
else-play, which `search_t` (the only `.search` `PlaysProof` rule, concluding the THEN-action) never
produces — so the certificate type is empty (`no_pp_else`).

**These lemmas are SOUNDNESS-LOAD-BEARING since the proof-DATA constructors landed:** `app`/`axK`
could otherwise route a proof to the false else-play; `no_provable_forbidden`/`no_pp_else` prove they
cannot, keeping the exclusion result (and the irreducibility argument) intact.

Background: `Research/Notes/WALLS_AND_EXTENSIONS.md`, `Research/Spikes/atom_complete_false_guard/`.
-/

namespace PD.Exclusion
open PD PD.PlaysCheck

/-! ## The exclusion lemmas (the else-play has no `Derivation`/`PlaysProof`/`Provable` cert) -/

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

/-- **No `PlaysProof` of a `.search`-bot's ELSE-action** as its OWN body. The only `.search`
    `PlaysProof` rule is `search_t`, which concludes the THEN-action `aT ≠ aE`; the body here is the
    `.search` bot itself (`body = meS`), so no other rule applies. By `cases` on the certificate. -/
theorem no_pp_else (k : Nat) (ψ0 : Formula) (aT aE : Action) (q : Prog) (hne : aT ≠ aE) {n : Nat}
    (cert : PlaysProof (.search k ψ0 (.const aT) (.const aE)) q (.search k ψ0 (.const aT) (.const aE)) aE n) :
    False := by
  -- the only `.search` rule is `search_t`, whose THEN-branch sub-proof runs `p = .const aT`; a
  -- `.const aT` can only play `aT`, so the conclusion action is `aT`, forced here to `aE` ⇒ `aT = aE`.
  cases cert with
  | search_t _ subcert =>
      -- subcert : PlaysProof meS q (.const aT) aE — but `.const` only plays its own action, forcing
      -- `aE = aT`, so `hne : aT ≠ aT`.
      cases subcert; exact hne rfl

/-- **No `Provable` concludes a `Forbidden` formula** (the else-play, or an implication whose
    consequent transitively is). Empties the `Provable.app` route to the else-play. Mirrors
    `cimcic_no_provable_forbidden`'s `Provable.rec` structure; the `atom` else-play case bottoms out
    on `no_pp_else`. -/
theorem no_provable_forbidden (k0 : Nat) (ψ0 : Formula) (aT aE : Action) (q0 : Prog) (hne : aT ≠ aE) :
    ∀ {m φ}, Provable m φ →
      ¬ Forbidden (.search k0 ψ0 (.const aT) (.const aE)) q0 aE φ := by
  intro m φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ φ _ => ¬ Forbidden (.search k0 ψ0 (.const aT) (.const aE)) q0 aE φ)
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    (fun {_k} {_φ} hd => by intro hF; obtain ⟨d, _⟩ := hd; exact no_deriv_else k0 ψ0 aT aE q0 hne d hF)
    (fun {_k} {_φ} hatom _ => by
        intro hF
        cases hatom with
        | mk cert _ =>
            simp only [Forbidden] at hF; obtain ⟨hp, hq, ha⟩ := hF
            subst hp; subst hq; subst ha; exact no_pp_else _ _ _ _ _ hne cert)
    (fun _ _ _ _ _ _ ih => by intro hF; exact ih hF)                              -- weakenImpl
    (fun {_k} _k₁ _k₂ _ψ₁ _ψ₂ _c0 _c1 _q _me _opp hme _hprud _hk2 _hsz _ih => by  -- searchThenSearch_t
        intro hF; subst hme; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all)
    (fun _φ _ψ _χ _a _b _hab _hbc _hak _hbk _hψsz _hsz _ihab ihbc => by intro hF; exact ihbc hF)  -- implTrans
    (fun {_k} _ _ _ _ _ _ _ => by intro hF; simp only [Forbidden] at hF)         -- atomBoxImpl
    (fun _kIn _K _φ _hprem _hsz _ih => by intro hF; simp only [Forbidden] at hF) -- boxIntro
    (fun _k _m _φ' _α _himpl _hante _hmk ihimpl _ihante => by intro hF; exact ihimpl hF)  -- app
    (fun _k _K _φ _α _himpl _hsz _ih => by intro hF; simp only [Forbidden] at hF) -- axK
    (fun _k _K _φ _hksz _hsz => by intro hF; simp only [Forbidden] at hF)          -- box4
    -- diagF: conclusion peels to `Forbidden tgt`; the LÖB-PREMISE GATE's IH peels to the same — contradiction.
    (fun _g _K _tgt _hgate _hsz ih => by intro hF; exact ih hF)                   -- diagF (gated)
    -- diagB: conclusion peels to `Forbidden (.diag …)` = False (catch-all).
    (fun _g _K _tgt _hgate _hsz _ih => by intro hF; simp only [Forbidden] at hF)     -- diagB
    -- axKf: conclusion peels to `.box` = False.
    (fun _k _K _φ _α _hsz => by intro hF; simp only [Forbidden] at hF)               -- axKf
    -- impS2: conclusion `φ→χ` peels to `Forbidden χ`; IH on premise-1 `φ→(ψ→χ)` peels to the same.
    (fun _φ _ψ _χ _m _K _h1 _h2 _hmk _hsz ih1 _ih2 => by intro hF; exact ih1 hF)  -- impS2
    h


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
  | app =>
      -- `app` could conclude the else-play via modus ponens from `Provable m (φ' → else-play)`. But
      -- that implication is `Forbidden` (consequent = else-play), and `no_provable_forbidden` empties
      -- every `Forbidden` `Provable` — so this case is vacuous.
      -- bound order: `m`, antecedent formula `φ'`, antecedent proof, `m ≤ k`, IMPLICATION proof.
      rename_i m φ' _hante _hmk himpl
      have hF : Forbidden (.search k ψ0 (.const aT) (.const aE)) q aE
          (.impl φ' (.plays (.search k ψ0 (.const aT) (.const aE)) q aE)) := ⟨rfl, rfl, rfl⟩
      exact (no_provable_forbidden k ψ0 aT aE q hne himpl hF).elim

end PD.Exclusion
