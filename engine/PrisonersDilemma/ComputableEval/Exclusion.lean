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

/-- **No CHEAP `PlaysProof` of a `.search`-bot's ELSE-action** as its OWN body: no certificate
    within the guard's own budget `k`. (Since the `search_f` repair, else-certificates DO exist —
    but their cost pays the full failed budget, so they always exceed `k`: THE FLOOR. This
    cost-qualified form is exactly what consistency permits; the unqualified version was the
    inconsistent axiom's shape.) `search_t` concludes the THEN-action `aT ≠ aE`; `search_f`'s
    cost `n' + m + k + c_node > k` is ruled out by the bound. -/
theorem no_pp_else (k : Nat) (ψ0 : Formula) (aT aE : Action) (q : Prog) (hne : aT ≠ aE) {n : Nat}
    (hn : n ≤ k)
    (cert : PlaysProof (.search k ψ0 (.const aT) (.const aE)) q (.search k ψ0 (.const aT) (.const aE)) aE n) :
    False := by
  cases cert with
  | search_t _ subcert =>
      -- subcert : PlaysProof meS q (.const aT) aE — but `.const` only plays its own action, forcing
      -- `aE = aT`, so `hne : aT ≠ aT`.
      cases subcert; exact hne rfl
  | search_f _ _ =>
      -- the else-certificate pays the full failed budget: cost ≥ k + 1 > k ≥ n — the floor.
      have hcn : c_node = 1 := rfl
      omega

/-- **No `Provable` concludes a `Forbidden` formula** (the else-play, or an implication whose
    consequent transitively is). Empties the `Provable.app` route to the else-play. Mirrors
    `cimcic_no_provable_forbidden`'s `Provable.rec` structure; the `atom` else-play case bottoms out
    on `no_pp_else`. -/
theorem no_provable_forbidden (k0 : Nat) (ψ0 : Formula) (aT aE : Action) (q0 : Prog) (hne : aT ≠ aE) :
    ∀ {m φ}, Provable m φ → m ≤ k0 →
      ¬ Forbidden (.search k0 ψ0 (.const aT) (.const aE)) q0 aE φ := by
  -- COST-QUALIFIED since the `search_f` repair: else-certificates exist ABOVE the floor
  -- (cost > k0), so the exclusion holds exactly WITHIN the guard's own budget — which is
  -- all `provable_else_isAtom`/the guard semantics ever needed. The additive gates thread
  -- the bound through every premise (premise budgets ≤ conclusion budget ≤ k0).
  intro m φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun m φ _ => m ≤ k0 →
      ¬ Forbidden (.search k0 ψ0 (.const aT) (.const aE)) q0 aE φ)
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    (fun {_k} {_φ} hd => by
        intro _hm hF; obtain ⟨d, _⟩ := hd; exact no_deriv_else k0 ψ0 aT aE q0 hne d hF)
    (fun {_k} {_φ} hatom _ => by
        intro hm hF
        cases hatom with
        | mk cert hle =>
            simp only [Forbidden] at hF; obtain ⟨hp, hq, ha⟩ := hF
            subst hp; subst hq; subst ha
            exact no_pp_else _ _ _ _ _ hne (by omega) cert)
    (fun _φ _ψ _m _hψ hle ih => by intro hm hF; exact ih (by omega) hF)          -- weakenImpl
    (fun {_k} _k₁ _k₂ _m _ψ₁ _ψ₂ _c0 _c1 _q _me _opp hme _hprud _hmk _hle _ih => by      -- searchThenSearch_t
        intro _hm hF; subst hme; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all)
    (fun _φ _ψ _χ _a _b _hab _hbc hle _ihab ihbc => by
        intro hm hF; exact ihbc (by omega) hF)                                    -- implTrans
    (fun {_k} _ _ _ _ _ _ _ => by intro _hm hF; simp only [Forbidden] at hF)     -- atomBoxImpl
    (fun _kIn _K _φ _hprem _hle _ih => by intro _hm hF; simp only [Forbidden] at hF) -- boxIntro
    (fun _k _m₁ _m₂ _φ' _α _himpl _hante hle ihimpl _ihante => by
        intro hm hF; exact ihimpl (by omega) hF)                                  -- app
    (fun _a _b _c _m _K _φ _α _hprem _hgate _hle _ih => by
        intro _hm hF; simp only [Forbidden] at hF)                                -- axK
    (fun _a _b _K _φ _hgate _hsz => by intro _hm hF; simp only [Forbidden] at hF) -- box4
    -- diagF: conclusion peels to `Forbidden tgt`; the LÖB-PREMISE GATE's IH peels to the same — contradiction.
    (fun _pm _fb _g _K _tgt _hgate hle ih => by
        intro hm hF; exact ih (by omega) hF)                                      -- diagF (gated)
    -- diagB: conclusion peels to `Forbidden (.diag …)` = False (catch-all).
    (fun _pm _fb _g _K _tgt _hgate _hle _ih => by
        intro _hm hF; simp only [Forbidden] at hF)                                -- diagB
    -- axKf: conclusion peels to `.box` = False.
    (fun _a _b _c _K _φ _α _hgate _hsz => by
        intro _hm hF; simp only [Forbidden] at hF)                                -- axKf
    -- impS2: conclusion `φ→χ` peels to `Forbidden χ`; IH on premise-1 `φ→(ψ→χ)` peels to the same.
    (fun _φ _ψ _χ _m₁ _m₂ _K _h1 _h2 hle ih1 _ih2 => by
        intro hm hF; exact ih1 (by omega) hF)                                     -- impS2
    -- boxMono: conclusion `□_aφ→□_bφ` peels to `.box` = False.
    (fun _a _b _K _φ _hab _hsz => by intro _hm hF; simp only [Forbidden] at hF)   -- boxMono
    -- atomNeg: conclusion `.neg` = False (catch-all).
    (fun _p _q _b _aN _m _hatom _hne _hle _ih => by
        intro _hm hF; simp only [Forbidden] at hF)                                -- atomNeg
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
      -- bound order: `m₁ m₂`, antecedent formula `φ'`, antecedent proof, IMPLICATION proof, gate.
      rename_i m₁ m₂ φ' _hante himpl hle
      have hF : Forbidden (.search k ψ0 (.const aT) (.const aE)) q aE
          (.impl φ' (.plays (.search k ψ0 (.const aT) (.const aE)) q aE)) := ⟨rfl, rfl, rfl⟩
      have hsp : 1 ≤ (Formula.plays (.search k ψ0 (.const aT) (.const aE)) q aE).size := by
        simp only [Formula.size]; omega
      exact (no_provable_forbidden k ψ0 aT aE q hne himpl (by omega) hF).elim

end PD.Exclusion
