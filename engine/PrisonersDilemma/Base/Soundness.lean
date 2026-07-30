import PrisonersDilemma.Base.ValuationSoundness

/-!
# Base/Soundness — every provable formula is true

The soundness spine's consumer face: `sound_upto` (the 2026-07-02 `search_f` repair) and
its corollaries `Pf_sound`, `proofSearch_sound`, `box_provable`.

**Pf-only (Phase 2, 2026-07-14).** The former `Derivation.sound` — a separate structural
induction over the `Type`-valued half of `S` — is GONE as a standalone theorem: its arms
(searchBranch / simStep / bot*Step / iteBranchSearch_t / eqRefl / eqNeg, and the
modusPonens/hypSyll function-application arms) are arms of the single `Pf` induction.
`atom_monotone`/`Pf_mono` moved to the core (`ProofSystem.lean`); they are re-exported
below for callers.

**Master-lemma refactor (2026-07-30).** The induction itself now lives in
`Base/ValuationSoundness.lean` as the PARAMETRIC valuation-soundness master lemma
`wv_sound_upto` (one budget-strong induction + raw mutual recursion, serving BOTH plain
soundness and the modified-valuation censuses); `sound_upto` below is its instantiation
at the empty atom relations, with a byte-identical statement. `eval_mono`,
`eval_mono_le`, `implChain_interp`, `searchPlug_eval`, `ctxPlug_eval` moved there too
(same namespace — importers are unaffected). Raw recursors live ONLY in
`ProofSystem.lean` §4 and `ValuationSoundness.lean`; every other consumer uses the
named eliminators or instantiates the master.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-! ## Transcript facts and the source-transparency faces

`Derivation.concl_size_le` (a transcript contains its conclusion) is now definitional: every
`Pf` leaf's side-condition IS `conclusion.size ≤ k`, and the combining rules add their premises
on top. The old `K_provable` (lift `modusPonens` to the budgeted level) is likewise subsumed —
`Pf.mp` IS the budgeted rule. -/

/-- S can read source code: if an agent `me` is literally `.search g ψ (.const a) (.const b)`,
    then S proves `□_g ψ' → me plays a against opponent` (`ψ' = ψ.subst me opponent`).
    Was an axiom; now witnessed by the `Pf.searchBranch` constructor. -/
theorem proof_system_verifies_search_branch :
    ∀ (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog),
      me = .search g ψ (.const a) (.const b) →
      ∃ m, proofSearch m
        (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)) = true :=
  fun g ψ a b me opponent hme =>
    ⟨_, (proofSearch_spec _ _).2 (Pf.searchBranch g ψ a b me opponent hme (Nat.le_refl _))⟩

/-- S can read `.sim` nodes: if `me = .sim p q`, then S proves
    `(p' plays a vs q') → (me plays a vs opponent)`. Witnessed by `Pf.simStep`. -/
theorem proof_system_verifies_sim :
    ∀ (me p q opponent : Prog) (a : Action),
      me = .sim p q →
      ∃ m, proofSearch m
        (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
               (.plays me opponent a)) = true :=
  fun me p q opponent a hme =>
    ⟨_, (proofSearch_spec _ _).2 (Pf.simStep me p q opponent a hme (Nat.le_refl _))⟩


/-! ## Atom certificate soundness (`PlaysProof` → real play)

The atom-side axioms `atom_monotone` and `AtomProvable_sound` are now THEOREMS:
`AtomProvable` is the constructive `PlaysProof` certificate, so monotonicity is
just relaxing its cost bound, and soundness is "a certificate yields a real
play." (Nothing on the false-guard *completeness* side is axiomatic either: the old
`atom_complete_false_guard` axiom was machine-checked INCONSISTENT and deleted
2026-07-03; the sound replacement is the `search_f` floor — see `Base/AtomCerts`
and `Base/Exclusion`.) -/

/-! ### Budget monotonicity — now in the core (`ProofSystem.lean`)

`atom_monotone` and `Pf_mono` are constructors-level facts (every rule's side-condition is
`… ≤ k` with `k` the output budget, so each re-applies with the bound relaxed) and moved to
`ProofSystem.lean` with the type. Re-exported here under the names callers use. -/

export PD (atom_monotone Pf_mono)

/-! ## Joint soundness by STRONG INDUCTION ON THE BUDGET (the `search_f` repair, 2026-07-02).

With the sound false-guard rule `search_f`, soundness cannot be a plain structural induction:
its arm must rule out a HYPOTHETICAL guard proof `Pf k guard` that is not a sub-derivation. The
budget floor in `search_f`'s cost (it pays the full failed budget `k`) is exactly what repairs
this: the hypothetical proof has transcript ≤ k, STRICTLY below the certificate's own cost, so a
strong induction on the budget/cost supplies its soundness. Within one budget `B`, certificates
come first (their `atomNeg`-style premises are smaller-cost certificates), then `Pf` (its `atom`
entry consumes the certificate half at the same `B`). The public `playsProof_sound` /
`AtomProvable_sound` / `Pf_sound` keep their statements as corollaries.

**Pf-only**: the second half now carries the ex-`Derivation` soundness arms directly
(searchBranch/simStep/bot*Step/iteBranchSearch_t/eqRefl/eqNeg + the mp/implTrans
function-application arms) — the old `struct` arm, which recursed into a separate
`Derivation.sound` induction, is gone. The raw `Pf.rec` is deliberate here: this is the one
proof where both motives must ride together (`Pf.atom` consumes a certificate; `search_t`
consumes a `Pf`). Everywhere else, use `Pf.induct`. -/

/-- **Joint soundness** — the instantiation of the master lemma `wv_sound_upto`
    (`Base/ValuationSoundness`) at the EMPTY atom relations, where the census
    obligations discharge vacuously and the valuation half is unused. The statement
    is unchanged from the pre-refactor budget-strong induction (which see, in
    `wv_sound_upto`, for the `search_f` floor argument this shape encodes). -/
theorem sound_upto : ∀ B : Nat,
    (∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
      ∃ N, eval N me opponent body = some a)
    ∧ (∀ k φ, Pf k φ → k ≤ B → φ.interp) := by
  intro B
  have h := wv_sound_upto (fun _ _ => False) (fun _ _ => False)
    (fun _ _ h => h)
    (fun _ _ _ hT _ => (hT.elim id id).elim)
    (fun _ _ hT _ => hT.elim id id)
    (fun _ _ _ _ _ _ hT _ => hT.elim id id)
    (fun _ _ _ hT _ => hT.elim id id)
    (fun _ _ _ _ _ _ hT _ => hT.elim id id)
    (fun _ _ _ hT => hT)
    (fun _ _ _ hT => hT)
    (fun _ _ _ _ _ _ _ hT _ _ => (hT.elim id id).elim)
    (fun _ _ _ _ _ _ _ hT _ => (hT.elim id id).elim)
    (fun _ _ _ h => h)
    (fun _ _ _ h => h)
    B
  exact ⟨h.1, fun k φ hp hk => (h.2 k φ hp).1 hk⟩

/-- **Soundness of the play certificate.** A `PlaysProof` yields an actual play (at some
    fuel). Corollary of `sound_upto` at `B := n`. -/
theorem playsProof_sound {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ N, eval N me opponent body = some a :=
  (sound_upto n).1 me opponent body a n h le_rfl

/-- **`AtomProvable_sound` (was an axiom).** A bounded certificate yields a real
    play, hence the atom's `interp` (`∃ n, play n me opponent = some a`). -/
theorem AtomProvable_sound (k : Nat) (φ : Formula) : AtomProvable k φ → φ.interp := by
  rintro ⟨cert, hle⟩
  obtain ⟨N, hN⟩ := playsProof_sound cert
  exact ⟨N, hN⟩

/-- **Soundness of bounded provability: anything provable within a budget is true.**
    Corollary of `sound_upto` at `B := k` (which see for the budget-strong-induction
    structure the `search_f` repair requires). -/
theorem Pf_sound : ∀ k φ, Pf k φ → φ.interp :=
  fun k φ h => (sound_upto k).2 k φ h le_rfl

/-
HOW TO DISCHARGE A `proofSearch k φ = b` GOAL.

The two boolean directions are proved by *opposite* bridges — this asymmetry is
fundamental (Σ₁ vs Π₁), not a stylistic choice:

• `proofSearch k φ = true`  — COMPLETENESS / Σ₁ side. Exhibit a witness.
    For a plays-atom `φ = .plays p q a`: produce a real `play n p q = some a`,
    feed it to `atom_complete_searchfree` (→ `AtomProvable (3 ^ n) φ`; search-free
    bots only), then flip with
    `(proofSearch_spec _ _).2 (Pf.atom …)`. `proofSearch_complete_plays`
    below packages exactly this. For a structural `φ` (e.g. `.eq p p`), use the
    transparency leaf directly (`Pf.eqRefl`). You are *constructing* a proof object.

• `proofSearch k φ = false` — SOUNDNESS side, by refutation. You CANNOT exhibit
    "a proof that no proof exists" (that is Π₁); instead rule out `true` via its
    semantic consequence. Canonical pattern:
      cases h : proofSearch k φ with
      | true  => exact absurd (proofSearch_sound _ _ h) (interp_…_false …)
      | false => rfl
    i.e. if it were `true`, `proofSearch_sound` would force `φ.interp` (the bot
    would actually play that), which a computed fact (`interp_…_false`) refutes.

Mnemonic: `= true` builds a proof (atom_complete_searchfree / a transparency leaf);
`= false` destroys a hypothetical one (proofSearch_sound + contradiction). The single
place these collided was the false-guard branch: the old `atom_complete_false_guard`
axiom lived there until it was machine-checked INCONSISTENT and deleted (2026-07-03).
The sound replacement is the `search_f` floor — else-play certificates exist only
from a Σ₁ refutation of the guard, at the full failed budget (`Base/AtomCerts`,
`Base/Exclusion`).
-/

-- Soundness of the proof-search oracle: the `Bool` reflection of `Pf_sound`.
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp :=
  fun k φ hk => Pf_sound k φ ((proofSearch_spec k φ).1 hk)

/-- Completeness of bounded proof search for SEARCH-FREE plays-atoms (the constructive
    fragment; the unrestricted form fell with the inconsistent axiom — a failed-search
    else-play is provable only above its floor, an anti-diagonal one not at all). -/
theorem proofSearch_complete_plays :
    ∀ p q a, p.hasSearch = false → q.hasSearch = false →
      (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a hp hq ⟨n, hn⟩
  exact ⟨3 ^ n, (proofSearch_spec _ (.plays p q a)).2
    (Pf.atom (atom_complete_searchfree p q a n hp hq hn))⟩

-- Monotonicity in proof-search budget: the Bool reflection of `Pf_mono`
-- (which see — every rule self-weakens in its output budget under transcript cost).
theorem proofSearch_monotone :
    ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true :=
  fun _k₁ _k₂ φ hk h1 =>
    (proofSearch_spec _ φ).2 (Pf_mono ((proofSearch_spec _ φ).1 h1) hk)


/-- **Bounded GL axiom 4 / necessitation** (`□_k φ → □_K □_k φ`), HBL D2 — NOW A THEOREM
    (was the axiom `box_provable`). If `φ` is provable within budget `k`, then that fact
    `□_k φ` is itself provable, at the output budget `K = (.box k φ).size` (≤ that bound).
    Discharged constructively by the `Pf.boxIntro` constructor (ProofSystem.lean): the
    conclusion `□_k φ` is built directly from the premise `Pf k φ`, with the size bound
    `(.box k φ).size ≤ K` met by `Nat.le_refl`. Sound + safe — see the `boxIntro` doc. -/
theorem box_provable (k : Nat) (φ : Formula) (h : Pf k φ) :
    ∃ K, K ≤ k + (Formula.box k φ).size ∧ Pf K (.box k φ) :=
  ⟨k + (Formula.box k φ).size, Nat.le_refl _, Pf.boxIntro k _ φ h (Nat.le_refl _)⟩

/-- **Object-level bounded Σ₁-completeness for play-atoms** (the conditional, kernel-checked
    THEOREM). When the play actually happens within `fuel` steps AND the budget `k` fits a
    certificate (`atom_cost fuel ≤ k`), the object implication `(p plays a vs q) → □_k (p plays a vs q)`
    is provable at `K`. Built from the certificate (→ `Pf k atom`),
    `boxIntro` (→ the box), and `weakenImpl` (→ the implication). The CERTIFICATE premise
    keeps it on the sound Σ₁ side: bounded Σ₁-completeness, NOT the GL-excluded
    converse-necessitation `φ → □φ`. (Historical note: the witness-free form was once the
    axiom `atom_box_provable_impl`, removed as unsound; this conditional theorem and the
    `atomBoxImpl` constructor are its sound content.) -/
theorem atom_box_provable_impl_sound (k K : Nat) (p q : Prog) (a : Action)
    (hatom : AtomProvable k (.plays p q a))
    (hK : k + (Formula.box k (.plays p q a)).size
          + (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ K) :
    Pf K (.impl (.plays p q a) (.box k (.plays p q a))) := by
  -- Under transcript cost the conclusion can no longer live at the box's own budget `k`
  -- (the implication's proof CONTAINS the box proof, which contains the `k`-certificate);
  -- the output budget `K` pays certificate + box + conclusion.
  have hbox : Pf (k + (Formula.box k (.plays p q a)).size) (.box k (.plays p q a)) :=
    Pf.boxIntro k _ _ (Pf.atom hatom) (Nat.le_refl _)
  exact Pf.weakenImpl (.plays p q a) (.box k (.plays p q a)) _ hbox hK

end PD.BaseTheorems
