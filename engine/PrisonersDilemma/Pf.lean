import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

/-!
# `Pf` — the unified proof-term type (coexistence layer)

ONE `Prop`-valued, budget-indexed proof-term type replacing the `Derivation`(Type) /
`Provable`(Prop) split for PROOF-WRITING, connected to the engine by the EXACT round-trip

    `pf_iff_provable : Pf k φ ↔ Provable k φ`      (at every budget, no slack)

The engine itself is UNCHANGED: `Derivation`/`Provable`/`PlaysProof` stay the semantics
(`proofSearch`, `eval`, the metatheory all speak `Provable`), and everything the engine
knows transfers across the iff for free (`Pf_sound` below; decidability via
`Provable_iff_decFull` ∘ the iff; `proofSearch_spec` likewise). New proofs can be WRITTEN
in `Pf` and SHIPPED as `Provable`. Validated in
`Research/Spikes/unified_pf/PfEngineSpike.lean` (the CIMCIC exclusion and the DupocBot
self-cooperation, both re-proved in `Pf` end-to-end); design history in
`Research/Notes/UNIFIED_PF_SKETCH.md`.

## Why this shape

* **22 constructors vs the engine's 25** (9 `Derivation` + 16 `Provable`): the
  `struct`/`atom` glue is gone (`atom` remains as the sole EXECUTION bridge), and the
  Type/Prop twins collapse — ONE `mp` (was `Derivation.modusPonens` + `Provable.app`),
  ONE `implTrans` (was `Derivation.hypSyll` + `Provable.implTrans`).
* **`Prop` with the budget as an INDEX** (the `PlaysProof` pattern): under transcript
  costs, `Derivation`'s only reason to be `Type`-valued (defining `.size` by structural
  recursion) disappears — the ex-`Derivation` leaves carry their ex-`struct` size gate as
  a side condition (a leaf's size IS its conclusion's size).
* **NON-mutual** (the load-bearing point): `Pf`'s certificate premises (`AtomProvable` in
  `atom`/`atomBoxImpl`/`atomNeg`) are non-recursive occurrences of the already-defined
  mutual block — `PlaysProof.search_t` keeps consuming `Provable`, converted through the
  iff when needed. A standalone inductive gets the NAMED `induction … with` tactic;
  the mutual `Provable` forces raw positional `Provable.rec` (compare
  `cimcic_no_pf_forbidden` in the spike against the engine's
  `cimcic_no_provable_forbidden`).
* `searchThenSearch_t` stays primitive: its then-branch is a `.search`, not a `.const`,
  so `searchBranch` + `mp` cannot derive it.

## Contents

1. `Pf` + `Pf_mono` (budget monotonicity).
2. The round-trip: `deriv_to_pf` (a `Derivation` embeds at exactly its size),
   `pf_of_provable`, `provable_of_pf`, `pf_iff_provable`, `Pf_sound`.
3. The internalized Löb/PBLT engines in `Pf`: `bloeb_engine_pf`, `pblt_engine_pf`,
   `pblt_engine_id_pf` — verbatim ports of `Base/Loeb.lean` (each step's constructor
   renamed; nothing in the chain was `Provable`-specific).

All results rest on Lean's 3 standard axioms only (the iff itself: `[propext]`).
-/

namespace PD

open PD.BaseTheorems

/-! ## 1. The unified proof-term type -/

/-- **`Pf k φ` — "φ has a proof transcript of ≤ k characters", as ONE type.**

Constructor groups (each rule is byte-for-byte the engine rule, minus the glue):
* `atom` — the SOLE execution bridge (was `Provable.atom`; `struct` is gone).
* Source transparency (ex-`Derivation` leaves) — side condition `conclusion.size ≤ k`
  replaces the `struct ⟨d, d.size ≤ k⟩` embedding.
* Logical core — ONE `mp` (at `Provable.app`'s cost, which a `struct`-embedded
  `modusPonens` tree also satisfies exactly), ONE `implTrans`, `weakenImpl`.
* The `Provable`-only rules (searchThenSearch_t, the modal/box tier, the diag fixpoint
  legs, atomNeg) — unchanged, with `Pf` premises where they had `Provable` premises. -/
inductive Pf : Nat → Formula → Prop where
  -- ── the execution bridge ──
  | atom : AtomProvable k φ → Pf k φ
  -- ── source transparency (ex-`Derivation` leaves; side condition = the ex-`struct` gate) ──
  | searchBranch (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .search g ψ (.const a) (.const b)) :
      (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
      Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
  | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
      (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a)).size ≤ k →
      Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                  (.plays me opponent a))
  | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :
      (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                    (.plays me opponent a)).size ≤ k →
      Pf k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                  (.plays me opponent a))
  | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .bot (.search g ψ (.const a) (.const b))) :
      (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
      Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
  | iteBranchSearch_t (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
      (q me opponent : Prog)
      (hme : me = .ite (.sim .opp (.bot z)) a'
                       (.search g ψ (.const c0) (.const c1)) q) :
      (Formula.impl (.plays opponent (.bot z) a')
                    (.impl (.box g (ψ.subst me opponent))
                           (.plays me opponent c0))).size ≤ k →
      Pf k (.impl (.plays opponent (.bot z) a')
                  (.impl (.box g (ψ.subst me opponent))
                         (.plays me opponent c0)))
  | eqRefl (p : Prog) :
      (Formula.eq p p).size ≤ k → Pf k (.eq p p)
  | eqNeg (p q : Prog) (hne : p ≠ q) :
      (Formula.neg (.eq p q)).size ≤ k → Pf k (.neg (.eq p q))
  -- ── logical core: ONE modus ponens, ONE transitivity ──
  | mp (m₁ m₂ : Nat) (φ α : Formula) :
      Pf m₁ (.impl φ α) → Pf m₂ φ → m₁ + m₂ + α.size ≤ k → Pf k α
  | implTrans (φ ψ χ : Formula) (a b : Nat) :
      Pf a (.impl φ ψ) → Pf b (.impl ψ χ) →
      a + b + (Formula.impl φ χ).size ≤ k → Pf k (.impl φ χ)
  | weakenImpl (φ ψ : Formula) (m : Nat) :
      Pf m ψ → m + (Formula.impl φ ψ).size ≤ k → Pf k (.impl φ ψ)
  | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
      (q me opponent : Prog)
      (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
      Pf m (ψ₂.subst me opponent) → m ≤ k₂ →
      c_guard k₂ +
        (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
      Pf k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
  -- ── modal / box tier (siblings now, not a separate type) ──
  | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
      AtomProvable kBox (.plays p q a) →
      kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
      Pf k (.impl (.plays p q a) (.box kBox (.plays p q a)))
  | boxIntro (kIn K : Nat) (φ : Formula) :
      Pf kIn φ →
      kIn + (Formula.box kIn φ).size ≤ K →
      Pf K (.box kIn φ)
  | axK (a b c m K : Nat) (φ α : Formula) :
      Pf m (.box a (.impl φ α)) →
      a + b + α.size ≤ c →
      m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
      Pf K (.impl (.box b φ) (.box c α))
  | box4 (a b K : Nat) (φ : Formula) :
      a + (Formula.box a φ).size ≤ b →
      (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
      Pf K (.impl (.box a φ) (.box b (.box a φ)))
  | diagF (pm fb g K : Nat) (tgt : Formula) :
      Pf pm (.impl (.box fb tgt) tgt) →
      pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
      Pf K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
  | diagB (pm fb g K : Nat) (tgt : Formula) :
      Pf pm (.impl (.box fb tgt) tgt) →
      pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
      Pf K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
  | axKf (a b c K : Nat) (φ α : Formula) :
      a + b + α.size ≤ c →
      (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
      Pf K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
  | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
      Pf m₁ (.impl φ (.impl ψ χ)) → Pf m₂ (.impl φ ψ) →
      m₁ + m₂ + (Formula.impl φ χ).size ≤ K → Pf K (.impl φ χ)
  | boxMono (a b K : Nat) (φ : Formula) :
      a ≤ b →
      (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
      Pf K (.impl (.box a φ) (.box b φ))
  | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
      AtomProvable m (.plays p q b) → b ≠ aN →
      m + (Formula.neg (.plays p q aN)).size ≤ k →
      Pf k (.neg (.plays p q aN))

/-- Budget monotonicity (same one-liner-per-arm shape as `Provable_mono`). -/
theorem Pf_mono : ∀ {k₁ : Nat} {φ : Formula}, Pf k₁ φ →
    ∀ {k₂ : Nat}, k₁ ≤ k₂ → Pf k₂ φ := by
  intro k₁ φ h k₂ hk
  cases h with
  | atom hatom => exact .atom (atom_monotone k₁ k₂ φ hk hatom)
  | searchBranch g ψ a b me opponent hme hle =>
      exact .searchBranch g ψ a b me opponent hme (Nat.le_trans hle hk)
  | simStep me p q opponent a hme hle =>
      exact .simStep me p q opponent a hme (Nat.le_trans hle hk)
  | botSimStep me p q opponent a hme hle =>
      exact .botSimStep me p q opponent a hme (Nat.le_trans hle hk)
  | botSearchStep g ψ a b me opponent hme hle =>
      exact .botSearchStep g ψ a b me opponent hme (Nat.le_trans hle hk)
  | iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle =>
      exact .iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme (Nat.le_trans hle hk)
  | eqRefl p hle => exact .eqRefl p (Nat.le_trans hle hk)
  | eqNeg p q hne hle => exact .eqNeg p q hne (Nat.le_trans hle hk)
  -- (`cases` unifies the constructor's `α` with the goal index `φ` and REORDERS the
  -- remaining fields, so bind them by display position via `rename_i`)
  | mp =>
      rename_i m₁ m₂ φ' h2 h1 hle
      exact .mp m₁ m₂ φ' φ h1 h2 (Nat.le_trans hle hk)
  | implTrans φ' ψ χ a b h1 h2 hle =>
      exact .implTrans φ' ψ χ a b h1 h2 (Nat.le_trans hle hk)
  | weakenImpl φ' ψ m hψ hle => exact .weakenImpl φ' ψ m hψ (Nat.le_trans hle hk)
  | searchThenSearch_t k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle =>
      exact .searchThenSearch_t k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk
        (Nat.le_trans hle hk)
  | atomBoxImpl kBox p q a hatom hle =>
      exact .atomBoxImpl kBox p q a hatom (Nat.le_trans hle hk)
  | boxIntro kIn K φ' hprem hle => exact .boxIntro kIn k₂ φ' hprem (Nat.le_trans hle hk)
  | axK a b c m K φ' α hprem hgate hle =>
      exact .axK a b c m k₂ φ' α hprem hgate (Nat.le_trans hle hk)
  | box4 a b K φ' hgate hle => exact .box4 a b k₂ φ' hgate (Nat.le_trans hle hk)
  | diagF pm fb g K tgt hgate hle => exact .diagF pm fb g k₂ tgt hgate (Nat.le_trans hle hk)
  | diagB pm fb g K tgt hgate hle => exact .diagB pm fb g k₂ tgt hgate (Nat.le_trans hle hk)
  | axKf a b c K φ' α hgate hle => exact .axKf a b c k₂ φ' α hgate (Nat.le_trans hle hk)
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle =>
      exact .impS2 φ' ψ χ m₁ m₂ k₂ h1 h2 (Nat.le_trans hle hk)
  | boxMono a b K φ' hab hle => exact .boxMono a b k₂ φ' hab (Nat.le_trans hle hk)
  | atomNeg p q b aN m hatom hne hle =>
      exact .atomNeg p q b aN m hatom hne (Nat.le_trans hle hk)

/-! ## 2. The round-trip -/

/-- Every `Derivation` embeds at EXACTLY its own size: `Pf d.size φ`. The leaves land on
    their `Pf` twins (leaf size = conclusion size); `modusPonens`/`hypSyll` land on
    `mp`/`implTrans`, whose cost shape (`m₁ + m₂ + conclusion-ish.size`) IS the transcript
    size of the corresponding tree. -/
theorem deriv_to_pf : ∀ {φ : Formula} (d : Derivation φ), Pf d.size φ := by
  intro φ d
  induction d with
  | modusPonens φ' ψ d1 d2 ih1 ih2 =>
      exact .mp _ _ φ' ψ ih1 ih2 (by simp [Derivation.size])
  | hypSyll φ' ψ χ d1 d2 ih1 ih2 =>
      exact .implTrans φ' ψ χ _ _ ih1 ih2 (by simp [Derivation.size])
  | searchBranch g ψ a b me opponent hme =>
      exact .searchBranch g ψ a b me opponent hme (by simp [Derivation.size])
  | simStep me p q opponent a hme =>
      exact .simStep me p q opponent a hme (by simp [Derivation.size])
  | botSimStep me p q opponent a hme =>
      exact .botSimStep me p q opponent a hme (by simp [Derivation.size])
  | botSearchStep g ψ a b me opponent hme =>
      exact .botSearchStep g ψ a b me opponent hme (by simp [Derivation.size])
  | iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme =>
      exact .iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme (by simp [Derivation.size])
  | eqRefl p => exact .eqRefl p (by simp [Derivation.size])
  | eqNeg p q hne => exact .eqNeg p q hne (by simp [Derivation.size])

/-- `Provable k φ → Pf k φ` — the LAST hand-written `Provable.rec`. Same 26-minor-premise
    positional style as the engine's exclusion proofs; the `struct` arm routes through
    `deriv_to_pf` + `Pf_mono`, every other arm is the same-named `Pf` constructor with the
    IH plugged in. -/
theorem pf_of_provable : ∀ {k : Nat} {φ : Formula}, Provable k φ → Pf k φ := by
  intro k φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun k φ _ => Pf k φ)
    -- PlaysProof arms (9) + AtomProvable.mk (1): motive is `True`.
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    -- struct: the ONE arm that changes shape — embed the Derivation, relax to the budget.
    (fun {_k} {_φ} hd => hd.elim fun d hsz => Pf_mono (deriv_to_pf d) hsz)
    -- atom
    (fun hatom _ => Pf.atom hatom)
    -- weakenImpl
    (fun φ' ψ m _hψ hle ih => Pf.weakenImpl φ' ψ m ih hle)
    -- searchThenSearch_t
    (fun k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _hprud hmk hle ih =>
      Pf.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle)
    -- implTrans
    (fun φ' ψ χ a b _h1 _h2 hle ih1 ih2 => Pf.implTrans φ' ψ χ a b ih1 ih2 hle)
    -- atomBoxImpl
    (fun kBox p q a hatom hle _ => Pf.atomBoxImpl kBox p q a hatom hle)
    -- boxIntro
    (fun kIn K φ' _hprem hle ih => Pf.boxIntro kIn K φ' ih hle)
    -- app → the merged mp
    (fun _k m₁ m₂ φ' α _h1 _h2 hle ih1 ih2 => Pf.mp m₁ m₂ φ' α ih1 ih2 hle)
    -- axK
    (fun a b c m K φ' α _hprem hgate hle ih => Pf.axK a b c m K φ' α ih hgate hle)
    -- box4
    (fun a b K φ' hgate hsz => Pf.box4 a b K φ' hgate hsz)
    -- diagF
    (fun pm fb g K tgt _hgate hle ih => Pf.diagF pm fb g K tgt ih hle)
    -- diagB
    (fun pm fb g K tgt _hgate hle ih => Pf.diagB pm fb g K tgt ih hle)
    -- axKf
    (fun a b c K φ' α hgate hsz => Pf.axKf a b c K φ' α hgate hsz)
    -- impS2
    (fun φ' ψ χ m₁ m₂ K _h1 _h2 hle ih1 ih2 => Pf.impS2 φ' ψ χ m₁ m₂ K ih1 ih2 hle)
    -- boxMono
    (fun a b K φ' hab hsz => Pf.boxMono a b K φ' hab hsz)
    -- atomNeg
    (fun p q b aN m hatom hne hle _ => Pf.atomNeg p q b aN m hatom hne hle)
    h

/-- `Pf k φ → Provable k φ` — a plain NAMED induction (`Pf` is standalone). Leaves
    re-enter through `struct` at the same budget; `mp`/`implTrans` land on
    `app`/`implTrans`; everything else is the same-named constructor. -/
theorem provable_of_pf : ∀ {k : Nat} {φ : Formula}, Pf k φ → Provable k φ := by
  intro k φ h
  induction h with
  | atom hatom => exact .atom hatom
  | searchBranch g ψ a b me opponent hme hle =>
      exact .struct ⟨.searchBranch g ψ a b me opponent hme, by simpa [Derivation.size] using hle⟩
  | simStep me p q opponent a hme hle =>
      exact .struct ⟨.simStep me p q opponent a hme, by simpa [Derivation.size] using hle⟩
  | botSimStep me p q opponent a hme hle =>
      exact .struct ⟨.botSimStep me p q opponent a hme, by simpa [Derivation.size] using hle⟩
  | botSearchStep g ψ a b me opponent hme hle =>
      exact .struct ⟨.botSearchStep g ψ a b me opponent hme, by simpa [Derivation.size] using hle⟩
  | iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle =>
      exact .struct ⟨.iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme,
        by simpa [Derivation.size] using hle⟩
  | eqRefl p hle => exact .struct ⟨.eqRefl p, by simpa [Derivation.size] using hle⟩
  | eqNeg p q hne hle => exact .struct ⟨.eqNeg p q hne, by simpa [Derivation.size] using hle⟩
  | mp m₁ m₂ φ' α _h1 _h2 hle ih1 ih2 => exact .app _ m₁ m₂ φ' α ih1 ih2 hle
  | implTrans φ' ψ χ a b _h1 _h2 hle ih1 ih2 => exact .implTrans φ' ψ χ a b ih1 ih2 hle
  | weakenImpl φ' ψ m _hψ hle ih => exact .weakenImpl φ' ψ m ih hle
  | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme _hprud hmk hle ih =>
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme ih hmk hle
  | atomBoxImpl kBox p q a hatom hle => exact .atomBoxImpl kBox p q a hatom hle
  | boxIntro kIn K φ' _hprem hle ih => exact .boxIntro kIn K φ' ih hle
  | axK a b c m K φ' α _hprem hgate hle ih => exact .axK a b c m K φ' α ih hgate hle
  | box4 a b K φ' hgate hsz => exact .box4 a b K φ' hgate hsz
  | diagF pm fb g K tgt _hgate hle ih => exact .diagF pm fb g K tgt ih hle
  | diagB pm fb g K tgt _hgate hle ih => exact .diagB pm fb g K tgt ih hle
  | axKf a b c K φ' α hgate hsz => exact .axKf a b c K φ' α hgate hsz
  | impS2 φ' ψ χ m₁ m₂ K _h1 _h2 hle ih1 ih2 => exact .impS2 φ' ψ χ m₁ m₂ K ih1 ih2 hle
  | boxMono a b K φ' hab hsz => exact .boxMono a b K φ' hab hsz
  | atomNeg p q b aN m hatom hne hle => exact .atomNeg p q b aN m hatom hne hle

/-- **The transfer theorem** — exact at every budget, both directions. Everything the
    engine knows about `Provable` (soundness, decidability, `proofSearch_spec`, …) is
    available to `Pf`, and every `Pf`-built proof is an engine proof. -/
theorem pf_iff_provable {k : Nat} {φ : Formula} : Pf k φ ↔ Provable k φ :=
  ⟨provable_of_pf, pf_of_provable⟩

/-- Soundness, free through the iff. -/
theorem Pf_sound {k : Nat} {φ : Formula} (h : Pf k φ) : φ.interp :=
  Provable_sound k φ (provable_of_pf h)

/-! ## 3. The internalized Löb / PBLT engines, in `Pf`

Verbatim ports of `Base/Loeb.lean` (`bloeb_engine`/`pblt_engine`/`pblt_engine_id`): each
step's constructor renamed (`Provable.• ↦ Pf.•`, `app ↦ mp`, `Provable_mono ↦ Pf_mono`),
all side-conditions untouched. Nothing in the chain was `Provable`-specific — the box
rules really are siblings of the structural rules. -/

/-- `bloeb_engine`, unified: bounded Löb inside `Pf` from the tight premise
    `Pf pm (□_fb φ → φ)`. -/
theorem bloeb_engine_pf (φ : Formula) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ K : Nat)
    (hLoeb : Pf pm (.impl (.box fb φ) φ))
    (H1 : pm + (Formula.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)).size ≤ c₁)
    (H2 : pm + (Formula.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)).size ≤ c₂)
    (H3 : c₁ ≤ n₁)
    (H4 : n₁ + (Formula.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))).size ≤ c₃)
    (H5 : n₁ + g + (Formula.impl (.box g (.diag g φ)) φ).size ≤ n₃)
    (H6 : (Formula.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
            (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))).size ≤ c₄)
    (H7 : c₄ + c₃ + (Formula.impl (.box g (.diag g φ))
            (.box n₃ (.impl (.box g (.diag g φ)) φ))).size ≤ c₅)
    (H8 : n₃ + n₄ + φ.size ≤ n₅)
    (H9 : (Formula.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₆)
    (H10 : g + (Formula.box g (.diag g φ)).size ≤ n₄)
    (H11 : (Formula.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))).size ≤ c₇)
    (H12 : c₅ + c₆ + (Formula.impl (.box g (.diag g φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₈)
    (H13 : c₈ + c₇ + (Formula.impl (.box g (.diag g φ)) (.box n₅ φ)).size ≤ c₉)
    (H14 : n₅ ≤ fb)
    (H15 : (Formula.impl (.box n₅ φ) (.box fb φ)).size ≤ c₁₀)
    (H16 : c₉ + c₁₀ + (Formula.impl (.box g (.diag g φ)) (.box fb φ)).size ≤ c₁₁)
    (H17 : c₁₁ + pm + (Formula.impl (.box g (.diag g φ)) φ).size ≤ c₁₂)
    (H18 : c₂ + c₁₂ + (Formula.diag g φ).size ≤ c₁₃)
    (H19 : c₁₃ ≤ g)
    (H20 : g + (Formula.box g (.diag g φ)).size ≤ c₁₄)
    (H21 : c₁₂ + c₁₄ + φ.size ≤ K) :
    Pf K φ := by
  have legF : Pf c₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)) :=
    Pf.diagF pm fb g c₁ φ hLoeb H1
  have legB : Pf c₂ (.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)) :=
    Pf.diagB pm fb g c₂ φ hLoeb H2
  have hnec : Pf c₃ (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))) :=
    Pf.boxIntro n₁ c₃ _ (Pf_mono legF H3) H4
  have hK1 : Pf c₄ (.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
      (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))) :=
    Pf.axKf n₁ g n₃ c₄ (.diag g φ) (.impl (.box g (.diag g φ)) φ) H5 H6
  have h2 : Pf c₅ (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ))) :=
    Pf.mp c₄ c₃ _ _ hK1 hnec H7
  have hK2 : Pf c₆ (.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    Pf.axKf n₃ n₄ n₅ c₆ (.box g (.diag g φ)) φ H8 H9
  have hfour : Pf c₇ (.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))) :=
    Pf.box4 g n₄ c₇ (.diag g φ) H10 H11
  have h4 : Pf c₈ (.impl (.box g (.diag g φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    Pf.implTrans _ _ _ c₅ c₆ h2 hK2 H12
  have h6 : Pf c₉ (.impl (.box g (.diag g φ)) (.box n₅ φ)) :=
    Pf.impS2 _ _ _ c₈ c₇ c₉ h4 hfour H13
  have hmono : Pf c₁₀ (.impl (.box n₅ φ) (.box fb φ)) :=
    Pf.boxMono n₅ fb c₁₀ φ H14 H15
  have h6' : Pf c₁₁ (.impl (.box g (.diag g φ)) (.box fb φ)) :=
    Pf.implTrans _ _ _ c₉ c₁₀ h6 hmono H16
  have hE : Pf c₁₂ (.impl (.box g (.diag g φ)) φ) :=
    Pf.implTrans _ _ _ c₁₁ pm h6' hLoeb H17
  have hF : Pf c₁₃ (.diag g φ) := Pf.mp c₂ c₁₂ _ _ legB hE H18
  have hG : Pf c₁₄ (.box g (.diag g φ)) :=
    Pf.boxIntro g c₁₄ _ (Pf_mono hF H19) H20
  exact Pf.mp c₁₂ c₁₄ _ _ hE hG H21

/-- `pblt_engine`, unified — T0's instantiation as multiples of one O(log k) unit. -/
theorem pblt_engine_pf (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + (φ k).size + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, bloeb_engine_pf (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [numCost, Formula.size]); omega

/-- `pblt_engine_id`, unified — the consumer-facing shape every bot theorem uses. -/
theorem pblt_engine_id_pf (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k) := by
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le 1646592 16449536
  obtain ⟨k₂, hk₂⟩ := pblt_engine_pf φ id pm (max k₁ Ksz)
    (fun k hk => hLoeb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    (by
      intro k hk
      have h1 := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
      have h2 := hφ k
      have h3 := hpm k
      show 8192 * (pm k + (φ k).size + Nat.log2 (id k) + 8) ≤ id k
      simp only [id]
      omega)
  exact ⟨k₂, hk₂⟩

end PD
