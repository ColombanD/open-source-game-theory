import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms


open Classical

open PD
open PD.Axioms
namespace PD.BaseTheorems

/-- `c_guard` (the cost of writing the budget numeral `k` in a proof transcript)
    is monotone: a larger `k` takes at least as many characters to write.
    Needed for `atom_cost_mono`. Now a *theorem* (was an axiom): with the concrete
    `c_guard k = Nat.log2 k + 1` (Derivation.lean), monotonicity is `Nat.log2`'s. -/
theorem c_guard_mono : ∀ {a b : Nat}, a ≤ b → c_guard a ≤ c_guard b := by
  intro a b h
  simp only [c_guard, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- `atom_cost` is monotone in fuel, so bot proofs can lift a small-fuel atom to a
    larger working budget via `proofSearch_monotone`. -/
theorem atom_cost_mono {a b : Nat} (h : a ≤ b) : atom_cost a ≤ atom_cost b := by
  unfold atom_cost
  exact Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.add_le_add_left (c_guard_mono h) _) h) _

/-- σ₁-completeness for atoms: every `fuel`-step play has an `AtomProvable`
    certificate at budget `atom_cost fuel`. Constructive when a `PlaysProof`
    exists; falls back to `atom_complete_false_guard` otherwise.
    This means that if p plays a against q within fuel steps,
    then S can prove that fact within the budget -/
theorem atom_complete :
    ∀ p q a fuel, play fuel p q = some a →
      AtomProvable (atom_cost fuel) (.plays p q a) := by
  intro p q a fuel h
  by_cases hc : ∃ _ : PlaysProof p q p a (atom_cost fuel), True
  · obtain ⟨cert, _⟩ := hc; exact .mk cert (Nat.le_refl _)
  · exact atom_complete_false_guard p q a fuel h hc

/-- The bridge `proofSearch ↔ Provable` is now a theorem, not an axiom. -/
theorem proofSearch_spec (k : Nat) (φ : Formula) :
    proofSearch k φ = true ↔ Provable k φ := by
  unfold proofSearch; exact decide_eq_true_iff

-- Soundness of the structural rules. Each `Derivation` yields a true
-- formula. The interesting cases (`searchBranch`, `simStep`) are exactly the
-- semantic content the old transparency axioms asserted for free.
--
-- Declared as `_root_.PD.Derivation.sound` (absolute name) so it lands in
-- the `PD.Derivation` namespace and dot notation `d.sound` on a
-- `d : PD.Derivation φ` resolves it — rather than being prefixed by the
-- ambient `PD.BaseTheorems` namespace.
theorem _root_.PD.Derivation.sound : ∀ {φ}, Derivation φ → φ.interp := by
  intro φ d
  induction d with
  | modusPonens φ ψ _ _ ih1 ih2 =>
      -- `.impl`'s interp is Lean implication, so this is just function application.
      exact ih1 ih2
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
  | botSimStep me p q opponent a hme =>
      -- `me = .bot (.sim p q)`: `eval` unwraps the `.bot` (one step, `me` stays the
      -- player), then runs the `.sim`. So `me` plays `a` iff its substituted body
      -- plays `a`. Witness fuel `n + 2`: one `.bot` unwrap, one `.sim` step.
      subst hme
      intro h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 2, by
        show eval (n+2) (.bot (.sim p q)) opponent (.bot (.sim p q)) = some a
        simp only [eval]; exact hn⟩
  | botSearchStep k ψ a b me opponent hme =>
      -- `me = .bot (.search k ψ (.const a) (.const b))`: `eval` unwraps the `.bot`
      -- (one step, `me` stays the player), then runs the `.search`. A provable
      -- guard makes `eval` take the `.const a` branch, so `me` plays `a`. Witness
      -- fuel `3`: one `.bot` unwrap, one `.search` step, one `.const a` step.
      subst hme
      intro hguard
      have hps : proofSearch k
          (ψ.subst (.bot (.search k ψ (.const a) (.const b))) opponent) = true :=
        (proofSearch_spec _ _).2 hguard
      exact ⟨3, by simp only [play, eval, hps, if_true]⟩
  | hypSyll φ ψ χ _ _ ih1 ih2 =>
      exact fun h => ih2 (ih1 h)
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme =>
      -- `me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q`.
      -- Guard `.sim .opp (.bot z)` is frame-independent: it equals `opponent` vs
      -- `.bot z` (`eval_sim_opp_bot_of_play`). Once the guard fires (`hb` gives it
      -- plays `a'`, so `a' == a'` selects the then-branch), the inner `.search`
      -- runs in-frame and consults `proofSearch k (ψ.subst me opponent)`, which the
      -- box premise reflects to `true` (`proofSearch_spec`), landing on `.const c0`.
      subst hme
      rintro ⟨nb, hb⟩ hbox
      have hps : proofSearch k (ψ.subst
          (.ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q)
          opponent) = true := (proofSearch_spec _ _).2 hbox
      -- `nb ≥ 1`: a fuel-`0` play is `none ≠ some a'`, so write `nb = m + 1`. The
      -- extra step lets the inner `.search`'s `.const c0` branch evaluate.
      obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := by
        cases nb with
        | zero => simp [play, eval] at hb
        | succ m => exact ⟨m, rfl⟩
      -- `.sim .opp (.bot z)` guard reduces (one fuel step; `subst` sends `.opp`↦
      -- opponent, leaves `.bot z` closed) to `eval (m+1) opponent z.bot opponent`,
      -- which is `play (m+1) opponent z.bot = some a'` (`hb`), frame-independent of
      -- `me`. Same reduction `eval_sim_opp_bot_of_play` performs, inlined since
      -- that helper lives downstream of this file.
      have hguard : eval (m + 1) opponent (.bot z) opponent = some a' := hb
      have hrefl : (a' == a') = true := by cases a' <;> rfl
      -- Witness fuel `m + 3`: `.ite` step (→ m+2) evaluates the guard `.sim`
      -- (→ m+1, matching `hguard`); the then-branch `.search` and its `.const c0`
      -- run at `m+1 ≥ 1`.
      refine ⟨m + 1 + 1 + 1, ?_⟩
      show eval (m + 1 + 1 + 1) _ opponent _ = some c0
      -- `.ite` step then `.sim` guard step, exposing `hguard`'s LHS exactly.
      rw [eval]
      simp only [bind, Option.bind]
      rw [show eval (m + 1 + 1) ((Prog.opp.sim z.bot).ite a'
              (.search k ψ (.const c0) (.const c1)) q) opponent (.sim .opp (.bot z))
            = eval (m + 1) opponent (.bot z) opponent from rfl, hguard]
      -- guard fired; `a' == a'` (`hrefl`) selects the `.search`, `hps` makes it
      -- take `.const c0`.
      simp only [hrefl, hps, if_pos, eval]
  | eqRefl p =>
      -- `.eq p p` interprets as `p = p`, which is `rfl`.
      rfl

/-- A derivation of size `m` witnesses `proofSearch m φ = true` (structural
    disjunct of `Provable`). -/
theorem derives {φ : Formula} (d : Derivation φ) : ∃ m, proofSearch m φ = true :=
  ⟨d.size, (proofSearch_spec _ _).2 (Provable.struct ⟨d, Nat.le_refl _⟩)⟩

/-- The **K axiom** of GL, budget-respecting: from a derivation of `φ → ψ` of
    size `≤ n` and one of `φ` of size `≤ m`, `ψ` is provable within `n + m + 1`.
    With the character-faithful `Derivation.size = conclusion.size`, the combined
    derivation's size is `ψ.size ≤ (φ → ψ).size ≤ n ≤ n + m + 1`. Lifts the
    `modusPonens` constructor to the budgeted `Provable` level. -/
theorem K_provable (n m : Nat) (φ ψ : Formula)
    (dImp : Derivation (.impl φ ψ)) (hI : dImp.size ≤ n)
    (dφ : Derivation φ) (_hF : dφ.size ≤ m) :
    Provable (n + m + 1) ψ := by
  -- dImp.size = (φ → ψ).size = φ.size + ψ.size + 1, so ψ.size ≤ n ≤ n+m+1.
  exact Provable.struct ⟨.modusPonens φ ψ dImp dφ, by
    simp only [Derivation.size] at *; simp [Formula.size] at hI; omega⟩

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


/-! ## Atom certificate soundness (`PlaysProof` → real play)

The atom-side axioms `atom_monotone` and `AtomProvable_sound` are now THEOREMS:
`AtomProvable` is the constructive `PlaysProof` certificate, so monotonicity is
just relaxing its cost bound, and soundness is "a certificate yields a real
play." (Only `atom_complete`'s false-guard *completeness* stays axiomatic — see
`Axioms.lean`.) -/

/-- Fuel monotonicity of `eval`: a successful run survives more fuel. Standard;
    by strong induction on the fuel, generalized over all of `me`/`opp`/`body`
    (the `.sim` case swaps players). -/
theorem eval_mono :
    ∀ (N : Nat) (me opponent body : Prog) (a : Action),
      eval N me opponent body = some a → eval (N+1) me opponent body = some a := by
  intro N
  induction N with
  | zero => intro me opponent body a h; simp [eval] at h
  | succ n ih =>
    intro me opponent body a h
    cases body with
    | const c => simpa [eval] using h
    | self => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | opp => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | bot p => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | sim p q => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | ite b a' p q =>
        rw [eval] at h ⊢
        cases hb : eval n me opponent b with
        | none => simp [hb] at h
        | some r =>
            rw [hb] at h; rw [ih me opponent b r hb]
            simp only [bind, Option.bind] at h ⊢
            by_cases hr : (r == a') = true
            · rw [if_pos hr] at h ⊢; exact ih _ _ _ _ h
            · rw [if_neg hr] at h ⊢; exact ih _ _ _ _ h
    | search k φ p q =>
        rw [eval] at h ⊢
        by_cases hg : proofSearch k (φ.subst me opponent) = true
        · rw [if_pos hg] at h ⊢; exact ih _ _ _ _ h
        · rw [if_neg hg] at h ⊢; exact ih _ _ _ _ h

/-- `≤`-form of fuel monotonicity. -/
theorem eval_mono_le {me opponent body : Prog} {a : Action} {N : Nat}
    (h : eval N me opponent body = some a) : ∀ M, N ≤ M → eval M me opponent body = some a := by
  intro M hM
  induction hM with
  | refl => exact h
  | step _ ih => exact eval_mono _ _ _ _ _ ih

/-- **Soundness of the play certificate.** A `PlaysProof` yields an actual play
    (at some fuel). Via `PlaysProof.rec` (`induction` can't handle the mutual
    block); `.ite`/`.search` unify the two child fuels with `eval_mono_le` to
    `max … + 1`. The `.search_t` case reflects its `Provable` guard premise into
    the `proofSearch` the evaluator consults, via `(proofSearch_spec).2`. -/
theorem playsProof_sound {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ N, eval N me opponent body = some a := by
  refine PlaysProof.rec
    (motive_1 := fun me opponent body a _ _ => ∃ N, eval N me opponent body = some a)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?atomMk ?provStruct ?provAtom ?provWeaken
    ?provSearchThenSearch ?provImplTrans ?provAtomBoxImpl ?provBoxIntro ?provApp ?provAxK ?provBox4
    ?provDiagF ?provDiagB ?provAxKf ?provImpS2 h
  case const => exact ⟨1, rfl⟩
  case self => intro me opponent a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case opp => intro me opponent a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case bot => intro me opponent p a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case sim => intro a n me opponent p q _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case ite_t =>
    intro me opponent b r m a' p a n q _ hr _ ihb ihp
    obtain ⟨Nb, hNb⟩ := ihb; obtain ⟨Np, hNp⟩ := ihp
    refine ⟨max Nb Np + 1, ?_⟩
    rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Np)]
    simp only [bind, Option.bind]; rw [if_pos hr]
    exact eval_mono_le hNp _ (Nat.le_max_right Nb Np)
  case ite_f =>
    intro me opponent b r m a' q a n p _ hr _ ihb ihq
    obtain ⟨Nb, hNb⟩ := ihb; obtain ⟨Nq, hNq⟩ := ihq
    refine ⟨max Nb Nq + 1, ?_⟩
    rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Nq)]
    simp only [bind, Option.bind]; rw [if_neg (by simp [hr])]
    exact eval_mono_le hNq _ (Nat.le_max_right Nb Nq)
  case search_t =>
    intro k me opponent p a n φ q hguard _ _ ihp
    obtain ⟨Np, hNp⟩ := ihp
    exact ⟨Np+1, by rw [eval, if_pos ((proofSearch_spec k (φ.subst me opponent)).2 hguard)]; exact hNp⟩
  case atomMk => intros; trivial
  case provStruct => intros; trivial
  case provAtom => intros; trivial
  case provWeaken => intros; trivial
  case provSearchThenSearch => intros; trivial
  case provImplTrans => intros; trivial
  case provAtomBoxImpl => intros; trivial
  case provBoxIntro => intros; trivial
  case provApp => intros; trivial
  case provAxK => intros; trivial
  case provBox4 => intros; trivial
  case provDiagF => intros; trivial
  case provDiagB => intros; trivial
  case provAxKf => intros; trivial
  case provImpS2 => intros; trivial

/-- **`atom_monotone` (was an axiom).** Relaxing the certificate's cost bound. -/
theorem atom_monotone (k₁ k₂ : Nat) (φ : Formula) (hk : k₁ ≤ k₂) :
    AtomProvable k₁ φ → AtomProvable k₂ φ := by
  rintro ⟨cert, hle⟩; exact .mk cert (Nat.le_trans hle hk)

/-- **`AtomProvable_sound` (was an axiom).** A bounded certificate yields a real
    play, hence the atom's `interp` (`∃ n, play n me opponent = some a`). -/
theorem AtomProvable_sound (k : Nat) (φ : Formula) : AtomProvable k φ → φ.interp := by
  rintro ⟨cert, _⟩
  obtain ⟨N, hN⟩ := playsProof_sound cert
  exact ⟨N, hN⟩

-- **Soundness of bounded provability: anything provable within a budget is true.**
-- One arm per `Provable` constructor (grouped as in `Derivation.lean`):
--   • entry points: `struct` (→ `Derivation.sound`), `atom` (→ `AtomProvable_sound`);
--   • implication reasoning: `weakenImpl`/`searchThenSearch_t`/`implTrans` (interp is Lean
--     implication, so these are function composition / the IH on the consequent);
--   • modal/box rules: `atomBoxImpl`/`boxIntro`/`app`/`axK`/`box4` — each interp is `Provable …`
--     (the box clause), discharged from the premise's provability (`app` runs the implication).
-- `induction`/`cases` can't recurse through the mutual block, so we drive it with `Provable.rec`
-- (mirroring `playsProof_sound`); the minor premises are POSITIONAL — all `PlaysProof`/`AtomProvable`
-- arms have motive `True`, then one arm per `Provable` constructor in declaration order.
theorem Provable_sound : ∀ k φ, Provable k φ → φ.interp := by
  intro k φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ φ _ => φ.interp)
    trivial                                   -- const
    (fun _ _ => trivial)                      -- self
    (fun _ _ => trivial)                      -- opp
    (fun _ _ => trivial)                      -- bot
    (fun _ _ => trivial)                      -- sim
    (fun _ _ _ _ _ => trivial)                -- ite_t
    (fun _ _ _ _ _ => trivial)                -- ite_f
    (fun _ _ _ _ => trivial)                  -- search_t
    (fun _ _ _ => trivial)                    -- mk (AtomProvable)
    (fun {k} {φ} hd => by obtain ⟨d, _⟩ := hd; exact d.sound)   -- struct
    (fun {k} {φ} hatom _ => AtomProvable_sound k φ hatom)       -- atom
    -- weakenImpl: `(.impl φ ψ).interp` is `φ.interp → ψ.interp`; the IH
    -- `ih : ψ.interp` (from `Provable m ψ`) discharges it via `fun _ => ih`.
    (fun _φ _ψ _m _hpsi _hmk _hsz ih => fun _ => ih)            -- weakenImpl
    -- searchThenSearch_t: conclusion `(□_{k₁} ψ₁' → me plays c0).interp`, i.e.
    -- `Provable k₁ ψ₁' → ∃ n, play n me opponent = some c0`. Given the box
    -- antecedent (`hbox : Provable k₁ ψ₁'`) and the prudence premise
    -- (`hprud : Provable k₂ ψ₂'`), both reflect to `proofSearch … = true`, so
    -- `eval` runs outer `.search` → inner `.search` → `.const c0`. Witness fuel 3.
    (fun {_k} k₁ k₂ ψ₁ ψ₂ c0 c1 q me opponent hme hprud _hk2 _hsz _ih => by
        subst hme
        intro hbox
        have hps₁ : proofSearch k₁ (ψ₁.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 hbox
        have hps₂ : proofSearch k₂ (ψ₂.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 hprud
        exact ⟨3, by simp only [play, eval, hps₁, hps₂, if_true]⟩)
    -- implTrans: compose the two implications' interps (function composition).
    (fun _φ _ψ _χ _a _b _hab _hbc _hak _hbk _hpsisz _hsz ihab ihbc => fun h => ihbc (ihab h))  -- implTrans
    -- atomBoxImpl: conclusion `(φ → □_k φ).interp`, i.e. `φ.interp → Provable k φ`.
    -- The certificate `hatom : AtomProvable k φ` discharges the consequent directly
    -- (`Provable.atom`), independent of the antecedent — no axiom.
    (fun {_k} _kBox _p _q _a hatom _hsz _ih => fun _ => Provable.atom hatom)  -- atomBoxImpl
    -- boxIntro: conclusion `(□_{kIn} φ).interp` is *definitionally* `Provable kIn φ`,
    -- which is exactly the premise `hprem`. The arm is the identity (`ih : φ.interp`
    -- is unused — we return the stronger provability the premise already carries).
    (fun _kIn _K _φ hprem _hsz _ih => hprem)                                  -- boxIntro
    -- app: conclusion `α.interp`. ihimp : `(φ→α).interp = (φ.interp → α.interp)`;
    -- ihφ : `φ.interp`. Pure function application — NO budget threshold. (binders: k m φ α impl ante mk)
    (fun _k _m _φ _α _himp _hante _hmk ihimp ihante => ihimp ihante)           -- app (k m φ α impl ante m≤k)
    -- axK: conclusion `(□φ → □α).interp = (Provable k φ → Provable k α)`. The IH on the premise
    -- `Provable k (□(φ→α))` is its interp `Provable k (φ→α)` (the held implication proof); apply it
    -- to the hypothetical `Provable k φ` via OBJECT modus ponens `Provable.app`. No budget threshold.
    (fun k _K φ α _himp _hsz ih => (fun hφ => Provable.app k k φ α ih hφ (Nat.le_refl k)))  -- axK
    -- box4: conclusion `(□_kφ → □_k(□_kφ)).interp = (Provable k φ → Provable k (□_kφ))`. Directly:
    -- `boxIntro k k φ hφ hksz` builds `Provable k (□_kφ)` (output budget k, since `(□φ).size ≤ k`).
    (fun k _K φ hksz _hsz =>
      (show Provable k φ → Provable k (.box k φ) from fun hφ => Provable.boxIntro k k φ hφ hksz))  -- box4
    -- diagF: conclusion `(ψ → (□_g ψ → tgt)).interp` where `ψ := .diag g tgt` and
    -- `ψ.interp = (Provable g ψ → tgt.interp)` BY DEFINITION (Dynamics.lean) — the identity.
    (fun _g _K _tgt _hgate _hsz _ih => fun h => h)                             -- diagF
    -- diagB: `((□_g ψ → tgt) → ψ).interp` — the same identity, other direction.
    (fun _g _K _tgt _hgate _hsz _ih => fun h => h)                             -- diagB
    -- axKf: `(□_k(φ→α) → (□_kφ → □_kα)).interp = Provable k (φ→α) → Provable k φ → Provable k α`:
    -- object modus ponens (`Provable.app`), no budget threshold.
    (fun k _K φ α _hsz => fun hab ha => Provable.app k k φ α hab ha (Nat.le_refl k))  -- axKf
    -- impS2: `(φ→χ).interp` from ih₁ : `(φ→(ψ→χ)).interp` and ih₂ : `(φ→ψ).interp` — the
    -- S-combinator, plain function application.
    (fun _φ _ψ _χ _m _K _h1 _h2 _hmk _hsz ih1 ih2 => fun hφ => (ih1 hφ) (ih2 hφ))  -- impS2
    h

/-
HOW TO DISCHARGE A `proofSearch k φ = b` GOAL.

The two boolean directions are proved by *opposite* bridges — this asymmetry is
fundamental (Σ₁ vs Π₁), not a stylistic choice:

• `proofSearch k φ = true`  — COMPLETENESS / Σ₁ side. Exhibit a witness.
    For a plays-atom `φ = .plays p q a`: produce a real `play n p q = some a`,
    feed it to `atom_complete` (→ `AtomProvable (atom_cost n) φ`), then flip with
    `(proofSearch_spec _ _).2 (Provable.atom …)`. `proofSearch_complete_plays`
    below packages exactly this. For a structural `φ` (e.g. `.eq p p`), build the
    `Derivation` and use `Provable.struct`. You are *constructing* a proof object.

• `proofSearch k φ = false` — SOUNDNESS side, by refutation. You CANNOT exhibit
    "a proof that no proof exists" (that is Π₁); instead rule out `true` via its
    semantic consequence. Canonical pattern:
      cases h : proofSearch k φ with
      | true  => exact absurd (proofSearch_sound _ _ h) (interp_…_false …)
      | false => rfl
    i.e. if it were `true`, `proofSearch_sound` would force `φ.interp` (the bot
    would actually play that), which a computed fact (`interp_…_false`) refutes.

Mnemonic: `= true` builds a proof (atom_complete / Derivation); `= false`
destroys a hypothetical one (proofSearch_sound + contradiction). The single place
these collide is `atom_complete`'s false-guard branch — see `atom_complete_false_guard`
in Axioms.lean.
-/

-- Soundness of the proof-search oracle: the `Bool` reflection of `Provable_sound`.
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp :=
  fun k φ hk => Provable_sound k φ ((proofSearch_spec k φ).1 hk)

/-- Completeness of bounded proof search for atomic plays-formulas: a play within
    `fuel` steps is provable within budget `atom_cost fuel`. -/
theorem proofSearch_complete_plays :
∀ p q a, (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a ⟨n, hn⟩
  exact ⟨atom_cost n,
    (proofSearch_spec _ (.plays p q a)).2 (Provable.atom (atom_complete p q a n hn))⟩

-- Monotonicity in proof-search budget: the structural disjunct relaxes its size
-- bound; the `AtomProvable` disjunct carries over by `atom_monotone`.
theorem proofSearch_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true := by
  intro k₁ k₂ φ hk h1
  cases (proofSearch_spec k₁ φ).1 h1 with
  | struct hd => obtain ⟨d, hsz⟩ := hd
                 -- the derivation carries over; only its size bound relaxes `k₁ → k₂`.
                 exact (proofSearch_spec k₂ φ).2
                   (Provable.struct ⟨d, Nat.le_trans hsz hk⟩)
  | atom hatom => exact (proofSearch_spec k₂ φ).2 (Provable.atom (atom_monotone k₁ k₂ φ hk hatom))
  | weakenImpl ψ' χ' m hpsi hmk hsz =>
      -- the conclusion's size bound relaxes from `k₁` to `k₂`; the consequent's
      -- proof and budget bound carry over (transitivity through `k₁ ≤ k₂`).
      exact (proofSearch_spec k₂ _).2
        (Provable.weakenImpl ψ' χ' m hpsi (Nat.le_trans hmk hk) (Nat.le_trans hsz hk))
  | searchThenSearch_t a₁ a₂ ψ₁ ψ₂ c0 c1 q me opponent hme hprud hk2 hsz =>
      -- same as `weakenImpl`: relax the conclusion's size and `k₂` bounds `k₁ → k₂`;
      -- the inner (prudence) proof and `hme` carry over unchanged.
      exact (proofSearch_spec k₂ _).2
        (Provable.searchThenSearch_t a₁ a₂ ψ₁ ψ₂ c0 c1 q me opponent hme hprud
          (Nat.le_trans hk2 hk) (Nat.le_trans hsz hk))
  | implTrans φ ψ χ a b hab hbc hak hbk hpsisz hsz =>
      -- relax the conclusion's size, both leg budgets, and the cut-formula size
      -- bound `k₁ → k₂` (all via transitivity through `k₁ ≤ k₂`).
      exact (proofSearch_spec k₂ _).2
        (Provable.implTrans φ ψ χ a b hab hbc (Nat.le_trans hak hk) (Nat.le_trans hbk hk)
          (Nat.le_trans hpsisz hk) (Nat.le_trans hsz hk))
  | atomBoxImpl kBox p q a hatom hsz =>
      -- the box certificate stays at its own budget `kBox` (untouched by `k₁ → k₂`);
      -- only the conclusion's size bound relaxes from `k₁` to `k₂`.
      exact (proofSearch_spec k₂ _).2
        (Provable.atomBoxImpl kBox p q a hatom (Nat.le_trans hsz hk))
  | boxIntro kIn =>
      -- the inner proof stays at its own budget `kIn`; the conclusion's `size ≤ k₁`
      -- bound relaxes to `size ≤ k₂` (self-weakening), so re-apply `boxIntro` at `k₂`.
      rename_i φ' hprem hsz
      exact (proofSearch_spec k₂ _).2
        (Provable.boxIntro kIn k₂ φ' hprem (Nat.le_trans hsz hk))
  | app =>
      -- object MP at the fixed budget `k₁`; lift each premise `k₁ → k₂` (recursively, via the spec),
      -- then re-apply `app` at `k₂`. Conclusion formula `α` is unchanged by the budget lift.
      -- `app k₁ m`'s conclusion budget `k₁` is FREE (premises at `m ≤ k₁`). Lift `k₁ → k₂` by
      -- re-applying `app` at `k₂` with the SAME premises (unchanged at `m`) and `m ≤ k₁ ≤ k₂`. NO
      -- recursion needed (premises don't move), so termination is preserved.
      -- bound order (read from the goal): `m`, a formula, antecedent proof, `m ≤ k₁`, implication.
      rename_i m _ hante hmk himpl
      exact (proofSearch_spec k₂ _).2
        (Provable.app k₂ m _ _ himpl hante (Nat.le_trans hmk hk))
  | axK kk =>
      -- `axK`'s INNER box budget `kk` is fixed in the CONCLUSION FORMULA `□_{kk}φ → □_{kk}α` — that
      -- formula does NOT change with `k₁ → k₂`. The PROOF budget `K` (separate, was `k₁`) self-weakens
      -- to `k₂`: keep the same premise (inner budget `kk` untouched), relax only the `size ≤ K` bound.
      rename_i φ' α' himp hsz
      exact (proofSearch_spec k₂ _).2
        (Provable.axK kk k₂ φ' α' himp (Nat.le_trans hsz hk))
  | box4 kk =>
      -- `box4`'s inner box budget `kk` is fixed in the conclusion formula `□_{kk}φ → □_{kk}□_{kk}φ`;
      -- the proof budget self-weakens `k₁ → k₂`. Keep the `(□φ).size ≤ kk` guard; relax `size ≤ K`.
      rename_i φ' hksz hsz
      exact (proofSearch_spec k₂ _).2
        (Provable.box4 kk k₂ φ' hksz (Nat.le_trans hsz hk))
  | diagF g =>
      -- fixpoint-leg budgets: the gate proof and the box subscript `g` are fixed in the conclusion
      -- formula; only the `size ≤ K` output bound relaxes `k₁ → k₂` (self-weakening).
      rename_i tgt hgate hsz
      exact (proofSearch_spec k₂ _).2 (Provable.diagF g k₂ tgt hgate (Nat.le_trans hsz hk))
  | diagB g =>
      rename_i tgt hgate hsz
      exact (proofSearch_spec k₂ _).2 (Provable.diagB g k₂ tgt hgate (Nat.le_trans hsz hk))
  | axKf kk =>
      rename_i φ' α' hsz
      exact (proofSearch_spec k₂ _).2 (Provable.axKf kk k₂ φ' α' (Nat.le_trans hsz hk))
  | impS2 φ' ψ' χ' m =>
      rename_i hab hb hmk hsz
      exact (proofSearch_spec k₂ _).2
        (Provable.impS2 φ' ψ' χ' m k₂ hab hb (Nat.le_trans hmk hk) (Nat.le_trans hsz hk))


/-- **Bounded GL axiom 4 / necessitation** (`□_k φ → □_K □_k φ`), HBL D2 — NOW A THEOREM
    (was the axiom `box_provable`). If `φ` is provable within budget `k`, then that fact
    `□_k φ` is itself provable, at the output budget `K = (.box k φ).size` (≤ that bound).
    Discharged constructively by the `Provable.boxIntro` constructor (Derivation.lean): the
    conclusion `□_k φ` is built directly from the premise `Provable k φ`, with the size bound
    `(.box k φ).size ≤ K` met by `Nat.le_refl`. Sound + safe — see the `boxIntro` doc. -/
theorem box_provable (k : Nat) (φ : Formula) (h : Provable k φ) :
    ∃ K, K ≤ (Formula.box k φ).size ∧ Provable K (.box k φ) :=
  ⟨(Formula.box k φ).size, Nat.le_refl _, Provable.boxIntro k _ φ h (Nat.le_refl _)⟩

/-- **Object-level bounded Σ₁-completeness for play-atoms** (the conditional, kernel-checked
    THEOREM). When the play actually happens within `fuel` steps AND the budget `k` fits a
    certificate (`atom_cost fuel ≤ k`), the object implication `(p plays a vs q) → □_k (p plays a vs q)`
    is provable at `k`. Built from `atom_complete` + `atom_monotone` (→ `Provable k atom`),
    `box_provable` (→ `Provable K (□_k atom)`), and `weakenImpl` (→ the implication).

    The threshold `atom_cost fuel ≤ k` keeps it on the sound Σ₁ side: bounded Σ₁-completeness, NOT the
    GL-excluded converse-necessitation `φ → □φ`. (Historical note: the witness-free form was once the
    axiom `atom_box_provable_impl`, removed as unsound; this conditional theorem and the `atomBoxImpl`
    constructor are its sound content.) -/
theorem atom_box_provable_impl_sound (k fuel : Nat) (p q : Prog) (a : Action)
    (hplay : play fuel p q = some a) (hk : atom_cost fuel ≤ k)
    (hsz : (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ k) :
    Provable k (.impl (.plays p q a) (.box k (.plays p q a))) := by
  have hatom : Provable k (.plays p q a) :=
    Provable.atom (atom_monotone (atom_cost fuel) k _ hk (atom_complete p q a fuel hplay))
  obtain ⟨K, hKle, hbox⟩ := box_provable k (.plays p q a) hatom
  -- `hKle : K ≤ (□_k atom).size`, and `hsz` forces `(□_k atom).size < (atom → □_k atom).size ≤ k`,
  -- so `K ≤ k` — exactly the budget bound the now-bounded `weakenImpl` requires.
  have hszbox : (Formula.box k (.plays p q a)).size < (Formula.impl (.plays p q a) (.box k (.plays p q a))).size := by
    simp only [Formula.size]; omega
  have hKk : K ≤ k := Nat.le_trans hKle (Nat.le_trans (Nat.le_of_lt hszbox) hsz)
  exact Provable.weakenImpl (.plays p q a) (.box k (.plays p q a)) K hbox hKk hsz

/-! ### The mutual-Löb corollary — closes the cross-bot cooperation fixpoints

`mutual_loeb` derives the closed Löb premise `□_k φP → φP` that `PBLT` consumes, from the two
object transparency legs (`legPD : □φP → φD`, `legDP : □φD → φP`). It uses ONLY constructors
(`boxIntro`/`axK`/`box4`/`implTrans`) — the "Route 2" assembly that replaced the removed
`boxInternalize` axiom (which used to internalize a proof *transformer*, a non-positive premise).
See the `boxInternalize` REMOVED note in `Axioms.lean`. -/

/-- **Mutual / simultaneous bounded Löb** (object form), via Route 2 — ALL CONSTRUCTORS, no axiom.
    From the two object transparency legs `legPD : □_k φP → φD` and `legDP : □_k φD → φP`, build
    `□_k φP → φP` as a `Provable` object:

      `boxIntro` legPD : □_k(□φP → φD)        (necessitate the leg)
      `axK`            : □_k(□φP) → □_k φD     (GL axiom-K distributes the box)
      `box4`           : □φP → □(□φP)          (object GL-4)
      `implTrans` ×2   : □φP → □φD → φP   ⇒    □_k φP → φP.

    All boxes stay at the single budget `k`; the side-conditions are formula-size bounds. -/
theorem mutual_loeb (k : Nat) (pP qP pD qD : Prog) (bP bD : Action)
    (legPD : Provable k (.impl (.box k (.plays pP qP bP)) (.plays pD qD bD)))
    (legDP : Provable k (.impl (.box k (.plays pD qD bD)) (.plays pP qP bP)))
    (hs1 : (Formula.box k (.impl (.box k (.plays pP qP bP)) (.plays pD qD bD))).size ≤ k)
    (hs2 : (Formula.impl (.box k (.box k (.plays pP qP bP))) (.box k (.plays pD qD bD))).size ≤ k)
    (hs3 : (Formula.box k (.plays pP qP bP)).size ≤ k)
    (hs4 : (Formula.impl (.box k (.plays pP qP bP)) (.box k (.box k (.plays pP qP bP)))).size ≤ k)
    (hs5 : (Formula.box k (.box k (.plays pP qP bP))).size ≤ k)
    (hszK4 : (Formula.impl (.box k (.plays pP qP bP)) (.box k (.plays pD qD bD))).size ≤ k)
    (hszBoxD : (Formula.box k (.plays pD qD bD)).size ≤ k)
    (hsz : (Formula.impl (.box k (.plays pP qP bP)) (.plays pP qP bP)).size ≤ k) :
    Provable k (.impl (.box k (.plays pP qP bP)) (.plays pP qP bP)) := by
  -- Route 2 (MutualLobSpike), now ALL CONSTRUCTORS — no transformer, no `boxInternalize` axiom:
  -- boxIntro legPD ; axK ; box4 ; implTrans×2.  φP = .plays pP qP bP, φD = .plays pD qD bD.
  -- 1. box the leg `□φP → φD` : Provable k (□_k(□φP → φD))
  have h1 : Provable k (Formula.box k (.impl (.box k (.plays pP qP bP)) (.plays pD qD bD))) :=
    Provable.boxIntro k k (.impl (.box k (.plays pP qP bP)) (.plays pD qD bD)) legPD hs1
  -- 2. axK distributes : □_k(□φP) → □_k φD
  have h2 : Provable k (.impl (.box k (.box k (.plays pP qP bP))) (.box k (.plays pD qD bD))) :=
    Provable.axK k k (.box k (.plays pP qP bP)) (.plays pD qD bD) h1 hs2
  -- 3. box4 (object GL-4) : □φP → □(□φP)
  have h3 : Provable k (.impl (.box k (.plays pP qP bP)) (.box k (.box k (.plays pP qP bP)))) :=
    Provable.box4 k k (.plays pP qP bP) hs3 hs4
  -- 4. implTrans h3 ; h2 : □φP → □φD  (cut formula □(□φP), size = hs5)
  have h4 : Provable k (.impl (.box k (.plays pP qP bP)) (.box k (.plays pD qD bD))) :=
    Provable.implTrans (.box k (.plays pP qP bP)) (.box k (.box k (.plays pP qP bP)))
      (.box k (.plays pD qD bD)) k k h3 h2 (le_refl k) (le_refl k) hs5 hszK4
  -- 5. implTrans h4 ; legDP : □φP → φP  (cut formula □φD, size = hszBoxD)
  exact Provable.implTrans (.box k (.plays pP qP bP)) (.box k (.plays pD qD bD))
    (.plays pP qP bP) k k h4 legDP (le_refl k) (le_refl k) hszBoxD hsz

/-! ## Bounded Löb INSIDE `Provable` — the internalized chain (I4).

`bloeb_engine` runs Löb's derivation entirely in `Provable` at ONE subscript-and-budget `u`, from the
TIGHT premise `Provable u (□_u φ → φ)`. The fixpoint sentence is `ψ := .diag u φ` (Program.lean), whose
`interp` IS the fixpoint (Dynamics.lean); the legs are the (Löb-premise-gated) `diagF`/`diagB` rules,
K-as-formula is `axKf`, and the S-composition is `impS2` — all sound constructors (Provable_sound).
The 12 size side-conditions are all `O(log u) + O(φ.size)`-shaped; `pblt_engine` discharges them from
ONE master bound. Design + validation: `Research/Notes/INTERNALIZATION_ROADMAP.md` (I0),
`Research/Spikes/pblt/I0Design.lean` (`bloeb_mini`, no axioms). -/

theorem bloeb_engine (u : Nat) (φ : Formula)
    (hLoeb : Provable u (.impl (.box u φ) φ))
    (hs1 : (Formula.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ)).size ≤ u)
    (hs2 : (Formula.impl (.impl (.box u (.diag u φ)) φ) (.diag u φ)).size ≤ u)
    (hs3 : (Formula.box u (Formula.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ))).size ≤ u)
    (hs5 : (Formula.impl (.box u (.diag u φ)) (.box u (.impl (.box u (.diag u φ)) φ))).size ≤ u)
    (hs6 : (Formula.impl (.box u (.impl (.box u (.diag u φ)) φ))
              (.impl (.box u (.box u (.diag u φ))) (.box u φ))).size ≤ u)
    (hs7 : (Formula.impl (.box u (.diag u φ)) (.impl (.box u (.box u (.diag u φ))) (.box u φ))).size ≤ u)
    (hs8 : (Formula.box u (.diag u φ)).size ≤ u)
    (hs9 : (Formula.impl (.box u (.diag u φ)) (.box u (.box u (.diag u φ)))).size ≤ u)
    (hs10 : (Formula.impl (.box u (.diag u φ)) (.box u φ)).size ≤ u)
    (hs11 : (Formula.impl (.box u (.diag u φ)) φ).size ≤ u)
    (hs12 : (Formula.box u (.impl (.box u (.diag u φ)) φ)).size ≤ u)
    (hs13 : (Formula.box u φ).size ≤ u) :
    Provable u φ := by
  -- the two fixpoint legs (gated on hLoeb)
  have legF : Provable u (.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ)) :=
    Provable.diagF u u φ hLoeb hs1
  have legB : Provable u (.impl (.impl (.box u (.diag u φ)) φ) (.diag u φ)) :=
    Provable.diagB u u φ hLoeb hs2
  -- h1 : □(ψ → (□ψ→φ))            [boxIntro legF]
  have h1 : Provable u (.box u (.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ))) :=
    Provable.boxIntro u u _ legF hs3
  -- h2 : □ψ → □(□ψ→φ)             [axK-rule on h1]
  have h2 : Provable u (.impl (.box u (.diag u φ)) (.box u (.impl (.box u (.diag u φ)) φ))) :=
    Provable.axK u u _ _ h1 hs5
  -- h3 : □(□ψ→φ) → (□□ψ → □φ)     [axKf — the FORMULA form of K]
  have h3 : Provable u (.impl (.box u (.impl (.box u (.diag u φ)) φ))
      (.impl (.box u (.box u (.diag u φ))) (.box u φ))) :=
    Provable.axKf u u (.box u (.diag u φ)) φ hs6
  -- h4 : □ψ → (□□ψ → □φ)          [implTrans h2 h3]
  have h4 : Provable u (.impl (.box u (.diag u φ)) (.impl (.box u (.box u (.diag u φ))) (.box u φ))) :=
    Provable.implTrans _ _ _ u u h2 h3 (Nat.le_refl u) (Nat.le_refl u) hs12 hs7
  -- h5 : □ψ → □□ψ                 [box4]
  have h5 : Provable u (.impl (.box u (.diag u φ)) (.box u (.box u (.diag u φ)))) :=
    Provable.box4 u u (.diag u φ) hs8 hs9
  -- h6 : □ψ → □φ                  [impS2 h4 h5 — S-composition]
  have h6 : Provable u (.impl (.box u (.diag u φ)) (.box u φ)) :=
    Provable.impS2 _ _ _ u u h4 h5 (Nat.le_refl u) hs10
  -- h7 : □ψ → φ                   [implTrans h6 hLoeb]
  have h7 : Provable u (.impl (.box u (.diag u φ)) φ) :=
    Provable.implTrans _ _ _ u u h6 hLoeb (Nat.le_refl u) (Nat.le_refl u) hs13 hs11
  -- h8 : ψ ; h9 : □ψ ; φ          [app legB h7 ; boxIntro ; app h7 h9]
  have h8 : Provable u (.diag u φ) := Provable.app u u _ _ legB h7 (Nat.le_refl u)
  have h9 : Provable u (.box u (.diag u φ)) := Provable.boxIntro u u _ h8 hs8
  exact Provable.app u u _ _ h7 h9 (Nat.le_refl u)

/-- **Parametric bounded Löb, INTERNAL** — the `PBLT` conclusion as a THEOREM. Tight premise
    (`Provable (f k) (□_{f k} φk → φk)` — what the consumers' `*_loeb_premise` lemmas produce) + ONE
    master size bound (`9·log2(f k) + 6·(φ k).size + 32 ≤ f k`, eventual — from the consumers'
    `linear_log2_add_le`-style lemmas, since play-atom families have size `O(log k)`). Conclusion is
    the axiom's exact `∃k₂, ∀k>k₂, ∃m, Provable m (φ k)` shape. -/
theorem pblt_engine (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Provable (f k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 9 * Nat.log2 (f k) + 6 * (φ k).size + 32 ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k) := by
  refine ⟨k₁, fun k hk => ⟨f k, ?_⟩⟩
  have hm := hsz k hk
  refine bloeb_engine (f k) (φ k) (hLoeb k hk) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · simp only [Formula.size]
      omega
