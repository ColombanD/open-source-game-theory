import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

/-!
# `evalC` — the ORIGINAL sound computable partial evaluator (HISTORICAL; superseded)

**Superseded 2026-07-03 by `Decidability/T31EngineDecider.lean` §9 (`evalG`)**, which commits
soundly in BOTH guard polarities (true via the verified enumerator `decFull`; false via a
DERIVABLE refutation plus soundness/consistency), agrees with `eval` at the SAME fuel, and
runs the actual search bots under `#eval`. `evalC` is kept building as the historical
first artifact and because its 3-valued-guard design lesson (a 2-valued guard is UNSOUND on
undecided searches) is documented here.

Historical context (updated): `eval` (Dynamics.lean) is `noncomputable` because its
`.search` guard consults the classical oracle `proofSearch k φ := decide (Provable k φ)`.
`Provable` is now known to be absolutely SEMIDECIDABLE (`Provable_iff_decFull`) and
DECIDABLE over the modest stratum (`Decidability/T47Stabilization.lean`); full decidability
— hence a strictly computable `eval` — is open exactly up to the `CutRelevance` conjecture
(`Decidability/T42ProvableB.lean`). The former claims in this header that the boundary was
"permanent" and axiom-backed predate the 2026-07-03 axiom deletion and are RETIRED.

`evalC` mirrors `eval` except the `.search` guard consults the 3-valued computable
`decGuard`: `some true` (a finite play witness fits the budget), `some false` (a finite
refutation), `none` (undecided — the Löb fixpoints). Faithfulness: `evalC_sound` — every
committed answer is a real classical play.
-/

namespace PD

mutual
  /-- Computable fuel-bounded **partial** evaluator. Mirrors `eval` except the `.search`
      guard consults the 3-valued computable `decGuard`; `none` guard ⇒ `none` result.
      One decreasing `fuel` across the mutual group ⇒ total & computable. -/
  def evalC : Nat → (me opponent body : Prog) → Option Action
    | 0,   _,  _,        _    => none
    | n+1, me, opponent, body => match body with
      | .const a        => some a
      | .self           => evalC n me opponent me
      | .opp            => evalC n me opponent opponent
      | .bot p          => evalC n me opponent p
      | .sim p q        =>
          let p' := p.subst me opponent
          let q' := q.subst me opponent
          evalC n p' q' p'
      | .ite b a p q    =>
          match evalC n me opponent b with
          | some r => if r == a then evalC n me opponent p else evalC n me opponent q
          | none   => none
      | .search k φ p q =>
          match decGuard k n (φ.subst me opponent) with
          | some true  => evalC n me opponent p
          | some false => evalC n me opponent q
          | none       => none

  /-- 3-valued, computable, fuel-bounded, **budget-`k`-faithful** guard decision —
      mirrors `eval`'s oracle `proofSearch k φ = decide (Provable k φ)` soundly in both
      polarities:
      * `some true`  — a finite play witness exists AND fits budget `k` (`atom_cost n ≤ k`),
        so the atom is `Provable k` (`atom_complete` + `atom_monotone`) ⇒ `proofSearch k`
        fires. The budget check is what makes `evalC` faithful to `eval` (without it, a
        witness exceeding `k` would make `evalC` cooperate where `eval`'s budgeted oracle
        does not — see the k=0 probe);
      * `some false` — a finite *refutation*: the subject actually plays another action,
        so the atom is semantically false (`¬ interp`), hence `¬ Provable k` (soundness)
        ⇒ `proofSearch k` does not fire. No budget needed for this direction;
      * `none`       — undecided within fuel (Löb fixpoints; or a witness over budget).
      Handles the guard shapes the library's bots use; everything else ⇒ `none`. -/
  def decGuard : Nat → Nat → Formula → Option Bool
    | _, 0,   _ => none
    | k, n+1, φ => match φ with
      | .plays p q a =>
          match evalC (n+1) p q p with
          | some b =>
              if b = a then
                -- plays `a`: commit `true` only on the SEARCH-FREE fragment (post-repair:
                -- the old `atom_cost` check leaned on the deleted-inconsistent axiom;
                -- search-crossing certificates need the full decider, T3.2c) within budget
                if p.hasSearch = false ∧ q.hasSearch = false ∧ 3 ^ (n+1) ≤ k
                  then some true else none
              else some false        -- plays `b ≠ a`: the atom is refuted (semantic)
          | none   => none
      | .impl φ' ψ    =>
          -- weakenImpl (true-consequent): consequent witnessed within the REDUCED budget
          -- `k − |φ'→ψ|` AND the implication fits `k` ⇒ `φ' → ψ` provable at `k`
          -- (transcript accounting: the implication's proof CONTAINS the consequent's,
          -- so `weakenImpl`'s gate is `m + |φ'→ψ| ≤ k`).
          -- We do not attempt to refute an implication computably ⇒ at most `some true`.
          match decGuard (k - (Formula.impl φ' ψ).size) n ψ with
          | some true => if (Formula.impl φ' ψ).size ≤ k then some true else none
          | _         => none
      | _            => none
end

open BaseTheorems in
/-- **Faithfulness of `evalC`/`decGuard` (C2).** Proved jointly by strong induction on
    fuel (the two facts are entangled within a fuel level: `decGuard (n+1)` consults
    `evalC (n+1)`, which consults `decGuard … n`):

    * `evalC fuel … = some a ⇒ eval fuel … = some a` — every committed answer of the
      computable evaluator is *exactly* the classical `eval`'s answer at the same fuel
      (so `#eval evalC` is provably the real outcome whenever it commits);
    * `decGuard k fuel φ = some true  ⇒ proofSearch k φ = true`,
      `decGuard k fuel φ = some false ⇒ proofSearch k φ = false` — the guard's verdicts
      agree with the classical oracle, which is what lets `evalC` mirror `eval`'s branch.

    The converse (eval ⇒ evalC) fails on the Löb fixpoints (eval cooperates via the
    reflection axioms, evalC returns `none`) — the intrinsic boundary, not a gap here. -/
theorem evalC_eq_and_decGuard_sound :
    ∀ fuel,
      (∀ me opponent body a, evalC fuel me opponent body = some a → eval fuel me opponent body = some a)
      ∧ (∀ k φ, (decGuard k fuel φ = some true → proofSearch k φ = true)
              ∧ (decGuard k fuel φ = some false → proofSearch k φ = false)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro me opponent body a h; simp [evalC] at h
    · intro k φ; exact ⟨fun h => by simp [decGuard] at h, fun h => by simp [decGuard] at h⟩
  | succ n ih =>
    obtain ⟨ihE, ihG⟩ := ih
    -- (E) first: evalC (n+1) = eval (n+1) on committed answers, using ihG for guards.
    have hE : ∀ me opponent body a,
        evalC (n+1) me opponent body = some a → eval (n+1) me opponent body = some a := by
      intro me opponent body a h
      cases body with
      | const c => simp only [evalC] at h; simp only [eval]; exact h
      | self => simp only [evalC] at h; rw [eval]; exact ihE _ _ _ _ h
      | opp => simp only [evalC] at h; rw [eval]; exact ihE _ _ _ _ h
      | bot p => simp only [evalC] at h; rw [eval]; exact ihE _ _ _ _ h
      | sim p q => simp only [evalC] at h; rw [eval]; exact ihE _ _ _ _ h
      | ite b a' p q =>
          simp only [evalC] at h; rw [eval]
          cases hb : evalC n me opponent b with
          | none => rw [hb] at h; simp at h
          | some r =>
              rw [hb] at h; simp only at h
              rw [ihE _ _ _ _ hb]; simp only [bind, Option.bind]
              by_cases hr : (r == a') = true
              · rw [if_pos hr] at h ⊢; exact ihE _ _ _ _ h
              · rw [if_neg hr] at h ⊢; exact ihE _ _ _ _ h
      | search k φ p q =>
          simp only [evalC] at h; rw [eval]
          -- branch on decGuard; ihG bridges it to proofSearch so eval takes the same leg
          cases hg : decGuard k n (φ.subst me opponent) with
          | none => rw [hg] at h; simp at h
          | some bguard =>
              cases bguard with
              | true =>
                  rw [hg] at h
                  rw [if_pos ((ihG k (φ.subst me opponent)).1 hg)]
                  exact ihE _ _ _ _ h
              | false =>
                  rw [hg] at h
                  rw [if_neg (by rw [(ihG k (φ.subst me opponent)).2 hg]; simp)]
                  exact ihE _ _ _ _ h
    refine ⟨hE, ?_⟩
    -- (G±) using hE at level n+1.
    intro k φ
    constructor
    · -- decGuard = some true → proofSearch k φ = true
      intro h
      cases φ with
      | plays p q a =>
          simp only [decGuard] at h
          cases hpl : evalC (n+1) p q p with
          | none => rw [hpl] at h; simp at h
          | some b =>
              rw [hpl] at h
              by_cases hba : b = a
              · subst hba
                simp only [↓reduceIte] at h
                by_cases hbud : p.hasSearch = false ∧ q.hasSearch = false ∧ 3 ^ (n+1) ≤ k
                · -- real search-free play at fuel n+1 (via hE) ⇒ constructive certificate
                  have hplay : play (n+1) p q = some b := hE _ _ _ _ hpl
                  exact (proofSearch_spec k _).2
                    (Provable.atom (atom_monotone (3 ^ (n+1)) k _ hbud.2.2
                      (atom_complete_searchfree p q b (n+1) hbud.1 hbud.2.1 hplay)))
                · simp [hbud] at h
              · simp [hba] at h    -- decGuard = some false, contradicts = some true
      | impl φ' ψ =>
          -- weakenImpl: consequent ψ provable within the reduced budget (ihG) AND the
          -- implication fits budget k ⇒ proofSearch k (additive gate: m + |φ'→ψ| ≤ k).
          simp only [decGuard] at h
          cases hψ : decGuard (k - (Formula.impl φ' ψ).size) n ψ with
          | none => rw [hψ] at h; simp at h
          | some bψ =>
              cases bψ with
              | true =>
                  rw [hψ] at h
                  by_cases hsz : (Formula.impl φ' ψ).size ≤ k
                  · -- ψ provable at the reduced budget (ihG); weakenImpl pays it + the conclusion
                    have hψprov : Provable (k - (Formula.impl φ' ψ).size) ψ :=
                      (proofSearch_spec _ ψ).1 ((ihG _ ψ).1 hψ)
                    exact (proofSearch_spec k _).2
                      (Provable.weakenImpl φ' ψ _ hψprov (by omega))
                  · simp [hsz] at h
              | false => rw [hψ] at h; simp at h
      | neg _ => simp [decGuard] at h
      | box _ _ => simp [decGuard] at h
      | eq _ _ => simp [decGuard] at h
      | diag _ _ => simp [decGuard] at h
    · -- decGuard = some false → proofSearch k φ = false
      intro h
      cases φ with
      | plays p q a =>
          simp only [decGuard] at h
          cases hpl : evalC (n+1) p q p with
          | none => rw [hpl] at h; simp at h
          | some b =>
              rw [hpl] at h
              by_cases hba : b = a
              · subst hba; simp only at h
                by_cases hbud : atom_cost (n+1) ≤ k <;> simp [hbud] at h
              · -- p actually plays b ≠ a, so `.plays p q a` is semantically false,
                -- hence not Provable k (soundness), so proofSearch k = false.
                cases hps : proofSearch k (Formula.plays p q a) with
                | false => rfl
                | true =>
                    exfalso
                    have hb_play : play (n+1) p q = some b := hE _ _ _ _ hpl
                    -- proofSearch true ⇒ interp ⇒ ∃m, play m p q = some a; but play is b≠a
                    obtain ⟨m, hm⟩ := proofSearch_sound k _ hps
                    -- both plays lift to fuel `max m (n+1)`, forcing `a = b`
                    have h1 : play (max m (n+1)) p q = some a :=
                      eval_mono_le hm (max m (n+1)) (le_max_left _ _)
                    have h2 : play (max m (n+1)) p q = some b :=
                      eval_mono_le hb_play (max m (n+1)) (le_max_right _ _)
                    have hab : (some a : Option Action) = some b := h1.symm.trans h2
                    injection hab with hab'
                    exact hba hab'.symm
      | impl φ' ψ =>
          -- the `.impl` branch never returns `some false` (at most `some true`)
          simp only [decGuard] at h
          cases hψ : decGuard (k - (Formula.impl φ' ψ).size) n ψ with
          | none => rw [hψ] at h; simp at h
          | some bψ => cases bψ <;> (rw [hψ] at h; simp at h)
      | neg _ => simp [decGuard] at h
      | box _ _ => simp [decGuard] at h
      | eq _ _ => simp [decGuard] at h
      | diag _ _ => simp [decGuard] at h

/-- Computable entry points, mirroring `play`/`outcome`. -/
def playC (fuel : Nat) (me opponent : Prog) : Option Action :=
  evalC fuel me opponent me

def outcomeC (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← playC fuel p q
  let b ← playC fuel q p
  some (a, b)

/-! ## Soundness corollaries (the trustworthiness of `#eval evalC`) -/

/-- `evalC`'s committed answer is exactly the classical `eval`'s, at the same fuel. -/
theorem evalC_sound {fuel : Nat} {me opponent body : Prog} {a : Action}
    (h : evalC fuel me opponent body = some a) : eval fuel me opponent body = some a :=
  (evalC_eq_and_decGuard_sound fuel).1 me opponent body a h

/-- `playC`'s committed answer is the classical `play`'s. -/
theorem playC_sound {fuel : Nat} {me opponent : Prog} {a : Action}
    (h : playC fuel me opponent = some a) : play fuel me opponent = some a :=
  evalC_sound h

/-- **`outcomeC` is sound**: whenever the computable evaluator commits to an outcome, it
    is exactly the classical (noncomputable) `outcome` at the same fuel. So every
    `#eval outcomeC …` that returns `some _` is the genuine game outcome — the kernel
    computation is backed by this theorem, not taken on faith. (The converse fails on the
    Löb fixpoints, where `outcome` commits via reflection and `outcomeC` returns `none`.) -/
theorem outcomeC_sound {fuel : Nat} {p q : Prog} {o : Outcome}
    (h : outcomeC fuel p q = some o) : outcome fuel p q = some o := by
  simp only [outcomeC, playC, bind, Option.bind] at h
  simp only [outcome, play, bind, Option.bind]
  cases ha : evalC fuel p q p with
  | none => rw [ha] at h; simp at h
  | some a =>
      rw [ha] at h; rw [evalC_sound ha]
      cases hb : evalC fuel q p q with
      | none => rw [hb] at h; simp at h
      | some b => rw [hb] at h; rw [evalC_sound hb]; simpa using h

end PD
