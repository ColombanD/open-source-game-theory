import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Asymptotics

/-!
# Base/AtomCerts — constructive atom certificates and cost monotonicity

The sound survivors of the deleted `atom_complete` axiom: `cert_searchfree` /
`atom_complete_searchfree` (search-free plays always have a `PlaysProof` at the run
price), the `atom_search_*` guard-commit certificates, `c_guard`/`atom_cost`
monotonicity, `Prog.hasSearch_subst`, and `proofSearch_spec`.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-- `subst` cannot introduce a `.search`: substituting search-free players into a search-free
    body stays search-free. -/
theorem Prog.hasSearch_subst : ∀ (p me oppo : Prog), p.hasSearch = false →
    me.hasSearch = false → oppo.hasSearch = false → (p.subst me oppo).hasSearch = false
  | .const _, _, _ => fun _ _ _ => rfl
  | .self, _, _ => fun _ hme _ => by simpa [Prog.subst] using hme
  | .opp, _, _ => fun _ _ ho => by simpa [Prog.subst] using ho
  | .bot p, m1, o1 => fun hp _ _ => by simpa [Prog.subst, Prog.hasSearch] using hp
  | .sim p q, m1, o1 => fun hp hme ho => by
      simp only [Prog.hasSearch, Bool.or_eq_false_iff] at hp
      simp only [Prog.subst, Prog.hasSearch, Bool.or_eq_false_iff]
      exact ⟨Prog.hasSearch_subst p m1 o1 hp.1 hme ho,
             Prog.hasSearch_subst q m1 o1 hp.2 hme ho⟩
  | .ite b ac p q, m1, o1 => fun hp hme ho => by
      simp only [Prog.hasSearch, Bool.or_eq_false_iff] at hp
      simp only [Prog.subst, Prog.hasSearch, Bool.or_eq_false_iff]
      exact ⟨⟨Prog.hasSearch_subst b m1 o1 hp.1.1 hme ho,
              Prog.hasSearch_subst p m1 o1 hp.1.2 hme ho⟩,
             Prog.hasSearch_subst q m1 o1 hp.2 hme ho⟩
  | .search _ _ _ _, _, _ => fun hp _ _ => by simp [Prog.hasSearch] at hp

/-- `c_guard` (the cost of writing the budget numeral `k` in a proof transcript)
    is monotone: a larger `k` takes at least as many characters to write.
    Needed for `atom_cost_mono`. Now a *theorem* (was an axiom): with the concrete
    `c_guard k = Nat.log2 k + 1` (ProofSystem.lean), monotonicity is `Nat.log2`'s. -/
theorem c_guard_mono : ∀ {a b : Nat}, a ≤ b → c_guard a ≤ c_guard b := by
  intro a b h
  simp only [numCost, c_guard, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- `atom_cost` is monotone in fuel, so bot proofs can lift a small-fuel atom to a
    larger working budget via `proofSearch_monotone`. -/
theorem atom_cost_mono {a b : Nat} (h : a ≤ b) : atom_cost a ≤ atom_cost b := by
  unfold atom_cost
  exact Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.add_le_add_left (c_guard_mono h) _) h) _

/-! ## Atom certificates, constructively — the deleted `atom_complete`'s SOUND survivors.

The old `atom_complete` (`play fuel p q = some a → AtomProvable (atom_cost fuel) …`) is GONE
with its axiom: it was FALSE — an else-play of a failed search has certificates only ABOVE the
failed budget (the `search_f` floor), and an anti-diagonal else-play has none at all
(`T32Inconsistency.lean`). What survives, constructively:
  * SEARCH-FREE runs certify at `3 ^ fuel` (`atom_complete_searchfree` — the honest bound;
    the old `atom_cost fuel` never actually bounded branching runs, the axiom silently
    covered the gap);
  * FIRED top-level searches certify at `log2 k + 3` via `search_t` (`atom_search_t_top` /
    `…_bot_top`) — cheap, since `search_t` cites the oracle rather than embedding the proof;
  * FAILED top-level searches certify at `m + k + 2` via `search_f` (`atom_search_f_top` /
    `…_bot_top`) given a refutation of the guard (`Pf.atomNeg`) — the floor `≥ k + 1`
    is what consistency forces. Deeper runs compose these per site. -/

theorem cert_searchfree : ∀ (fuel : Nat) (me oppo body : Prog) (a : Action),
    me.hasSearch = false → oppo.hasSearch = false → body.hasSearch = false →
    eval fuel me oppo body = some a →
    ∃ n, PlaysProof me oppo body a n ∧ n ≤ 3 ^ fuel := by
  intro fuel
  induction fuel with
  | zero => intro me oppo body a _ _ _ h; simp [eval] at h
  | succ f ih =>
    intro me oppo body a hme ho hb h
    have h3 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    have hpow : 3 ^ (f+1) = 3 ^ f + 3 ^ f + 3 ^ f := by rw [pow_succ]; ring
    have hcn : c_node = 1 := rfl
    cases body with
    | const c =>
        rw [eval] at h
        injection h with h'
        subst h'
        exact ⟨c_leaf, .const, by have : c_leaf = 1 := rfl; omega⟩
    | self =>
        rw [eval] at h
        obtain ⟨n, cert, hn⟩ := ih me oppo me a hme ho hme h
        exact ⟨n + c_node, .self cert, by omega⟩
    | opp =>
        rw [eval] at h
        obtain ⟨n, cert, hn⟩ := ih me oppo oppo a hme ho ho h
        exact ⟨n + c_node, .opp cert, by omega⟩
    | bot p =>
        rw [eval] at h
        have hp : p.hasSearch = false := by simpa [Prog.hasSearch] using hb
        obtain ⟨n, cert, hn⟩ := ih me oppo p a hme ho hp h
        exact ⟨n + c_node, .bot cert, by omega⟩
    | sim p q =>
        simp only [eval] at h
        simp only [Prog.hasSearch, Bool.or_eq_false_iff] at hb
        have hp' := Prog.hasSearch_subst p me oppo hb.1 hme ho
        have hq' := Prog.hasSearch_subst q me oppo hb.2 hme ho
        obtain ⟨n, cert, hn⟩ := ih _ _ _ a hp' hq' hp' h
        exact ⟨n + c_node, .sim cert, by omega⟩
    | ite b ac p q =>
        rw [eval] at h
        cases hg : eval f me oppo b with
        | none => rw [hg] at h; simp [bind, Option.bind] at h
        | some r =>
            rw [hg] at h
            simp only [bind, Option.bind] at h
            simp only [Prog.hasSearch, Bool.or_eq_false_iff] at hb
            obtain ⟨n₁, cert₁, hn₁⟩ := ih me oppo b r hme ho hb.1.1 hg
            by_cases hr : (r == ac) = true
            · rw [if_pos hr] at h
              obtain ⟨n₂, cert₂, hn₂⟩ := ih me oppo p a hme ho hb.1.2 h
              exact ⟨n₁ + n₂ + c_node, .ite_t cert₁ hr cert₂, by omega⟩
            · rw [if_neg hr] at h
              obtain ⟨n₂, cert₂, hn₂⟩ := ih me oppo q a hme ho hb.2 h
              have hrf : (r == ac) = false := by simpa using hr
              exact ⟨n₁ + n₂ + c_node, .ite_f cert₁ hrf cert₂, by omega⟩
    | search k g p q => simp [Prog.hasSearch] at hb

/-- Σ₁-completeness for SEARCH-FREE atoms — the constructive fragment of the deleted
    `atom_complete`, at the honest bound `3 ^ fuel`. -/
theorem atom_complete_searchfree (p q : Prog) (a : Action) (fuel : Nat)
    (hp : p.hasSearch = false) (hq : q.hasSearch = false)
    (h : play fuel p q = some a) : AtomProvable (3 ^ fuel) (.plays p q a) := by
  obtain ⟨n, cert, hn⟩ := cert_searchfree fuel p q p a hp hq hp h
  exact ⟨cert, hn⟩

/-- FIRED top-level search (the Dupoc/Cupod shape): the guard's provability at its own
    literal certifies the then-play at `log2 k + 3` characters. -/
theorem atom_search_t_top (k : Nat) (g : Formula) (aT aE : Action) (oppo : Prog)
    (hg : Pf k (g.subst (.search k g (.const aT) (.const aE)) oppo)) :
    AtomProvable (Nat.log2 k + 3)
      (.plays (.search k g (.const aT) (.const aE)) oppo aT) := by
  refine ⟨PlaysProof.search_t hg PlaysProof.const, ?_⟩
  show c_leaf + c_guard k + c_node ≤ Nat.log2 k + 3
  simp only [numCost, c_leaf, c_guard, c_node]
  omega

/-- FIRED `.bot`-wrapped top-level search (the `.bot DupocBot` shape). -/
theorem atom_search_t_bot_top (k : Nat) (g : Formula) (aT aE : Action) (oppo : Prog)
    (hg : Pf k (g.subst (.bot (.search k g (.const aT) (.const aE))) oppo)) :
    AtomProvable (Nat.log2 k + 4)
      (.plays (.bot (.search k g (.const aT) (.const aE))) oppo aT) := by
  refine ⟨PlaysProof.bot (PlaysProof.search_t hg PlaysProof.const), ?_⟩
  show c_leaf + c_guard k + c_node + c_node ≤ Nat.log2 k + 4
  simp only [numCost, c_leaf, c_guard, c_node]
  omega

/-- FAILED top-level search: a refutation of the guard certifies the else-play — at the
    FLOOR `≥ k + 1` (the cost pays the whole failed budget; consistency forces this). -/
theorem atom_search_f_top (k m : Nat) (g : Formula) (aT aE : Action) (oppo : Prog)
    (hneg : Pf m (.neg (g.subst (.search k g (.const aT) (.const aE)) oppo))) :
    AtomProvable (m + k + 2)
      (.plays (.search k g (.const aT) (.const aE)) oppo aE) := by
  refine ⟨PlaysProof.search_f hneg PlaysProof.const, ?_⟩
  show c_leaf + m + k + c_node ≤ m + k + 2
  simp only [c_leaf, c_node]
  omega

/-- FAILED `.bot`-wrapped top-level search. -/
theorem atom_search_f_bot_top (k m : Nat) (g : Formula) (aT aE : Action) (oppo : Prog)
    (hneg : Pf m (.neg (g.subst (.bot (.search k g (.const aT) (.const aE))) oppo))) :
    AtomProvable (m + k + 3)
      (.plays (.bot (.search k g (.const aT) (.const aE))) oppo aE) := by
  refine ⟨PlaysProof.bot (PlaysProof.search_f hneg PlaysProof.const), ?_⟩
  show c_leaf + m + k + c_node + c_node ≤ m + k + 3
  simp only [c_leaf, c_node]
  omega

/-- The bridge `proofSearch ↔ Pf` is now a theorem, not an axiom. -/
theorem proofSearch_spec (k : Nat) (φ : Formula) :
    proofSearch k φ = true ↔ Pf k φ := by
  unfold proofSearch; exact decide_eq_true_iff

end PD.BaseTheorems
