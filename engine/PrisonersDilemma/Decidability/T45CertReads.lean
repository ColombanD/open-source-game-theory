import PrisonersDilemma.Decidability.T31EngineDecider
import PrisonersDilemma.Decidability.T43ModestUniverse

/-!
# T4.5 spike — the certificate layer's READ INTERFACE (T4.4c part 1).

`DECIDABILITY_ROADMAP.md` T4.4c. The stabilization argument needs a CONGRUENCE property for
the step operator `stepB` (T4.4): at an in-space query, its value depends only on the
approximation's values at in-space queries. Every logic-side read of `stepB` strictly
decreases the budget or lands in a finite formula family — EXCEPT the reads hidden inside
the imported `decCertG` (the atom side): its guard cites `D kg (g.subst me oppo)` and its
refutation sweeps `D m (.neg (g.subst me oppo))` consult the oracle at formulas built by the
evaluation dynamics. This spike makes those reads a first-class object:

  * **`CertRead b me oppo body m ψ`** — the budget-indexed reachability relation: "running
    the certificate search at budget `b` on `(me, oppo, body)` may consult the oracle at
    `(m, ψ)`". One constructor per `decCertG` consultation site (guard cite, refutation
    sweep) and per recursion site (structural descent, `.sim` re-rooting, `.ite`/`.search`
    branches), overapproximating the swept budgets.
  * **`decCertG_congr`** — two oracles agreeing on the `CertRead`-set produce THE SAME
    Bool at every fuel: `decCertG` reads its oracle ONLY at `CertRead` queries. (Induction
    on fuel, mirroring the recursion; `certOG_congr` is the plays-atom wrapper.)
  * **`certRead_mem_guardU`** — over the T4.3 modest universe (players × players × certU),
    every read formula is a `guardU` member or the `.neg` of one: the read-set of the
    whole atom layer is FINITE. (Consumes T4.3's `step_sim`/`step_search`/subterm
    machinery.)

Together: the atom side of `stepB` is congruent past the finite guard family — the last
opaque piece of the in-space closure. Part 2 assembles the logic-side space and the T4.1a
countP stabilization on top.
-/

namespace PD.T45
open PD PD.T31 PD.T43

/-! ## 1. The read relation — one constructor per consultation/recursion site. -/

/-- `CertRead b me oppo body m ψ`: the certificate search at budget `b` on
    `(me, oppo, body)` may consult the guard oracle at `(m, ψ)`. Budget-indexed and
    OVERAPPROXIMATING (sweeps quantified, both `.ite`/`.search` branches included) —
    exactness is not needed, only: (i) `decCertG` reads within it (`decCertG_congr`),
    (ii) it stays in the finite guard family over the modest universe
    (`certRead_mem_guardU`). -/
inductive CertRead : Nat → Prog → Prog → Prog → Nat → Formula → Prop where
  -- the two consultation sites of the `.search` case
  | citeT {b : Nat} {me oppo : Prog} {kg : Nat} {g : Formula} {p q : Prog} :
      CertRead b me oppo (.search kg g p q) kg (g.subst me oppo)
  | citeF {b : Nat} {me oppo : Prog} {kg : Nat} {g : Formula} {p q : Prog} {m : Nat}
      (hm : m ≤ b) :
      CertRead b me oppo (.search kg g p q) m (.neg (g.subst me oppo))
  -- recursion through the `.search` branches
  | searchT {b : Nat} {me oppo : Prog} {kg : Nat} {g : Formula} {p q : Prog} {m : Nat}
      {ψ : Formula} :
      CertRead (b - c_guard kg - c_node) me oppo p m ψ →
      CertRead b me oppo (.search kg g p q) m ψ
  | searchF {b : Nat} {me oppo : Prog} {kg : Nat} {g : Formula} {p q : Prog}
      {m' m : Nat} {ψ : Formula} (hm' : m' ≤ b) :
      CertRead (b - m' - kg - c_node) me oppo q m ψ →
      CertRead b me oppo (.search kg g p q) m ψ
  -- structural descent
  | selfR {b : Nat} {me oppo : Prog} {m : Nat} {ψ : Formula} :
      CertRead (b - c_node) me oppo me m ψ →
      CertRead b me oppo .self m ψ
  | oppR {b : Nat} {me oppo : Prog} {m : Nat} {ψ : Formula} :
      CertRead (b - c_node) me oppo oppo m ψ →
      CertRead b me oppo .opp m ψ
  | botR {b : Nat} {me oppo p : Prog} {m : Nat} {ψ : Formula} :
      CertRead (b - c_node) me oppo p m ψ →
      CertRead b me oppo (.bot p) m ψ
  | simR {b : Nat} {me oppo p q : Prog} {m : Nat} {ψ : Formula} :
      CertRead (b - c_node) (p.subst me oppo) (q.subst me oppo) (p.subst me oppo) m ψ →
      CertRead b me oppo (.sim p q) m ψ
  -- `.ite`: the guard at any swept budget, both branches at the residues
  | iteG {b : Nat} {me oppo g : Prog} {a' : Action} {p q : Prog} {m' m : Nat}
      {ψ : Formula} (hm' : m' ≤ b) :
      CertRead m' me oppo g m ψ →
      CertRead b me oppo (.ite g a' p q) m ψ
  | iteP {b : Nat} {me oppo g : Prog} {a' : Action} {p q : Prog} {m' m : Nat}
      {ψ : Formula} (hm' : m' ≤ b) :
      CertRead (b - m' - c_node) me oppo p m ψ →
      CertRead b me oppo (.ite g a' p q) m ψ
  | iteQ {b : Nat} {me oppo g : Prog} {a' : Action} {p q : Prog} {m' m : Nat}
      {ψ : Formula} (hm' : m' ≤ b) :
      CertRead (b - m' - c_node) me oppo q m ψ →
      CertRead b me oppo (.ite g a' p q) m ψ

/-! ## 2. Congruence: `decCertG` reads its oracle ONLY at `CertRead` queries. -/

theorem anyCongr {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.any_cons]
      rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem decCertG_congr {D₁ D₂ : Nat → Formula → Bool} :
    ∀ (fuel b : Nat) (me oppo body : Prog) (a : Action),
    (∀ m ψ, CertRead b me oppo body m ψ → D₁ m ψ = D₂ m ψ) →
    decCertG D₁ fuel b me oppo body a = decCertG D₂ fuel b me oppo body a := by
  intro fuel
  induction fuel with
  | zero => intro b me oppo body a _; rfl
  | succ f ih =>
    intro b me oppo body a hD
    rw [decCertG.eq_def, decCertG.eq_def]
    cases body with
    | const c => rfl
    | self =>
        simp only []
        rw [ih _ _ _ _ _ (fun m ψ hr => hD m ψ (.selfR hr))]
    | opp =>
        simp only []
        rw [ih _ _ _ _ _ (fun m ψ hr => hD m ψ (.oppR hr))]
    | bot p =>
        simp only []
        rw [ih _ _ _ _ _ (fun m ψ hr => hD m ψ (.botR hr))]
    | sim p q =>
        simp only []
        rw [ih _ _ _ _ _ (fun m ψ hr => hD m ψ (.simR hr))]
    | ite g a' p q =>
        simp only []
        congr 1
        apply anyCongr
        intro m' hm'
        have hm'b : m' ≤ b := by
          have := List.mem_range.mp hm'; omega
        apply anyCongr
        intro r _
        rw [ih m' _ _ g r (fun m ψ hr => hD m ψ (.iteG hm'b hr))]
        congr 1
        by_cases hra : (r == a') = true
        · rw [if_pos hra, if_pos hra,
            ih _ _ _ p a (fun m ψ hr => hD m ψ (.iteP hm'b hr))]
        · rw [if_neg hra, if_neg hra,
            ih _ _ _ q a (fun m ψ hr => hD m ψ (.iteQ hm'b hr))]
    | search kg g p q =>
        simp only []
        rw [hD kg (g.subst me oppo) .citeT,
          ih _ _ _ _ _ (fun m ψ hr => hD m ψ (.searchT hr))]
        congr 1
        apply anyCongr
        intro m' hm'
        have hm'b : m' ≤ b := by
          have := List.mem_range.mp hm'; omega
        rw [hD m' (.neg (g.subst me oppo)) (.citeF hm'b),
          ih _ _ _ _ _ (fun m ψ hr => hD m ψ (.searchF hm'b hr))]

/-- The plays-atom wrapper: `certOG` is congruent past the `CertRead`-set. -/
theorem certOG_congr {D₁ D₂ : Nat → Formula → Bool} (fuel k : Nat)
    {p q : Prog} {a : Action}
    (hD : ∀ m ψ, CertRead k p q p m ψ → D₁ m ψ = D₂ m ψ) :
    certOG D₁ fuel k (.plays p q a) = certOG D₂ fuel k (.plays p q a) := by
  show decCertG D₁ fuel k p q p a = decCertG D₂ fuel k p q p a
  exact decCertG_congr fuel k p q p a hD

/-! ## 3. Over the modest universe, the read-set is the finite guard family. -/

/-- **The atom layer's reads are FINITE**: over the T4.3 modest universe, every oracle
    consultation of the certificate search is at a `guardU` member or the `.neg` of one. -/
theorem certRead_mem_guardU (r₁ r₂ : Prog)
    (h₁ : modestP r₁ = true) (h₂ : modestP r₂ = true) :
    ∀ {b : Nat} {me oppo body : Prog} {m : Nat} {ψ : Formula},
    CertRead b me oppo body m ψ →
    me ∈ players r₁ r₂ → oppo ∈ players r₁ r₂ → body ∈ certU r₁ r₂ →
    ψ ∈ guardU r₁ r₂ ∨ ∃ ψ₀ ∈ guardU r₁ r₂, ψ = .neg ψ₀ := by
  intro b me oppo body m ψ hr
  induction hr with
  | citeT =>
      intro hme hoppo hbody
      exact Or.inl (step_search r₁ r₂ hme hoppo hbody)
  | citeF hm =>
      intro hme hoppo hbody
      exact Or.inr ⟨_, step_search r₁ r₂ hme hoppo hbody, rfl⟩
  | @searchT _ _ _ kg g p q _ _ _ ih =>
      intro hme hoppo hbody
      refine ih hme hoppo (certU_trans r₁ r₂ hbody ?_)
      simp only [subsP, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (Or.inr (mem_subsP_self p)))
  | @searchF _ _ _ kg g p q _ _ _ _ _ ih =>
      intro hme hoppo hbody
      refine ih hme hoppo (certU_trans r₁ r₂ hbody ?_)
      simp only [subsP, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (mem_subsP_self q))
  | selfR _ ih =>
      intro hme hoppo _
      exact ih hme hoppo (players_subset_certU r₁ r₂ hme)
  | oppR _ ih =>
      intro hme hoppo _
      exact ih hme hoppo (players_subset_certU r₁ r₂ hoppo)
  | @botR _ _ _ p _ _ _ ih =>
      intro hme hoppo hbody
      refine ih hme hoppo (certU_trans r₁ r₂ hbody ?_)
      simp only [subsP, List.mem_cons]
      exact Or.inr (mem_subsP_self p)
  | @simR _ _ _ p q _ _ _ ih =>
      intro hme hoppo hbody
      obtain ⟨hp', hq'⟩ := step_sim r₁ r₂ h₁ h₂ hme hoppo hbody
      exact ih hp' hq' (players_subset_certU r₁ r₂ hp')
  | @iteG _ _ _ g a' p q _ _ _ _ _ ih =>
      intro hme hoppo hbody
      refine ih hme hoppo (certU_trans r₁ r₂ hbody ?_)
      simp only [subsP, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (Or.inl (mem_subsP_self g)))
  | @iteP _ _ _ g a' p q _ _ _ _ _ ih =>
      intro hme hoppo hbody
      refine ih hme hoppo (certU_trans r₁ r₂ hbody ?_)
      simp only [subsP, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (Or.inr (mem_subsP_self p)))
  | @iteQ _ _ _ g a' p q _ _ _ _ _ ih =>
      intro hme hoppo hbody
      refine ih hme hoppo (certU_trans r₁ r₂ hbody ?_)
      simp only [subsP, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (mem_subsP_self q))

end PD.T45
