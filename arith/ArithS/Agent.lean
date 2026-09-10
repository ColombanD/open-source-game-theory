import ArithS.Neg
import PrisonersDilemma.Base.Soundness
import PrisonersDilemma.Base.AtomCerts

/-!
# ArithS.Agent — T2-AGENT: engine certificates are runs of the arithmetized evaluator (roadmap M3, step (e))

**Every evaluation certificate of `S` is a run of the arithmetized evaluator at the same
budgets, given agreement on the consulted `□_k` facts; unconditional for search-free
programs.**

The engine's `PlaysProof me opp body a n` (`ProofSystem.lean`) is the certificate that, in
the frame `(me, opp)`, the body plays `a` in `n` evaluation steps; its `search_t`/`search_f`
arms consult the proof system on the CLOSED guard `φ.subst me opp` (a `Pf k` derivation,
resp. a `Pf m` refutation). The arithmetized evaluator `EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ a`
(`ArithS.Eval`) consults instead `LenProvableV TAct k (guardCode (tcode φ) (pcode me)
(pcode opp))` — the code of the template `tmpl φ` filled with the players' descriptions,
which on the fragment IS the template code of the closed instantiation
(`guardOf_eq_tcode_subst`, from `tcode_subst`).

* `guardOf φ me opp := guardCode (tcode φ) (pcode me) (pcode opp)` — the consulted guard;
  `guardOf_eq_quote_trAt` (it is `⌜trAt me opp φ⌝`), `guardOf_eq_tcode_subst`.
* `GuardAgreeT` / `GuardAgreeF` — the two directions of "the engine's `Pf` verdict and the
  arithmetized `□_k` verdict agree on the consulted guards": a `Pf k` derivation of the
  closed guard yields a `TAct`-proof of length `≤ k` of its realization (bounded D1 — a
  HYPOTHESIS, named, never an axiom: T2-NEG shows no budget-keeping transfer exists in
  general, so this is exactly where Critch's (d) enters), and a `Pf m` refutation excludes
  one. `models_trAt_of_lenProvableV` is the one-sided fact PA-soundness gives for free: a
  found arithmetized guard is TRUE in `ℕ`. Engine-refutability plus engine soundness
  (`PD.Pf_sound`) gives falsity of the ENGINE reading `Formula.interp` — a different
  sentence (`play`, not `EvalGraph`) — so `GuardAgreeF` is not derived from soundness here.
* `playsProof_evalGraph` — THE THEOREM, on the MODEST fragment (`modestP`: the search-bot
  fragment `fragP` of `ArithS.Code` with `.sim` arguments a placeholder or a closed
  program — the engine's own modesty condition of `Decidability/T43ModestUniverse`, true of
  the whole zoo). Modesty is what makes the fragment CLOSED under the `.sim` step: the new
  frame `(p.subst me opp, q.subst me opp)` is drawn from `{me, opp, p, q}`. The plain
  `fragP` is NOT closed under `subst` — `fragP (p.subst me opp)` needs `atomicP me` as
  soon as `p` contains a searcher whose template names a placeholder, and no searcher is
  `closedP` (its template names `.self`/`.opp`).
* `playsProof_evalGraph_searchFree` — the UNCONDITIONAL version for search-free players
  and body (`Prog.hasSearch = false`): no guard is ever consulted, so no oracle hypothesis.
* `atomProvable_evalGraph` — the atom form (`AtomProvable k (.plays me opp a)`).
* `models_trAt_plays` — the TRUTH equation for the realized play-atom on closed programs:
  `ℕ ⊧ trAt me' opp' (.plays me opp a) ↔ ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜me⌝ a` (the frame
  `me'`, `opp'` is irrelevant for closed programs).

## Remaining gap (recorded, not forced)

From TRUTH of `trAt me' opp' (.plays me opp a)` to `TAct ⊢ trAt …` (Σ₁-completeness):
Foundation's `sigma_one_completeness` is stated for theories over `ℒₒᵣ`; `TAct` is a
theory over `LAct`, and the realized sentence names the action constants `c_C`, `c_D`,
which `TAct` leaves uninterpreted (only `c_C ≠ c_D` — the τ-symmetry of
`ArithS.Symmetry` depends on it), so the sentence is not the `emb`-image of an `ℒₒᵣ`
sentence and cannot be transported. A proof would reason generically in the two constants;
it is not attempted here.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### The consulted guard -/

/-- The guard code the arithmetized evaluator consults at the node `.search k φ p q` in the
frame `(me, opp)`: the template code of `φ` filled with the players' descriptions. -/
noncomputable def guardOf (φ : PD.Formula) (me opp : PD.Prog) : ℕ :=
  guardCode (tcode φ) (pcode me) (pcode opp)

lemma guardOf_eq_quote_trAt (φ : PD.Formula) (me opp : PD.Prog) :
    guardOf φ me opp = ⌜trAt me opp φ⌝ :=
  (quote_trAt me opp φ).symm

/-- On the fragment the consulted guard IS the template code of the CLOSED instantiation
`φ.subst me opp` — the formula the engine's `search_t`/`search_f` premises are about. -/
lemma guardOf_eq_tcode_subst {me opp : PD.Prog} (hme : me ≠ .self ∧ me ≠ .opp)
    (hopp : opp ≠ .self ∧ opp ≠ .opp) (φ : PD.Formula) (h : fragF φ = true) :
    guardOf φ me opp = tcode (φ.subst me opp) := by
  rw [tcode_subst hme hopp φ h, gsubst_of_template (isSemiformula_tcode φ)]
  rfl

/-! ### The oracle hypotheses -/

/-- Bounded D1 on the consulted guards: an engine derivation `⊢_k` of the closed guard yields
a `TAct`-proof of length `≤ k` of its realization. -/
def GuardAgreeT : Prop :=
  ∀ (φ : PD.Formula) (me opp : PD.Prog) (k : ℕ),
    PD.Pf k (φ.subst me opp) → LenProvableV TAct k (guardOf φ me opp)

/-- The negative direction: an engine refutation `⊢_m ¬guard` excludes a `TAct`-proof of
length `≤ k` of the realization, at every `k`. -/
def GuardAgreeF : Prop :=
  ∀ (φ : PD.Formula) (me opp : PD.Prog) (k m : ℕ),
    PD.Pf m (.neg (φ.subst me opp)) → ¬ LenProvableV TAct k (guardOf φ me opp)

/-- **Soundness of a found guard**: if the arithmetized evaluator finds the guard, its
realization is TRUE in `ℕ` (`TAct` is sound: `models_TAct`). -/
theorem models_trAt_of_lenProvableV {φ : PD.Formula} {me opp : PD.Prog} {k : ℕ}
    (h : LenProvableV TAct k (guardOf φ me opp)) : ℕ↓[LAct] ⊧ trAt me opp φ := by
  rw [guardOf_eq_quote_trAt, lenProvableV_nat] at h
  exact models_of_provable models_TAct (provable_iff_provable.mp h.provable)

/-- What engine soundness gives on the OTHER side: a refuted closed guard is false in the
engine's reading. This is `Formula.interp`, a sentence about `play`, not about `EvalGraph`;
`GuardAgreeF` is not derived from it. -/
theorem not_interp_of_pf_neg {ψ : PD.Formula} {m : ℕ} (h : PD.Pf m (.neg ψ)) : ¬ ψ.interp :=
  PD.BaseTheorems.Pf_sound m (.neg ψ) h

/-! ### Actions -/

lemma actCode_inj {r a : PD.Action} (h : actCode r = actCode a) : r = a := by
  cases r <;> cases a <;> first | rfl | exact absurd h (by decide)

lemma actCode_eq_of_beq {r a : PD.Action} (h : (r == a) = true) : actCode r = actCode a := by
  cases r <;> cases a <;> first | rfl | exact absurd h (by decide)

lemma actCode_ne_of_beq_false {r a : PD.Action} (h : (r == a) = false) : actCode r ≠ actCode a := by
  cases r <;> cases a <;> first | exact absurd h (by decide) | decide

/-! ### The modest fragment -/

/-- The MODEST search-bot fragment: `fragP` with every `.sim` argument a placeholder or a
closed program (`atomicP`). This is the engine's modesty condition
(`Decidability/T43ModestUniverse`), true of the whole zoo, and it is what closes the
fragment under the `.sim` step's substitution. -/
def modestP : PD.Prog → Bool
  | .const _ => true
  | .self => true
  | .opp => true
  | .bot p => modestP p
  | .sim p q => atomicP p && atomicP q && modestP p && modestP q
  | .ite b _ p q => modestP b && modestP p && modestP q
  | .search _ φ p q => fragF φ && modestP p && modestP q
  | .tvote _ _ _ _ => false
  | .sys _ _ => false
  | .selfIdx _ => false

theorem fragP_of_modestP : ∀ p : PD.Prog, modestP p = true → fragP p = true
  | .const _, _ => rfl
  | .self, _ => rfl
  | .opp, _ => rfl
  | .bot p, h => fragP_of_modestP p h
  | .sim p q, h => by
    simp only [modestP, Bool.and_eq_true] at h
    simp only [fragP, fragP_of_modestP p h.1.2, fragP_of_modestP q h.2, Bool.and_self]
  | .ite b _ p q, h => by
    simp only [modestP, Bool.and_eq_true] at h
    simp only [fragP, fragP_of_modestP b h.1.1, fragP_of_modestP p h.1.2, fragP_of_modestP q h.2,
      Bool.and_self]
  | .search _ φ p q, h => by
    simp only [modestP, Bool.and_eq_true] at h
    simp only [fragP, h.1.1, fragP_of_modestP p h.1.2, fragP_of_modestP q h.2, Bool.and_self]
  | .tvote _ _ _ _, h => by simp [modestP] at h
  | .sys _ _, h => by simp [modestP] at h
  | .selfIdx _, h => by simp [modestP] at h

/-- A player is a program, not a pronoun (the side condition of `pcode_subst`). -/
def Proper (p : PD.Prog) : Prop := p ≠ .self ∧ p ≠ .opp

lemma proper_of_closedP {p : PD.Prog} (h : closedP p = true) : Proper p :=
  ⟨closedP_ne_self h, closedP_ne_opp h⟩

/-- `subst` of an atomic program is `me`, `opp`, or the (closed) program itself. -/
lemma subst_of_atomicP {p : PD.Prog} (hp : atomicP p = true) (me opp : PD.Prog) :
    p.subst me opp = me ∨ p.subst me opp = opp ∨ (closedP p = true ∧ p.subst me opp = p) := by
  simp only [atomicP, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl) | hc
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hc, subst_of_closedP p me opp hc⟩)

/-! ### The evaluation invariant -/

/-- The invariant carried along a derivation: proper modest players, a modest body, and
(when `sf = true`) no search node in any of them. -/
def Inv (sf : Bool) (me opp body : PD.Prog) : Prop :=
  Proper me ∧ Proper opp ∧ modestP me = true ∧ modestP opp = true ∧ modestP body = true ∧
    (sf = true → me.hasSearch = false ∧ opp.hasSearch = false ∧ body.hasSearch = false)

namespace Inv

variable {sf : Bool} {me op : PD.Prog}

lemma self (h : Inv sf me op .self) : Inv sf me op me :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.1, fun hs ↦ ⟨(h.2.2.2.2.2 hs).1, (h.2.2.2.2.2 hs).2.1, (h.2.2.2.2.2 hs).1⟩⟩

lemma opp (h : Inv sf me op .opp) : Inv sf me op op :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.1,
    fun hs ↦ ⟨(h.2.2.2.2.2 hs).1, (h.2.2.2.2.2 hs).2.1, (h.2.2.2.2.2 hs).2.1⟩⟩

lemma bot {p : PD.Prog} (h : Inv sf me op (.bot p)) : Inv sf me op p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun hs ↦ ⟨(h.2.2.2.2.2 hs).1, (h.2.2.2.2.2 hs).2.1, by simpa [PD.Prog.hasSearch] using (h.2.2.2.2.2 hs).2.2⟩⟩

lemma ite {b p q : PD.Prog} {a : PD.Action} (h : Inv sf me op (.ite b a p q)) :
    Inv sf me op b ∧ Inv sf me op p ∧ Inv sf me op q := by
  obtain ⟨hme, hop, hmm, hmo, hmb, hs⟩ := h
  simp only [modestP, Bool.and_eq_true] at hmb
  have hs' : sf = true → me.hasSearch = false ∧ op.hasSearch = false ∧
      (b.hasSearch = false ∧ p.hasSearch = false ∧ q.hasSearch = false) := fun h ↦ by
    obtain ⟨h1, h2, h3⟩ := hs h
    simp only [PD.Prog.hasSearch, Bool.or_eq_false_iff] at h3
    exact ⟨h1, h2, h3.1.1, h3.1.2, h3.2⟩
  exact ⟨⟨hme, hop, hmm, hmo, hmb.1.1, fun h ↦ ⟨(hs' h).1, (hs' h).2.1, (hs' h).2.2.1⟩⟩,
    ⟨hme, hop, hmm, hmo, hmb.1.2, fun h ↦ ⟨(hs' h).1, (hs' h).2.1, (hs' h).2.2.2.1⟩⟩,
    ⟨hme, hop, hmm, hmo, hmb.2, fun h ↦ ⟨(hs' h).1, (hs' h).2.1, (hs' h).2.2.2.2⟩⟩⟩

/-- A search node is never reached under `sf = true`; otherwise both branches inherit. -/
lemma search {k : ℕ} {φ : PD.Formula} {p q : PD.Prog} (h : Inv sf me op (.search k φ p q)) :
    sf = false ∧ Inv sf me op p ∧ Inv sf me op q := by
  obtain ⟨hme, hop, hmm, hmo, hmb, hs⟩ := h
  have hsf : sf = false := by
    cases sf
    · rfl
    · exact absurd (hs rfl).2.2 (by simp [PD.Prog.hasSearch])
  simp only [modestP, Bool.and_eq_true] at hmb
  refine ⟨hsf, ⟨hme, hop, hmm, hmo, hmb.1.2, ?_⟩, ⟨hme, hop, hmm, hmo, hmb.2, ?_⟩⟩ <;>
    exact fun h ↦ absurd (hsf.symm.trans h) Bool.false_ne_true

lemma tvote {v : PD.VoteList} {θ : ℕ} {p q : PD.Prog} (h : Inv sf me op (.tvote v θ p q)) : False := by
  simpa [modestP] using h.2.2.2.2.1

lemma sys {defs : PD.ProgList} {i : ℕ} (h : Inv sf me op (.sys defs i)) : False := by
  simpa [modestP] using h.2.2.2.2.1

/-- The body of a `.sim` node is one atomic program at a time. -/
lemma sim_arg {p : PD.Prog} (h : Inv sf me op p) (hp : atomicP p = true) :
    Proper (p.subst me op) ∧ modestP (p.subst me op) = true ∧
      (sf = true → (p.subst me op).hasSearch = false) := by
  obtain ⟨hme, hop, hmm, hmo, hmp, hs⟩ := h
  rcases subst_of_atomicP hp me op with e | e | ⟨hc, e⟩
  · rw [e]; exact ⟨hme, hmm, fun h ↦ (hs h).1⟩
  · rw [e]; exact ⟨hop, hmo, fun h ↦ (hs h).2.1⟩
  · rw [e]; exact ⟨proper_of_closedP hc, hmp, fun h ↦ (hs h).2.2⟩

/-- **Closure under the `.sim` step**: the new frame `(p.subst me op, q.subst me op)` with
body `p.subst me op` satisfies the invariant. -/
lemma sim {p q : PD.Prog} (h : Inv sf me op (.sim p q)) :
    Inv sf (p.subst me op) (q.subst me op) (p.subst me op) := by
  obtain ⟨hme, hop, hmm, hmo, hmb, hs⟩ := h
  simp only [modestP, Bool.and_eq_true] at hmb
  have hs' : sf = true → me.hasSearch = false ∧ op.hasSearch = false ∧
      (p.hasSearch = false ∧ q.hasSearch = false) := fun h ↦ by
    obtain ⟨h1, h2, h3⟩ := hs h
    simp only [PD.Prog.hasSearch, Bool.or_eq_false_iff] at h3
    exact ⟨h1, h2, h3⟩
  have hp : Inv sf me op p := ⟨hme, hop, hmm, hmo, hmb.1.2, fun h ↦ ⟨(hs' h).1, (hs' h).2.1, (hs' h).2.2.1⟩⟩
  have hq : Inv sf me op q := ⟨hme, hop, hmm, hmo, hmb.2, fun h ↦ ⟨(hs' h).1, (hs' h).2.1, (hs' h).2.2.2⟩⟩
  obtain ⟨pp, mp, sp⟩ := sim_arg hp hmb.1.1.1
  obtain ⟨pq, mq, sq⟩ := sim_arg hq hmb.1.1.2
  exact ⟨pp, pq, mp, mq, mp, fun h ↦ ⟨sp h, sq h, sp h⟩⟩

end Inv

/-! ### The theorem -/

/-- The core induction, with a flag `sf` that switches the oracle off (`sf = true`: the
invariant forbids search nodes, so the oracle hypotheses are vacuous). -/
theorem playsProof_evalGraph_core (sf : Bool) (hag : sf = false → GuardAgreeT)
    (hneg : sf = false → GuardAgreeF) {me opp body : PD.Prog} {a : PD.Action} {n : ℕ}
    (h : PD.PlaysProof me opp body a n) :
    Inv sf me opp body → ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) := by
  refine PD.PlaysProof.induct
    (motive := fun me opp body a n _ ↦
      Inv sf me opp body → ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · -- const
    intro me opp a _
    refine ⟨1, ?_⟩
    rw [pcode_const]
    exact (EvalGraph.const_iff (n := 0)).mpr rfl
  · -- self
    intro me opp a n _ ih hI
    obtain ⟨N, hN⟩ := ih (Inv.self hI)
    refine ⟨N + 1, ?_⟩
    rw [pcode_self, EvalGraph.self_iff]
    exact hN
  · -- opp
    intro me opp a n _ ih hI
    obtain ⟨N, hN⟩ := ih (Inv.opp hI)
    refine ⟨N + 1, ?_⟩
    rw [pcode_opp, EvalGraph.opp_iff]
    exact hN
  · -- bot
    intro me opp p a n _ ih hI
    obtain ⟨N, hN⟩ := ih (Inv.bot hI)
    refine ⟨N + 1, ?_⟩
    rw [pcode_bot, EvalGraph.bot_iff]
    exact hN
  · -- sim
    intro a n me opp p q _ ih hI
    obtain ⟨N, hN⟩ := ih (Inv.sim hI)
    have hp : fragP p = true := fragP_of_modestP p (by
      have := hI.2.2.2.2.1
      simp only [modestP, Bool.and_eq_true] at this
      exact this.1.2)
    have hq : fragP q = true := fragP_of_modestP q (by
      have := hI.2.2.2.2.1
      simp only [modestP, Bool.and_eq_true] at this
      exact this.2)
    rw [pcode_subst hI.1 hI.2.1 p hp, pcode_subst hI.1 hI.2.1 q hq] at hN
    refine ⟨N + 1, ?_⟩
    rw [pcode_sim, EvalGraph.sim_iff]
    exact hN
  · -- ite_t
    intro me opp b r m a' p a n q _ hr _ ihb ihp hI
    obtain ⟨hIb, hIp, _⟩ := Inv.ite hI
    obtain ⟨N₁, h₁⟩ := ihb hIb
    obtain ⟨N₂, h₂⟩ := ihp hIp
    refine ⟨max N₁ N₂ + 1, ?_⟩
    rw [pcode_ite, EvalGraph.ite_iff]
    exact ⟨actCode r, EvalGraph.mono_le (le_max_left _ _) h₁,
      Or.inl ⟨actCode_eq_of_beq hr, EvalGraph.mono_le (le_max_right _ _) h₂⟩⟩
  · -- ite_f
    intro me opp b r m a' q a n p _ hr _ ihb ihq hI
    obtain ⟨hIb, _, hIq⟩ := Inv.ite hI
    obtain ⟨N₁, h₁⟩ := ihb hIb
    obtain ⟨N₂, h₂⟩ := ihq hIq
    refine ⟨max N₁ N₂ + 1, ?_⟩
    rw [pcode_ite, EvalGraph.ite_iff]
    exact ⟨actCode r, EvalGraph.mono_le (le_max_left _ _) h₁,
      Or.inr ⟨actCode_ne_of_beq_false hr, EvalGraph.mono_le (le_max_right _ _) h₂⟩⟩
  · -- search_t
    intro k me opp p a n φ q hg _ ih hI
    obtain ⟨hsf, hIp, _⟩ := Inv.search hI
    obtain ⟨N, hN⟩ := ih hIp
    refine ⟨N + 1, ?_⟩
    rw [pcode_search, EvalGraph.search_iff]
    exact Or.inl ⟨hag hsf φ me opp k hg, hN⟩
  · -- search_f
    intro m me opp q a n k φ p hg _ ih hI
    obtain ⟨hsf, _, hIq⟩ := Inv.search hI
    obtain ⟨N, hN⟩ := ih hIq
    refine ⟨N + 1, ?_⟩
    rw [pcode_search, EvalGraph.search_iff]
    exact Or.inr ⟨hneg hsf φ me opp k m hg, hN⟩
  · -- voteZero_t
    intro me opp p q a n v _ _ hI
    exact (Inv.tvote hI).elim
  · -- voteNil_f
    intro me opp p q a n θ _ _ _ hI
    exact (Inv.tvote hI).elim
  · -- voteCons_c
    intro me opp p q a n θ w m I rest _ _ _ _ _ hI
    exact (Inv.tvote hI).elim
  · -- voteCons_d
    intro me opp p q a n θ w m I rest _ _ _ _ _ hI
    exact (Inv.tvote hI).elim
  · -- voteHigh_f
    intro me opp p q a n θ c v _ _ _ _ hI
    exact (Inv.tvote hI).elim
  · -- sysStep
    intro me opp defs i p a n _ _ _ hI
    exact (Inv.sys hI).elim

/-- **T2-AGENT.** Every evaluation certificate of `S` on the modest fragment is a run of the
arithmetized evaluator, at the same budgets, given agreement on the consulted `□_k` facts
(`GuardAgreeT`/`GuardAgreeF`). -/
theorem playsProof_evalGraph (hag : GuardAgreeT) (hneg : GuardAgreeF)
    {me opp body : PD.Prog} {a : PD.Action} {n : ℕ} (h : PD.PlaysProof me opp body a n)
    (hme : Proper me) (hopp : Proper opp)
    (hmme : modestP me = true) (hmopp : modestP opp = true) (hbody : modestP body = true) :
    ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) :=
  playsProof_evalGraph_core false (fun _ ↦ hag) (fun _ ↦ hneg) h
    ⟨hme, hopp, hmme, hmopp, hbody, fun h ↦ absurd h Bool.false_ne_true⟩

/-- **T2-AGENT, search-free, unconditional**: no guard is consulted, no oracle hypothesis. -/
theorem playsProof_evalGraph_searchFree
    {me opp body : PD.Prog} {a : PD.Action} {n : ℕ} (h : PD.PlaysProof me opp body a n)
    (hme : Proper me) (hopp : Proper opp)
    (hmme : modestP me = true) (hmopp : modestP opp = true) (hbody : modestP body = true)
    (hsme : me.hasSearch = false) (hsopp : opp.hasSearch = false) (hsbody : body.hasSearch = false) :
    ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a) :=
  playsProof_evalGraph_core true (fun h ↦ Bool.noConfusion h)
    (fun h ↦ Bool.noConfusion h) h
    ⟨hme, hopp, hmme, hmopp, hbody, fun _ ↦ ⟨hsme, hsopp, hsbody⟩⟩

/-- The atom form: an engine atom certificate `⊢_k (.plays me opp a)` is a run of the
arithmetized `play` (`eval me opp me`). -/
theorem atomProvable_evalGraph (hag : GuardAgreeT) (hneg : GuardAgreeF)
    {k : ℕ} {me opp : PD.Prog} {a : PD.Action} (h : PD.AtomProvable k (.plays me opp a))
    (hme : Proper me) (hopp : Proper opp) (hmme : modestP me = true) (hmopp : modestP opp = true) :
    ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode me) (actCode a) := by
  cases h with
  | mk hp _ => exact playsProof_evalGraph hag hneg hp hme hopp hmme hmopp hmme

/-- The atom form, search-free and unconditional. -/
theorem atomProvable_evalGraph_searchFree
    {k : ℕ} {me opp : PD.Prog} {a : PD.Action} (h : PD.AtomProvable k (.plays me opp a))
    (hme : Proper me) (hopp : Proper opp) (hmme : modestP me = true) (hmopp : modestP opp = true)
    (hsme : me.hasSearch = false) (hsopp : opp.hasSearch = false) :
    ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode me) (actCode a) := by
  cases h with
  | mk hp _ => exact playsProof_evalGraph_searchFree hp hme hopp hmme hmopp hmme hsme hsopp hsme

/-! ### The truth equation for the realized play-atom -/

lemma val_cl {n : ℕ} (t : ClosedSemiterm LAct 0) (b : Fin n → ℕ) :
    (cl t : Semiterm LAct Empty n).val (s := stdAct) b Empty.elim = t.val (s := stdAct) ![] Empty.elim := by
  unfold cl
  rw [Semiterm.val_castLE, Subsingleton.elim (fun x : Fin 0 ↦ b (x.castLE (Nat.zero_le n))) ![]]

lemma stdAct_rel_eq (v : Fin 2 → ℕ) :
    stdAct.rel (Language.Eq.eq : LAct.Rel 2) v ↔ v 0 = v 1 := Iff.rfl

/-- `relDesc` in `ℕ` is the graph of `relabel`. -/
lemma eval_relDesc (v : Fin 4 → ℕ) :
    Semiformula.Eval (s := stdAct) v Empty.elim relDesc ↔ v 0 = relabel (v 1) (v 2) (v 3) := by
  unfold relDesc
  rw [Semiformula.eval_lMap, stdAct_lMap_emb]
  exact relabel_defined.df v

/-- `evalG` in `ℕ` is `EvalGraph`. -/
lemma eval_evalG (v : Fin 5 → ℕ) :
    Semiformula.Eval (s := stdAct) v Empty.elim evalG ↔ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold evalG
  rw [Semiformula.eval_lMap, stdAct_lMap_emb]
  exact evalGraph_defined.df v

/-- A closed description in `ℕ` pins the program: `∃ d, d = dnum c ∧ x = relabel (dU c) (dW c) d`
is `x = c`. -/
lemma eval_closedDesc (c : ℕ) (b : Fin 7 → ℕ) :
    Semiformula.Eval (s := stdAct) b Empty.elim (closedDesc c) ↔ b 0 = c := by
  unfold closedDesc descF
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc, stdAct_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar, val_cl, val_dnumT]
  constructor
  · rintro ⟨x, rfl, h⟩
    rwa [relabel_val_desc] at h
  · intro h
    exact ⟨dnum c, rfl, by rw [relabel_val_desc]; exact h⟩

/-- **The truth equation**: for closed programs the realized play-atom holds in `ℕ` iff the
arithmetized `play` yields `a`; the frame `(me', opp')` is irrelevant. -/
theorem models_trAt_plays (me' opp' me opp : PD.Prog) (a : PD.Action)
    (hme : closedP me = true) (hopp : closedP opp = true) :
    ℕ↓[LAct] ⊧ trAt me' opp' (.plays me opp a) ↔
      ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode me) (actCode a) := by
  rw [models_iff]
  unfold trAt Semiformula.Realize
  rw [tmpl_plays]
  unfold progGraph
  rw [progAux_of_ne (closedP_ne_self hme) (closedP_ne_opp hme),
    progAux_of_ne (closedP_ne_self hopp) (closedP_ne_opp hopp)]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc, eval_evalG, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar,
    val_cl, val_actT]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

/-! ### Sanity: the zoo is modest -/

theorem modestP_DupocBot (k : ℕ) : modestP (PD.Bots.DupocBot k) = true := rfl

theorem proper_DupocBot (k : ℕ) : Proper (PD.Bots.DupocBot k) := ⟨by simp [PD.Bots.DupocBot], by simp [PD.Bots.DupocBot]⟩

end ArithS

