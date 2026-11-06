import ArithS.Outcome.Spec
import ArithS.Eval.TauCheck

/-!
# ArithS.Tau.Spec — the tau ROW statement of PA-`S'` (Phase 3 of `SPRIME_SOURCE_OF_TRUTH.md`)

The engine states every tau template's per-hypothesis content as a bit row
(`Tau/RowSpec.lean`: at every large budget, template `A`'s compiled instance at hypothesis `T` plays
`row T` against itself). This module is the same statement on CODES, for the arithmetized evaluator:

* `paperOrder` — the 16 paper templates, in the engine's order (the columns of the table in §3 of the
  design note);
* `instCode k A T := progCode (inst (tauZoo k) A T)` — the code of the engine's compiled instance;
* `bitPlays k A T a` — the engine's `RowSpec` frame on codes: some fuel runs the instance against
  itself (`.bot inst` on both sides, body `inst`) to the action `a`;
* `RowSpecA A order row` — for all large `k`, every slot of `order` plays its row value;
* `FloorBitA A T hinge a` — a FLOOR bit: for all large `k` at which the hinge fails, the slot plays `a`
  (the engine-side half of the base cell's dichotomy, `Outcome/Floor.lean`, on one tau bit).

A template's row theorem `@[tau_rowA] theorem <t>RowSpecA : RowSpecA .<t> <order> <t>RowA` states the
NON-floor slots (`order` = `paperOrder` minus the template's floor slots, a literal list); each floor
slot is its own `@[tau_floor_bitA] theorem <t>RowSpecA_<T>_floor`. `Tau/Lint.lean` validates both and
runs the census; `lake exe export_sprime_outcomes` writes `app/generated/sprime_tau_rows.json`.

`instCode` unfolds to the concrete compiled code for concrete templates: the engine's compiler is
structurally recursive (Gate D1), so `inst (tauZoo k) A T` reduces by `rfl` to a literal `Prog` with `k`
only in its `.search k` leaves, and `progCode` follows by `simp`. The unfolding lemmas for the shapes
Phase 3 needs are in §3 (`instCode_coop`, `instCode_tftSim`, …); the hypothesis-side instances the
rows consult (`instCode k T .coop`, `instCode k T .defect`, …) are unfolded in `Tau/Columns.lean`.
-/

namespace ArithS.Tau

open PD PD.Tau

/-! ### 1. The order, the instance codes, the bit -/

/-- The 16 paper templates, in the engine's order: the columns of the Phase-3 table (14 until 2026-10-19, when
`dupocTroll` — the Dupoc-hunting identity checker of the ladder zoo `body8+trolls` — joined after `cupodTroll`, and
`dimdid` — τ(CIMCIC)'s C/D transposition, the second implication prover of `body8+trolls+provers` — after `cimcic`). -/
def paperOrder : List Tmpl :=
  [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .dupocTroll, .cupod, .dimcid, .cimcic, .dimdid,
   .prudent, .maxconfidence, .minconfidence]

/-- The code of the engine's compiled instance of template `A` at hypothesis `T` and budget `k`. -/
noncomputable def instCode (k : ℕ) (A T : Tmpl) : ℕ := progCode (inst (tauZoo k) A T)

/-- **The tau bit on codes** — the engine's `RowSpec` frame: the instance, bot-wrapped on both sides,
runs its own body to the action `a` at some fuel. -/
def bitPlays (k : ℕ) (A T : Tmpl) (a : Action) : Prop :=
  ∃ N, EvalGraph N (pBot (instCode k A T)) (pBot (instCode k A T)) (instCode k A T) (actCode a)

/-- A bit for all large `k`. -/
def bitEventually (A T : Tmpl) (a : Action) : Prop := ∃ k₂, ∀ k, k₂ < k → bitPlays k A T a

/-- **The canonical tau row statement of PA-`S'`**: at every sufficiently large budget, template
`A`'s instance at each hypothesis `T ∈ order` plays `row T` (the engine's `PD.Tau.RowSpec`, on codes). -/
def RowSpecA (A : Tmpl) (order : List Tmpl) (row : Tmpl → Action) : Prop :=
  ∃ k₂, ∀ k, k₂ < k → ∀ T ∈ order, bitPlays k A T (row T)

/-- **A floor bit**: for all large `k` at which the hinge FAILS, the slot plays `a` — the engine-side
half of a dichotomy, on one tau bit. The hinge is written inline (`□[k] …`), as in `Outcome/Floors.lean`. -/
def FloorBitA (A T : Tmpl) (hinge : ℕ → Prop) (a : Action) : Prop :=
  ∃ k₂, ∀ k, k₂ < k → ¬ hinge k → bitPlays k A T a

/-! ### 2. Constructors -/

theorem bitPlays_of_evalGraph {k : ℕ} {A T : Tmpl} {a : Action} {N : ℕ}
    (h : EvalGraph N (pBot (instCode k A T)) (pBot (instCode k A T)) (instCode k A T) (actCode a)) :
    bitPlays k A T a := ⟨N, h⟩

/-- A bit from a run on an explicit code equal to the instance code. -/
theorem bitPlays_of_eq {k : ℕ} {A T : Tmpl} {a : Action} {c : ℕ} (hc : instCode k A T = c)
    (h : ∃ N, EvalGraph N (pBot c) (pBot c) c (actCode a)) : bitPlays k A T a := by
  subst hc; exact h

/-- A bit is unique (`EvalGraph.unique'`). -/
theorem bitPlays_unique {k : ℕ} {A T : Tmpl} {a b : Action} (ha : bitPlays k A T a) (hb : bitPlays k A T b) :
    a = b := by
  obtain ⟨n, hn⟩ := ha; obtain ⟨m, hm⟩ := hb
  have := EvalGraph.unique' hn hm
  cases a <;> cases b <;> simp [actCode] at this ⊢

/-- A bit that holds at every `k` holds eventually. -/
theorem bitEventually.of_forall {A T : Tmpl} {a : Action} (h : ∀ k, bitPlays k A T a) : bitEventually A T a :=
  ⟨0, fun k _ ↦ h k⟩

/-- An eventual bit transported along a per-budget implication (a row's bit from a column's bit). -/
theorem bitEventually.mono {A T A' T' : Tmpl} {a a' : Action} (f : ∀ k, bitPlays k A T a → bitPlays k A' T' a')
    (h : bitEventually A T a) : bitEventually A' T' a' := by
  obtain ⟨k₂, h⟩ := h
  exact ⟨k₂, fun k hk ↦ f k (h k hk)⟩

/-- Two eventual bits combined. -/
theorem bitEventually.mono₂ {A T A' T' A'' T'' : Tmpl} {a a' a'' : Action}
    (f : ∀ k, bitPlays k A T a → bitPlays k A' T' a' → bitPlays k A'' T'' a'')
    (h : bitEventually A T a) (h' : bitEventually A' T' a') : bitEventually A'' T'' a'' := by
  obtain ⟨k₁, h⟩ := h; obtain ⟨k₂, h'⟩ := h'
  exact ⟨k₁ + k₂, fun k hk ↦ f k (h k (by omega)) (h' k (by omega))⟩

theorem RowSpecA.nil (A : Tmpl) (row : Tmpl → Action) : RowSpecA A [] row :=
  ⟨0, fun _ _ T hT ↦ absurd hT List.not_mem_nil⟩

/-- One more slot: an eventual bit at `T` extends a row over `order` to a row over `T :: order`. -/
theorem RowSpecA.cons {A T : Tmpl} {order : List Tmpl} {row : Tmpl → Action}
    (hT : bitEventually A T (row T)) (rest : RowSpecA A order row) : RowSpecA A (T :: order) row := by
  obtain ⟨k₁, h₁⟩ := hT; obtain ⟨k₂, h₂⟩ := rest
  refine ⟨k₁ + k₂, fun k hk T' hT' ↦ ?_⟩
  rcases List.mem_cons.mp hT' with rfl | hmem
  · exact h₁ k (by omega)
  · exact h₂ k (by omega) T' hmem

/-- The list form: one eventual bit per slot of the order. -/
theorem RowSpecA.of_forall {A : Tmpl} {row : Tmpl → Action} :
    ∀ (order : List Tmpl), (∀ T ∈ order, bitEventually A T (row T)) → RowSpecA A order row
  | [], _ => RowSpecA.nil A row
  | T :: rest, h =>
      RowSpecA.cons (h T (List.mem_cons_self ..))
        (RowSpecA.of_forall rest fun t ht ↦ h t (List.mem_cons_of_mem _ ht))

/-- A row's slot, read back as an eventual bit. -/
theorem RowSpecA.slot {A : Tmpl} {order : List Tmpl} {row : Tmpl → Action} (h : RowSpecA A order row)
    {T : Tmpl} (hT : T ∈ order) : bitEventually A T (row T) := by
  obtain ⟨k₂, h⟩ := h
  exact ⟨k₂, fun k hk ↦ h k hk T hT⟩

/-- A floor bit from an eventual `¬ hinge → bit`. -/
theorem FloorBitA.of_not_hinge {A T : Tmpl} {hinge : ℕ → Prop} {a : Action}
    (h : ∃ k₂, ∀ k, k₂ < k → ¬ hinge k → bitPlays k A T a) : FloorBitA A T hinge a := h

/-- A floor bit whose value is SETTLED (the hinge is the partner's question, not consulted on this side):
an eventual bit is a floor bit for any hinge. -/
theorem FloorBitA.of {A T : Tmpl} (hinge : ℕ → Prop) {a : Action} (h : bitEventually A T a) :
    FloorBitA A T hinge a := by
  obtain ⟨k₂, h⟩ := h
  exact ⟨k₂, fun k hk _ ↦ h k hk⟩

/-- A floor bit whose hinge always fails beyond some budget is an eventual bit. -/
theorem FloorBitA.eventual_of_not_hinge {A T : Tmpl} {hinge : ℕ → Prop} {a : Action}
    (h : FloorBitA A T hinge a) (hn : ∃ k₁, ∀ k, k₁ < k → ¬ hinge k) : bitEventually A T a := by
  obtain ⟨k₀, h⟩ := h; obtain ⟨k₁, hn⟩ := hn
  exact ⟨k₀ + k₁, fun k hk ↦ h k (by omega) (hn k (by omega))⟩

/-! ### 3. The compiled instances of the seven simple templates, on codes

Each lemma is the engine's `inst_<t>_peel` (`Tau/Zoo.lean`, by `rfl`) read through `progCode`. The
hypothesis-side instance `instCode k T B` the row consults is left folded; `Tau/Columns.lean` unfolds it
per `(T, B)`. -/

/-- Constants ignore their hypothesis. -/
theorem instCode_coop (k : ℕ) (T : Tmpl) : instCode k .coop T = pConst 0 := by
  unfold instCode; rw [inst_coop_peel]; simp [actCode]

theorem instCode_defect (k : ℕ) (T : Tmpl) : instCode k .defect T = pConst 1 := by
  unfold instCode; rw [inst_defect_peel]; simp [actCode]

/-- τ(TFTSim): one run-stage on the hypothesis's instance at the cooperator. -/
theorem instCode_tftSim (k : ℕ) (T : Tmpl) : instCode k .tftSim T =
    pIte (pSim (pBot (instCode k T .coop)) (pBot (instCode k T .coop))) 0 (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_tftSim_peel]; simp [actCode]

/-- τ(DBot): one run-stage on the hypothesis's instance at the defector, firing on cooperation. -/
theorem instCode_dbot (k : ℕ) (T : Tmpl) : instCode k .dbot T =
    pIte (pSim (pBot (instCode k T .defect)) (pBot (instCode k T .defect))) 0 (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dbot_peel]; simp [actCode]

/-- τ(OBot): two defection watches (`test = D`) on the instances at the cooperator and the defector. -/
theorem instCode_obot (k : ℕ) (T : Tmpl) : instCode k .obot T =
    pIte (pSim (pBot (instCode k T .coop)) (pBot (instCode k T .coop))) 1 (pConst 1)
      (pIte (pSim (pBot (instCode k T .defect)) (pBot (instCode k T .defect))) 1 (pConst 1) (pConst 0)) := by
  unfold instCode; rw [inst_obot_peel]; simp [actCode]

/-- τ(EBot): the three-stage run cascade on the instances at the defector, the cooperator and the mirror. -/
theorem instCode_ebot (k : ℕ) (T : Tmpl) : instCode k .ebot T =
    pIte (pSim (pBot (instCode k T .defect)) (pBot (instCode k T .defect))) 0 (pConst 1)
      (pIte (pSim (pBot (instCode k T .coop)) (pBot (instCode k T .coop))) 0 (pConst 0)
        (pIte (pSim (pBot (instCode k T .mirror)) (pBot (instCode k T .mirror))) 0 (pConst 0) (pConst 1))) := by
  unfold instCode; rw [inst_ebot_peel]; simp [actCode]

/-- τ(CupodTroll) at the one hypothesis it recognises: the decidably TRUE identity, then-branch `D`. -/
theorem instCode_cupodTroll_cupod (k : ℕ) : instCode k .cupodTroll .cupod =
    pSearch k (templateCode (.eq (.const .C) (.const .C))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupodTroll_peel_cupod]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- …and at every other hypothesis: the decidably FALSE identity, else-branch `C`. -/
theorem instCode_cupodTroll (k : ℕ) (T : Tmpl) (h : T ≠ .cupod) : instCode k .cupodTroll T =
    pSearch k (templateCode (.eq (.const .C) (.const .D))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupodTroll_peel k T h]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- τ(DupocTroll) (2026-10-19) at a hypothesis with Dupoc's SOURCE (`.dupoc` and the two natives): the decidably
TRUE identity, then-branch `D`. -/
theorem instCode_dupocTroll_rec (k : ℕ) (T : Tmpl) (h : tmplSpec T = tauDupocSpec) : instCode k .dupocTroll T =
    pSearch k (templateCode (.eq (.const .C) (.const .C))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dupocTroll_peel_rec k T h]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- …and at every hypothesis whose source is not Dupoc's: the decidably FALSE identity, else-branch `C`. -/
theorem instCode_dupocTroll (k : ℕ) (T : Tmpl) (h : tmplSpec T ≠ tauDupocSpec) : instCode k .dupocTroll T =
    pSearch k (templateCode (.eq (.const .C) (.const .D))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dupocTroll_peel k T h]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

end ArithS.Tau
