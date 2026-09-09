import PrisonersDilemma.Base.Soundness

/-!
# Tau/Vote — the uniform tau player and its vote interface (refined Def 4, 2026-08-18)

**Scope (narrowed 2026-08-19):** the machinery CONTRACT only — the probe atoms, the
player, the positional bits interface (`VoteBits`/`eval_tvote_of_bits`/
`tauPlayer_phase_bits`), and the point-mass coherence anchor. Everything PROVED about
compiled shapes (play-lemmas, false-bit lemmas, bridges, glue) lives in
`Tau/Theorems/Helpers.lean`, per the Tau-layout doctrine; `eval_det` was promoted to
`Base/ValuationSoundness.lean`.

The **refined Def 4** (`Research/Notes/TAUBOTS.md`) is the uniform structural
SOURCE LIFT τ: lift base bot `A`'s code constructor-by-constructor, and let the player
take ONE weighted vote over the COMPOUND per-hypothesis decisions

```
TauA(B₁…Bₙ; w⃗, θ)  =  C   iff   Σ { wᵢ : inst(A, δ_Bᵢ) plays C } ≥ θ
```

read by EVALUATION. Two consequences shape this file:

* **One player definition for every bot.** `tauPlayer v θ` is the whole σ-level; all
  per-bot content lives in the DECISION VECTOR `v`. This replaces the four ad-hoc
  shapes of the 2026-08-11/12 layer (single `tsearch`, nested `tsearch`, `iteTree`),
  whose per-bot geometry is exactly what let the retracted "crowd-exploiter" TauEBot
  masquerade as a lift of EBot.
* **Two producers of vectors, one vote.** τ produces the vector of a LIFTED base bot
  (each entry = that bot's entire decision procedure at point mass); signal-NATIVE
  bots (e.g. "cooperate iff the Coop hypothesis carries more than half the mass")
  hand-write theirs. Both feed the same `tauPlayer`, the same peel lemma, and the same
  phase theorem.

The Löb/floor structure is untouched and lives one level down, INSIDE the entries —
`proofSearch` appears exactly where the lifted base bot's own code puts it.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The probe atom -/

/-- Def-4 probe atom for a closed instance `I`: "`I`, frozen, plays C against
    itself". `.bot`-freezing is the subst barrier (a bare slot would let the
    enclosing player's `subst` capture the instance's internals); the second slot is
    inert for `.opp`-free programs; instance-vs-itself is the canonical closed
    choice. This is ALSO the frame `.tvote` entries run in — the two were aligned by
    design, so every probe fact doubles as an entry fact. -/
def probe (I : Prog) : Formula := .plays (.bot I) (.bot I) Action.C

/-- Probe atoms are closed: `subst` cannot touch a `.bot`-frozen instance. -/
theorem probe_subst (I me o : Prog) : (probe I).subst me o = probe I := rfl

/-- The DEFECTION probe atom — "`I`, frozen, plays D against itself". Added with the
    `test` field (2026-08-18): GuardianBot's stage asks `S` for defection (`⊢_k probeD`)
    rather than cooperation. -/
def probeD (I : Prog) : Formula := .plays (.bot I) (.bot I) Action.D

theorem probeD_subst (I me o : Prog) : (probeD I).subst me o = probeD I := rfl

/-- **The IMPLICATION probe atom** (2026-08-20, the `.impl`-guard fragment
    extension): "if `A`'s instance plays `test` against `B`'s, then `B`'s plays
    `test` against `A`'s" — both sides frozen, so the whole formula is closed.

    This is the tau reading of CIMCIC's guard
    `.impl (.plays .self .opp C) (.plays .opp .self C)`: in the lift, "me" is the
    probing instance and "the opponent" is the probed one, and BOTH are `.bot`-frozen
    terms rather than pronouns. Unlike `probe`/`probeD` the two slots differ, so the
    atom takes both instances. -/
def probeImpl (I J : Prog) (test : Action) : Formula :=
  .impl (.plays (.bot I) (.bot J) test) (.plays (.bot J) (.bot I) test)

theorem probeImpl_subst (I J : Prog) (test : Action) (me o : Prog) :
    (probeImpl I J test).subst me o = probeImpl I J test := rfl

/-! ## The uniform player -/

/-- **THE tau player**: vote over the decision vector `v` with caution threshold `θ`.
    Constant branches, so the play is `C` exactly when the C-mass reaches `θ`. -/
def tauPlayer (v : VoteList) (θ : Nat) : Prog :=
  .tvote v θ (.const .C) (.const .D)

/-! ### Mass from an explicit bit list

Rather than defining a global valuation function (which forces the elaborator to decide
term equality between large cascade terms), a bot supplies its entries' actions
POSITIONALLY. `massOf` computes the C-mass of such a list, and `VoteBits` ties it to
the vector. This is the practical interface the per-bot phase theorems use. -/

/-- The C-mass of a vector whose entries' actions are given positionally. -/
def massOf : List (Nat × Action) → Nat
  | [] => 0
  | (w, a) :: rest => (if a == Action.C then w else 0) + massOf rest

/-- The C-mass of a BIT TABLE over a zoo enumeration — the fold form of every regime
    mass: `bitMass w b order = Σ { w T : T ∈ order, b T = .C }`. On a concrete
    enumeration it reduces (via `massOf`) to the literal weight sum, so the
    hand-written regime masses are its display forms. -/
def bitMass {ι : Type} (w : ι → Nat) (b : ι → Action) (order : List ι) : Nat :=
  massOf (order.map fun T => (w T, b T))

/-- "This vector's entries play these actions, in order." -/
inductive VoteBits : VoteList → List (Nat × Action) → Prop where
  | nil : VoteBits .nil []
  | cons {w : Nat} {I : Prog} {rest : VoteList} {a : Action} {bs : List (Nat × Action)} :
      (∃ N, eval N (.bot I) (.bot I) I = some a) → VoteBits rest bs →
      VoteBits (.cons w I rest) ((w, a) :: bs)

/-- The peel workhorse, restated over positional bits — no valuation function, so no
    term-equality obligations anywhere. -/
theorem eval_tvote_of_bits (me opponent : Prog) :
    ∀ (v : VoteList) (bs : List (Nat × Action)) (θ : Nat), VoteBits v bs →
      ∃ N, eval N me opponent (tauPlayer v θ)
        = some (if θ ≤ massOf bs then Action.C else Action.D)
  | .nil, _, θ, .nil => by
      cases θ with
      | zero =>
          refine ⟨2, ?_⟩
          rw [if_pos (Nat.zero_le _), tauPlayer, eval_tvote_zero 1]; rfl
      | succ m =>
          refine ⟨2, ?_⟩
          rw [if_neg (by simp [massOf]), tauPlayer, eval_tvote_nil 1 (by omega)]; rfl
  | .cons w I rest, _, θ, .cons (a := a) (bs := bs) hI hrest => by
      cases θ with
      | zero =>
          refine ⟨2, ?_⟩
          rw [if_pos (Nat.zero_le _), tauPlayer, eval_tvote_zero 1]; rfl
      | succ m =>
          obtain ⟨NI, hNI⟩ := hI
          cases a with
          | C =>
              obtain ⟨Nb, hNb⟩ := eval_tvote_of_bits me opponent rest _ (m + 1 - w) hrest
              refine ⟨max NI Nb + 1, ?_⟩
              rw [tauPlayer, eval_tvote_cons_c (max NI Nb) (by omega)
                    (eval_mono_le hNI _ (Nat.le_max_left _ _))]
              have hiff : (m + 1 - w ≤ massOf bs) ↔ (m + 1 ≤ massOf ((w, Action.C) :: bs)) := by
                simp only [massOf, if_pos (by decide : ((Action.C == Action.C) = true))]
                omega
              rw [← if_congr hiff rfl rfl]
              exact eval_mono_le hNb _ (Nat.le_max_right _ _)
          | D =>
              obtain ⟨Nb, hNb⟩ := eval_tvote_of_bits me opponent rest _ (m + 1) hrest
              refine ⟨max NI Nb + 1, ?_⟩
              rw [tauPlayer, eval_tvote_cons_d (max NI Nb) (by omega)
                    (eval_mono_le hNI _ (Nat.le_max_left _ _))]
              have hiff : (m + 1 ≤ massOf bs) ↔ (m + 1 ≤ massOf ((w, Action.D) :: bs)) := by
                simp only [massOf,
                  if_neg (by decide : ¬ ((Action.D == Action.C) = true))]
                omega
              rw [← if_congr hiff rfl rfl]
              exact eval_mono_le hNb _ (Nat.le_max_right _ _)

/-- **The α-phase theorem over positional bits** — the interface every per-bot theorem
    below uses. -/
theorem tauPlayer_phase_bits {v : VoteList} {bs : List (Nat × Action)} (θ : Nat)
    (hbits : VoteBits v bs) (opponent : Prog) :
    (θ ≤ massOf bs → ∃ N, play N (tauPlayer v θ) opponent = some .C)
    ∧ (¬ θ ≤ massOf bs → ∃ N, play N (tauPlayer v θ) opponent = some .D) := by
  refine ⟨fun hθ => ?_, fun hθ => ?_⟩
  · obtain ⟨N, hN⟩ := eval_tvote_of_bits (tauPlayer v θ) opponent v bs θ hbits
    exact ⟨N, by rw [play, hN, if_pos hθ]⟩
  · obtain ⟨N, hN⟩ := eval_tvote_of_bits (tauPlayer v θ) opponent v bs θ hbits
    exact ⟨N, by rw [play, hN, if_neg hθ]⟩

/-! ## The MAX aggregator — native players (2026-08-27)

A tau player is a (bit row, aggregator) pair. Every LIFT aggregates by `sum ≥ θ`
(`tauPlayer`: the signal's C-mass reaches the threshold). A NATIVE player may
aggregate differently; the first is MaxConfidenceBot's **`max ≥ θ`** — "some SINGLE
hypothesis carrying at least θ of the signal on its own plays C" — realized as a
chain of ONE-entry votes: a one-entry `.tvote` fires iff its entry plays C AND
`θ ≤ w` (the residual must hit zero), otherwise the chain falls to the next link.
No new language primitive; entries are frozen exactly as in `tauPlayer`. The max is
NOT a threshold of any C-mass (`maxconfidence_not_linear`, `TauMaxConfidence/Phase.lean`)
— which is what makes MaxConfidenceBot the lift of no base bot. -/

/-- The max-aggregated player over a decision vector. -/
def maxPlayer (θ : Nat) : VoteList → Prog
  | .nil           => .const .D
  | .cons w I rest => .tvote (.cons w I .nil) θ (.const .C) (maxPlayer θ rest)

/-- The max aggregator over positional bits: some entry carries `≥ θ` and plays C —
    or `θ = 0` on a non-empty list (a zero threshold fires the first vote before
    any entry is read, exactly as `tauPlayer` at `θ = 0`). -/
def maxHit (θ : Nat) : List (Nat × Action) → Bool
  | [] => false
  | (w, a) :: rest =>
      (decide (θ = 0) || (decide (θ ≤ w) && decide (a = Action.C))) || maxHit θ rest

theorem maxHit_true_iff (θ : Nat) : ∀ bs : List (Nat × Action),
    maxHit θ bs = true ↔ (θ = 0 ∧ bs ≠ []) ∨ ∃ p ∈ bs, θ ≤ p.1 ∧ p.2 = Action.C
  | [] => by simp [maxHit]
  | (w, a) :: rest => by
      rw [maxHit, Bool.or_eq_true, Bool.or_eq_true, maxHit_true_iff θ rest]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, ne_eq,
        reduceCtorEq, not_false_eq_true, and_true]
      constructor
      · rintro ((h0 | ⟨hw, ha⟩) | (⟨h0, _⟩ | ⟨p, hp, hpw, hpa⟩))
        · exact Or.inl h0
        · exact Or.inr ⟨(w, a), Or.inl rfl, hw, ha⟩
        · exact Or.inl h0
        · exact Or.inr ⟨p, Or.inr hp, hpw, hpa⟩
      · rintro (h0 | ⟨p, (rfl | hp), hpw, hpa⟩)
        · exact Or.inl (Or.inl h0)
        · exact Or.inl (Or.inr ⟨hpw, hpa⟩)
        · exact Or.inr (Or.inr ⟨p, hp, hpw, hpa⟩)

/-- The peel workhorse for the max chain — the twin of `eval_tvote_of_bits`. -/
theorem eval_maxPlayer_of_bits (me opponent : Prog) :
    ∀ (v : VoteList) (bs : List (Nat × Action)) (θ : Nat), VoteBits v bs →
      ∃ N, eval N me opponent (maxPlayer θ v)
        = some (if maxHit θ bs then Action.C else Action.D)
  | .nil, _, _, .nil => ⟨1, rfl⟩
  | .cons w I rest, _, θ, .cons (a := a) (bs := bs) hI hrest => by
      obtain ⟨NI, hNI⟩ := hI
      obtain ⟨Nr, hNr⟩ := eval_maxPlayer_of_bits me opponent rest bs θ hrest
      refine ⟨max NI Nr + 3, ?_⟩
      have hI' : eval (max NI Nr + 2) (.bot I) (.bot I) I = some a :=
        eval_mono_le hNI _ (by omega)
      have hr' : eval (max NI Nr + 1) me opponent (maxPlayer θ rest)
          = some (if maxHit θ bs then Action.C else Action.D) :=
        eval_mono_le hNr _ (by omega)
      cases θ with
      | zero =>
          rw [maxPlayer, eval_tvote_zero (max NI Nr + 2)]
          simp [maxHit, eval]
      | succ m =>
          cases a with
          | C =>
              rw [maxPlayer, eval_tvote_cons_c (max NI Nr + 2) (by omega) hI']
              by_cases hw : m + 1 ≤ w
              · have h0 : m + 1 - w = 0 := by omega
                rw [h0, eval_tvote_zero (max NI Nr + 1)]
                simp [maxHit, hw, eval]
              · rw [eval_tvote_nil (max NI Nr + 1) (by omega), hr']
                simp [maxHit, hw]
          | D =>
              rw [maxPlayer, eval_tvote_cons_d (max NI Nr + 2) (by omega) hI',
                  eval_tvote_nil (max NI Nr + 1) (by omega), hr']
              simp [maxHit]

/-- **The phase theorem of the max chain** over positional bits. -/
theorem maxPlayer_phase_bits {v : VoteList} {bs : List (Nat × Action)} (θ : Nat)
    (hbits : VoteBits v bs) (opponent : Prog) :
    (maxHit θ bs = true → ∃ N, play N (maxPlayer θ v) opponent = some .C)
    ∧ (maxHit θ bs = false → ∃ N, play N (maxPlayer θ v) opponent = some .D) := by
  refine ⟨fun hθ => ?_, fun hθ => ?_⟩
  · obtain ⟨N, hN⟩ := eval_maxPlayer_of_bits (maxPlayer θ v) opponent v bs θ hbits
    exact ⟨N, by rw [play, hN, if_pos hθ]⟩
  · obtain ⟨N, hN⟩ := eval_maxPlayer_of_bits (maxPlayer θ v) opponent v bs θ hbits
    exact ⟨N, by rw [play, hN, if_neg (by simp [hθ])]⟩

/-! ## The MIN aggregator — the worst-case dual (2026-09-01)

MinConfidenceBot is MaxConfidenceBot's C/D-transposition dual, the Gilboa–Schmeidler
pessimist: **cooperate iff NO single hypothesis carrying at least θ of the signal on
its own FAILS my test** — equivalently, every θ-credible hypothesis passes it. Where
the max player cooperates on one credible cooperator, the min player defects on one
credible defector. Realized as the same chain of one-entry `.tvote`s, with the
polarity flipped: each vote FALLS THROUGH when its entry plays C and commits `D` when
it plays D. An entry is CREDIBLE when its weight is positive and at least θ (a
weightless entry carries nothing and can block nothing); non-credible entries emit no
node at all — the gate is compile-time, exactly as the chain structure itself is,
because weights are data. θ = 0 therefore behaves as θ = 1 ("any positive-weight
defector blocks"), the dual of `maxHit`'s vacuous-fire corner. Like the max, the min
is NOT a threshold of any C-mass (`minconfidence_not_linear`,
`TauMinConfidence/Phase.lean`) — the app-side dial maps by `θ_credible ↔ 1 − α`. -/

/-- The min-aggregated (worst-case) player over a decision vector: defect on the
    first credible entry that plays D, cooperate when none does. -/
def minPlayer (θ : Nat) : VoteList → Prog
  | .nil           => .const .C
  | .cons w I rest =>
      if 1 ≤ w ∧ θ ≤ w
      then .tvote (.cons w I .nil) 1 (minPlayer θ rest) (.const .D)
      else minPlayer θ rest

/-- The min aggregator over positional bits: some credible entry plays D. -/
def minMiss (θ : Nat) : List (Nat × Action) → Bool
  | [] => false
  | (w, a) :: rest =>
      (decide (1 ≤ w) && decide (θ ≤ w) && decide (a = Action.D)) || minMiss θ rest

theorem minMiss_true_iff (θ : Nat) : ∀ bs : List (Nat × Action),
    minMiss θ bs = true ↔ ∃ p ∈ bs, 1 ≤ p.1 ∧ θ ≤ p.1 ∧ p.2 = Action.D
  | [] => by simp [minMiss]
  | (w, a) :: rest => by
      rw [minMiss, Bool.or_eq_true, minMiss_true_iff θ rest]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (⟨⟨h1, hθ⟩, ha⟩ | ⟨p, hp, h1, hθ, ha⟩)
        · exact ⟨(w, a), Or.inl rfl, h1, hθ, ha⟩
        · exact ⟨p, Or.inr hp, h1, hθ, ha⟩
      · rintro ⟨p, (rfl | hp), h1, hθ, ha⟩
        · exact Or.inl ⟨⟨h1, hθ⟩, ha⟩
        · exact Or.inr ⟨p, hp, h1, hθ, ha⟩

/-- The peel workhorse for the min chain — the polarity-flipped twin of
    `eval_maxPlayer_of_bits`. -/
theorem eval_minPlayer_of_bits (me opponent : Prog) :
    ∀ (v : VoteList) (bs : List (Nat × Action)) (θ : Nat), VoteBits v bs →
      ∃ N, eval N me opponent (minPlayer θ v)
        = some (if minMiss θ bs then Action.D else Action.C)
  | .nil, _, _, .nil => ⟨1, rfl⟩
  | .cons w I rest, _, θ, .cons (a := a) (bs := bs) hI hrest => by
      obtain ⟨NI, hNI⟩ := hI
      obtain ⟨Nr, hNr⟩ := eval_minPlayer_of_bits me opponent rest bs θ hrest
      by_cases hc : 1 ≤ w ∧ θ ≤ w
      · refine ⟨max NI Nr + 3, ?_⟩
        have hI' : eval (max NI Nr + 2) (.bot I) (.bot I) I = some a :=
          eval_mono_le hNI _ (by omega)
        have hr' : eval (max NI Nr + 1) me opponent (minPlayer θ rest)
            = some (if minMiss θ bs then Action.D else Action.C) :=
          eval_mono_le hNr _ (by omega)
        cases a with
        | C =>
            rw [minPlayer, if_pos hc, eval_tvote_cons_c (max NI Nr + 2) (by omega) hI']
            have h0 : 1 - w = 0 := by omega
            rw [h0, eval_tvote_zero (max NI Nr + 1), hr']
            simp [minMiss]
        | D =>
            rw [minPlayer, if_pos hc, eval_tvote_cons_d (max NI Nr + 2) (by omega) hI',
                eval_tvote_nil (max NI Nr + 1) (by omega)]
            simp [minMiss, hc.1, hc.2, eval]
      · refine ⟨Nr, ?_⟩
        rw [minPlayer, if_neg hc, hNr]
        have hb : (decide (1 ≤ w) && decide (θ ≤ w) && decide (a = Action.D)) = false := by
          rcases Decidable.not_and_iff_or_not.mp hc with h | h <;> simp [h]
        simp [minMiss, hb]

/-- **The phase theorem of the min chain** over positional bits. -/
theorem minPlayer_phase_bits {v : VoteList} {bs : List (Nat × Action)} (θ : Nat)
    (hbits : VoteBits v bs) (opponent : Prog) :
    (minMiss θ bs = false → ∃ N, play N (minPlayer θ v) opponent = some .C)
    ∧ (minMiss θ bs = true → ∃ N, play N (minPlayer θ v) opponent = some .D) := by
  refine ⟨fun hθ => ?_, fun hθ => ?_⟩
  · obtain ⟨N, hN⟩ := eval_minPlayer_of_bits (minPlayer θ v) opponent v bs θ hbits
    exact ⟨N, by rw [play, hN, if_neg (by simp [hθ])]⟩
  · obtain ⟨N, hN⟩ := eval_minPlayer_of_bits (minPlayer θ v) opponent v bs θ hbits
    exact ⟨N, by rw [play, hN, if_pos hθ]⟩

/-! ## Prefix commitment and divergent tails (τ(Mirror), 2026-08-24)

A vote COMMITS as soon as its residual threshold hits zero, without consulting
the remaining entries — so a non-terminating entry at the END of the list only
sinks the vote when the prefix's C-mass falls short of `θ`. This is what makes
τ(Mirror) — whose own diagonal entry diverges — a bot with a genuine phase: `C`
below its prefix mass, and honestly `none` (not `D`) above it. -/

/-- Append on vote lists. -/
def _root_.PD.VoteList.app : VoteList → VoteList → VoteList
  | .nil, v => v
  | .cons w I rest, v => .cons w I (rest.app v)

/-- If the PREFIX's C-mass reaches `θ`, the vote plays `C` whatever the tail. -/
theorem eval_tvote_prefix_C (me opponent : Prog) :
    ∀ (v : VoteList) (bs : List (Nat × Action)) (θ : Nat) (tail : VoteList),
      VoteBits v bs → θ ≤ massOf bs →
      ∃ N, eval N me opponent (tauPlayer (v.app tail) θ) = some Action.C
  | .nil, _, θ, tail, .nil, hθ => by
      simp only [massOf] at hθ
      have h0 : θ = 0 := by omega
      subst h0
      exact ⟨2, by rw [tauPlayer, eval_tvote_zero 1]; rfl⟩
  | .cons w I rest, _, θ, tail, .cons (a := a) (bs := bs) hI hrest, hθ => by
      cases θ with
      | zero => exact ⟨2, by rw [tauPlayer, eval_tvote_zero 1]; rfl⟩
      | succ m =>
          obtain ⟨NI, hNI⟩ := hI
          cases a with
          | C =>
              have hθ' : m + 1 - w ≤ massOf bs := by
                simp only [massOf, if_pos (by decide : ((Action.C == Action.C) = true))] at hθ
                omega
              obtain ⟨Nb, hNb⟩ := eval_tvote_prefix_C me opponent rest bs (m + 1 - w) tail hrest hθ'
              refine ⟨max NI Nb + 1, ?_⟩
              rw [VoteList.app, tauPlayer, eval_tvote_cons_c (max NI Nb) (by omega)
                    (eval_mono_le hNI _ (Nat.le_max_left _ _))]
              exact eval_mono_le hNb _ (Nat.le_max_right _ _)
          | D =>
              have hθ' : m + 1 ≤ massOf bs := by
                simp only [massOf, if_neg (by decide : ¬ ((Action.D == Action.C) = true))] at hθ
                omega
              obtain ⟨Nb, hNb⟩ := eval_tvote_prefix_C me opponent rest bs (m + 1) tail hrest hθ'
              refine ⟨max NI Nb + 1, ?_⟩
              rw [VoteList.app, tauPlayer, eval_tvote_cons_d (max NI Nb) (by omega)
                    (eval_mono_le hNI _ (Nat.le_max_left _ _))]
              exact eval_mono_le hNb _ (Nat.le_max_right _ _)

/-- If the prefix's C-mass falls short of `θ` and the (single) trailing entry
    DIVERGES, the vote is `none` at every fuel. -/
theorem eval_tvote_prefix_none (me opponent : Prog) {w' : Nat} {J : Prog}
    (hJ : ∀ N, eval N (.bot J) (.bot J) J = none) :
    ∀ (v : VoteList) (bs : List (Nat × Action)) (θ : Nat),
      VoteBits v bs → ¬ θ ≤ massOf bs →
      ∀ N, eval N me opponent (tauPlayer (v.app (.cons w' J .nil)) θ) = none
  | .nil, _, θ, .nil, hθ, N => by
      simp only [massOf] at hθ
      cases N with
      | zero => simp [eval]
      | succ n => rw [VoteList.app, tauPlayer, eval_tvote_cons_none n (by omega) (hJ n)]
  | .cons w I rest, _, θ, .cons (a := a) (bs := bs) hI hrest, hθ, N => by
      cases N with
      | zero => simp [eval]
      | succ n =>
          have hθ0 : θ ≠ 0 := by intro h; subst h; exact hθ (Nat.zero_le _)
          rw [VoteList.app, tauPlayer]
          rcases hE : eval n (.bot I) (.bot I) I with _ | a'
          · rw [eval_tvote_cons_none n hθ0 hE]
          · obtain ⟨NI, hNI⟩ := hI
            have haa : a' = a := by
              have h1 := eval_mono_le hE (max n NI) (Nat.le_max_left _ _)
              have h2 := eval_mono_le hNI (max n NI) (Nat.le_max_right _ _)
              exact Option.some.inj (h1.symm.trans h2)
            subst haa
            cases a' with
            | C =>
                rw [eval_tvote_cons_c n hθ0 hE]
                exact eval_tvote_prefix_none me opponent hJ rest bs (θ - w) hrest (by
                  simp only [massOf, if_pos (by decide : ((Action.C == Action.C) = true))] at hθ
                  omega) n
            | D =>
                rw [eval_tvote_cons_d n hθ0 hE]
                exact eval_tvote_prefix_none me opponent hJ rest bs θ hrest (by
                  simp only [massOf, if_neg (by decide : ¬ ((Action.D == Action.C) = true))] at hθ
                  omega) n

/-- **The prefix phase theorem**: a vector whose LAST entry diverges plays `C`
    below the prefix mass and `none` above it. -/
theorem tauPlayer_phase_prefix {v : VoteList} {bs : List (Nat × Action)} (θ : Nat)
    (hbits : VoteBits v bs) {w' : Nat} {J : Prog}
    (hJ : ∀ N, eval N (.bot J) (.bot J) J = none) (opponent : Prog) :
    (θ ≤ massOf bs →
      ∃ N, play N (tauPlayer (v.app (.cons w' J .nil)) θ) opponent = some .C)
    ∧ (¬ θ ≤ massOf bs →
      ∀ N, play N (tauPlayer (v.app (.cons w' J .nil)) θ) opponent = none) := by
  refine ⟨fun hθ => ?_, fun hθ N => ?_⟩
  · obtain ⟨N, hN⟩ := eval_tvote_prefix_C _ opponent v bs θ (.cons w' J .nil) hbits hθ
    exact ⟨N, by rw [play]; exact hN⟩
  · rw [play]; exact eval_tvote_prefix_none _ opponent hJ v bs θ hbits hθ N

/-! ## The point-mass coherence lemma

**The theorem the retracted crowd-exploiter would have failed.** At a point-mass
signal — one hypothesis carrying all the weight, with a threshold it can meet — the
tau player plays exactly what its instance plays. This is the σ-level anchor of
Def 4: `TauA(δ_B) = inst(A, δ_B)` behaviorally, which is what makes the vote a LIFT
of `A` rather than some new agent built out of `A`'s parts.

**Intentionally unconsumed**: this is a spec-level RESULT (like an outcome
theorem), whose consumer is the design review and the thesis, not another proof —
zero in-tree uses is its correct state, not dead code.

The retracted `TauEBot` (nested `tsearch`, θ inside the cascade) satisfies this at
point mass too — that was the trap. What it fails is coherence AWAY from point mass,
which is now structural rather than checkable: away from point mass, `tauPlayer` can
only ever vote once over compound decisions, because there is nowhere else to put a
threshold. -/
theorem tauPlayer_point_mass {w θ : Nat} {I : Prog} {a : Action} (me opponent : Prog)
    (hθ : θ ≠ 0) (hle : θ ≤ w) (hI : ∃ N, eval N (.bot I) (.bot I) I = some a) :
    ∃ N, eval N me opponent (tauPlayer (.cons w I .nil) θ) = some a := by
  obtain ⟨NI, hNI⟩ := hI
  cases a with
  | C =>
      refine ⟨NI + 3, ?_⟩
      rw [tauPlayer, eval_tvote_cons_c (NI + 2) hθ (eval_mono_le hNI _ (by omega))]
      -- the entry's weight covers the threshold, so the residual is 0 and the peel
      -- short-circuits to the then-branch
      have hres : θ - w = 0 := by omega
      rw [hres, eval_tvote_zero (NI + 1)]
      rfl
  | D =>
      refine ⟨NI + 3, ?_⟩
      rw [tauPlayer, eval_tvote_cons_d (NI + 2) hθ (eval_mono_le hNI _ (by omega))]
      rw [eval_tvote_nil (NI + 1) hθ]
      rfl

end PD.Tau
