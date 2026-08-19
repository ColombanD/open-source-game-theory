import PrisonersDilemma.Base.Soundness

/-!
# Tau/Vote — the uniform tau player and its peel workhorse (refined Def 4, 2026-08-18)

The **refined Def 4** (`Research/Notes/DEF4_TVOTE_ROADMAP.md`) is the uniform structural
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

/-! ## The uniform player -/

/-- **THE tau player**: vote over the decision vector `v` with caution threshold `θ`.
    Constant branches, so the play is `C` exactly when the C-mass reaches `θ`. -/
def tauPlayer (v : VoteList) (θ : Nat) : Prog :=
  .tvote v θ (.const .C) (.const .D)

/-- The C-mass of a vector under a valuation of its entries (which entry plays `C`). -/
def voteMass (val : Prog → Action) : VoteList → Nat
  | .nil           => 0
  | .cons w I rest => (if val I == Action.C then w else 0) + voteMass val rest

/-- "Every entry of the vector runs to the action `val` assigns it" — the hypothesis
    the peel workhorse consumes. One `VoteAllVals` proof per bot IS that bot's whole
    per-hypothesis content; everything above it is uniform.

    `val` is a FUNCTION on programs rather than a positional list because the peel
    recurses structurally on the vector. When two entries of a vector are the same
    term (as in τ(TFTPf), whose Dupoc and TFTPf hypotheses both resolve to the same
    instance), they necessarily get the same action — which is correct: an
    entry's play is a property of the term, and identical terms play identically. -/
inductive VoteAllVals (val : Prog → Action) : VoteList → Prop where
  | nil : VoteAllVals val .nil
  | cons {w : Nat} {I : Prog} {rest : VoteList} :
      (∃ N, eval N (.bot I) (.bot I) I = some (val I)) → VoteAllVals val rest →
      VoteAllVals val (.cons w I rest)

/-- Build a `VoteAllVals` step when the entry's action is known independently of
    `val`'s definitional shape: supply the play and the valuation equation. -/
theorem VoteAllVals.cons_of {val : Prog → Action} {w : Nat} {I : Prog}
    {rest : VoteList} {a : Action} (hval : val I = a)
    (hplay : ∃ N, eval N (.bot I) (.bot I) I = some a) (hrest : VoteAllVals val rest) :
    VoteAllVals val (.cons w I rest) :=
  .cons (hval ▸ hplay) hrest

/-! ### Mass from an explicit bit list

Rather than defining a global valuation function (which forces the elaborator to decide
term equality between large cascade terms), a bot supplies its entries' actions
POSITIONALLY. `massOf` computes the C-mass of such a list, and `VoteBits` ties it to
the vector. This is the practical interface the per-bot phase theorems use. -/

/-- The C-mass of a vector whose entries' actions are given positionally. -/
def massOf : List (Nat × Action) → Nat
  | [] => 0
  | (w, a) :: rest => (if a == Action.C then w else 0) + massOf rest

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
      simp only [massOf]
      cases θ with
      | zero =>
          refine ⟨2, ?_⟩
          rw [if_pos (Nat.le_refl 0), tauPlayer, eval_tvote_zero 1]; rfl
      | succ m =>
          refine ⟨2, ?_⟩
          rw [if_neg (by simp), tauPlayer, eval_tvote_nil 1 (by omega)]; rfl
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

/-! ## The peel workhorse -/

/-- Unfolding helper: a cooperating head entry contributes its weight. -/
theorem voteMass_cons_C {val : Prog → Action} {w : Nat} {I : Prog} {rest : VoteList}
    (h : val I = Action.C) :
    voteMass val (.cons w I rest) = w + voteMass val rest := by
  simp only [voteMass, h]
  rw [if_pos (by decide : ((Action.C == Action.C) = true))]

/-- Unfolding helper: a defecting head entry contributes nothing. -/
theorem voteMass_cons_D {val : Prog → Action} {w : Nat} {I : Prog} {rest : VoteList}
    (h : val I = Action.D) :
    voteMass val (.cons w I rest) = voteMass val rest := by
  simp [voteMass, h, if_neg (by decide : ¬ ((Action.D == Action.C) = true))]

/-- **The peel workhorse** (twin of the retired `eval_tsearch_of_bits`, with entries
    EVALUATED instead of probed). If every entry runs to its valuation, the vote plays
    `C` exactly when the C-mass reaches `θ`.

    Entries are closed and frozen, so they run in their own frame `eval N I I I` and
    the enclosing `me`/`opponent` never touch them — which is why a tau player's play
    depends on its signal alone. -/
theorem eval_tvote_of_vals (me opponent : Prog) (val : Prog → Action) :
    ∀ (v : VoteList) (θ : Nat), VoteAllVals val v →
      ∃ N, eval N me opponent (tauPlayer v θ)
        = some (if θ ≤ voteMass val v then Action.C else Action.D)
  | .nil, θ, _ => by
      simp only [voteMass]
      cases θ with
      | zero =>
          refine ⟨2, ?_⟩
          rw [if_pos (Nat.le_refl 0), tauPlayer, eval_tvote_zero 1]
          rfl
      | succ m =>
          refine ⟨2, ?_⟩
          rw [if_neg (by simp), tauPlayer, eval_tvote_nil 1 (by omega)]
          rfl
  | .cons w I rest, θ, hvals => by
      obtain ⟨hI, hrest⟩ : (∃ N, eval N (.bot I) (.bot I) I = some (val I)) ∧ VoteAllVals val rest := by
        cases hvals with
        | cons h hr => exact ⟨h, hr⟩
      cases θ with
      | zero =>
          refine ⟨2, ?_⟩
          rw [if_pos (Nat.zero_le _), tauPlayer, eval_tvote_zero 1]
          rfl
      | succ m =>
          obtain ⟨NI, hNI⟩ := hI
          cases hv : val I with
          | C =>
              obtain ⟨Nb, hNb⟩ :=
                eval_tvote_of_vals me opponent val rest (m + 1 - w) hrest
              refine ⟨max NI Nb + 1, ?_⟩
              rw [hv] at hNI
              rw [tauPlayer, eval_tvote_cons_c (max NI Nb) (by omega)
                    (eval_mono_le hNI _ (Nat.le_max_left _ _))]
              have hiff : (m + 1 - w ≤ voteMass val rest)
                  ↔ (m + 1 ≤ voteMass val (.cons w I rest)) := by
                rw [voteMass_cons_C (val := val) (w := w) (I := I) (rest := rest) hv]
                omega
              rw [← if_congr hiff rfl rfl]
              exact eval_mono_le hNb _ (Nat.le_max_right _ _)
          | D =>
              obtain ⟨Nb, hNb⟩ :=
                eval_tvote_of_vals me opponent val rest (m + 1) hrest
              refine ⟨max NI Nb + 1, ?_⟩
              rw [hv] at hNI
              rw [tauPlayer, eval_tvote_cons_d (max NI Nb) (by omega)
                    (eval_mono_le hNI _ (Nat.le_max_left _ _))]
              have hiff : (m + 1 ≤ voteMass val rest)
                  ↔ (m + 1 ≤ voteMass val (.cons w I rest)) := by
                rw [voteMass_cons_D (val := val) (w := w) (I := I) (rest := rest) hv]
              rw [← if_congr hiff rfl rfl]
              exact eval_mono_le hNb _ (Nat.le_max_right _ _)
termination_by structural v _ _ => v

/-! ## The point-mass coherence lemma

**The theorem the retracted crowd-exploiter would have failed.** At a point-mass
signal — one hypothesis carrying all the weight, with a threshold it can meet — the
tau player plays exactly what its instance plays. This is the σ-level anchor of
Def 4: `TauA(δ_B) = inst(A, δ_B)` behaviorally, which is what makes the vote a LIFT
of `A` rather than some new agent built out of `A`'s parts.

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

/-! ## The generic phase theorem

Proven ONCE over the vote, for every vector — lifted or signal-native. Per-bot work
reduces to supplying a `VoteAllVals` (what each entry plays) and computing its
`voteMass`; the α-boundary then falls out of arithmetic. This replaces the four
per-bot phase theorems of the retracted layer. -/

/-- **The α-phase theorem, uniform.** A tau player cooperates exactly when its
    cooperation mass reaches the caution threshold — against EVERY opponent, since
    entries are closed and `.opp`-free. -/
theorem tauPlayer_phase {val : Prog → Action} {v : VoteList} (θ : Nat)
    (hvals : VoteAllVals val v) (opponent : Prog) :
    (θ ≤ voteMass val v → ∃ N, play N (tauPlayer v θ) opponent = some .C)
    ∧ (¬ θ ≤ voteMass val v → ∃ N, play N (tauPlayer v θ) opponent = some .D) := by
  constructor
  · intro hθ
    obtain ⟨N, hN⟩ := eval_tvote_of_vals (tauPlayer v θ) opponent val v θ hvals
    exact ⟨N, by rw [play]; rw [hN, if_pos hθ]⟩
  · intro hθ
    obtain ⟨N, hN⟩ := eval_tvote_of_vals (tauPlayer v θ) opponent val v θ hvals
    exact ⟨N, by rw [play]; rw [hN, if_neg hθ]⟩

/-- Package two existential plays into an existential outcome (fuel aligned by
    monotonicity). Carried over verbatim from the retired `PeelLemmas`. -/
theorem outcome_of_ex_plays {A B : Prog} {a b : Action}
    (hA : ∃ N, play N A B = some a) (hB : ∃ N, play N B A = some b) :
    ∃ N, outcome N A B = some (a, b) := by
  obtain ⟨N₁, h₁⟩ := hA
  obtain ⟨N₂, h₂⟩ := hB
  refine ⟨max N₁ N₂, ?_⟩
  have h₁' : play (max N₁ N₂) A B = some a := eval_mono_le h₁ _ (Nat.le_max_left _ _)
  have h₂' : play (max N₁ N₂) B A = some b := eval_mono_le h₂ _ (Nat.le_max_right _ _)
  simp [outcome, h₁', h₂']

/-! ## The probe ↔ entry bridge

A `.tvote` entry runs `.bot`-framed, which is LITERALLY the probe atom's frame. So
every bit lemma the tau layer already proves about `probe I` is a fact about the
entry `I`, one `.bot` unfolding apart. This is what lets the whole `Certs` layer be
reused verbatim under the refined definition. -/

/-- A true probe atom gives a cooperating entry. -/
theorem entry_C_of_interp {I : Prog} (h : (probe I).interp) :
    ∃ N, eval N (.bot I) (.bot I) I = some Action.C := by
  simp only [probe, Formula.interp] at h
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [play, eval] at hn
  | succ m => exact ⟨m, by rw [play, eval] at hn; exact hn⟩

/-- A false probe atom on a TERMINATING entry gives a defecting entry. (Termination is
    a real side-condition: `¬interp` alone also holds of an entry that never plays.) -/
theorem entry_D_of_not_interp {I : Prog}
    (hterm : ∃ N a, eval N (.bot I) (.bot I) I = some a) (h : ¬ (probe I).interp) :
    ∃ N, eval N (.bot I) (.bot I) I = some Action.D := by
  obtain ⟨N, a, hNa⟩ := hterm
  cases a with
  | C => exact absurd ⟨N+1, by rw [play, eval]; exact hNa⟩ h
  | D => exact ⟨N, hNa⟩

/-- A `Pf` of the probe gives a cooperating entry (via soundness). -/
theorem entry_C_of_pf {I : Prog} {K : Nat} (h : Pf K (probe I)) :
    ∃ N, eval N (.bot I) (.bot I) I = some Action.C :=
  entry_C_of_interp (Pf_sound _ _ h)

/-! ## Shape play-lemmas

What each COMPILE IDIOM plays, given its probe bits. Stated over the explicit `Prog`
shapes the Spec compiler emits (a prove-stage, the two-stage cascade, a run-stage) —
no zoo vocabulary, so they apply to any zoo's compiled entries by defeq. Probes are
closed (`probe_subst`), so a shape's play never depends on the frame it is consulted
from — the term-level reason a tau player's action depends on its signal alone. -/

/-- A single prove-stage (`.search` on a probe, constant branches) cooperates exactly
    when its probe fires… -/
theorem searchProbe_plays_C {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probe I) = true) :
    ∃ N, eval N me opp (.search k (probe I) (.const .C) (.const .D)) = some Action.C := by
  refine ⟨2, ?_⟩
  rw [eval, probe_subst, h]
  rfl

/-- …and defects when it does not. -/
theorem searchProbe_plays_D {k : Nat} {I : Prog} (me opp : Prog)
    (h : proofSearch k (probe I) = false) :
    ∃ N, eval N me opp (.search k (probe I) (.const .C) (.const .D)) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, probe_subst, h, if_neg (by simp)]
  rfl

/-- The two-stage exploiter cascade DEFECTS when its exploit-probe fires… -/
theorem cascade_plays_D_of_exploit {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = true) :
    ∃ N, eval N me opp (.search k (probe I_D) (.const .D)
      (.search k (probe I_C) (.const .C) (.const .D))) = some Action.D := by
  refine ⟨2, ?_⟩
  rw [eval, probe_subst, h1]
  rfl

/-- …COOPERATES when the exploit fails but reciprocity fires… -/
theorem cascade_plays_C {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = false)
    (h2 : proofSearch k (probe I_C) = true) :
    ∃ N, eval N me opp (.search k (probe I_D) (.const .D)
      (.search k (probe I_C) (.const .C) (.const .D))) = some Action.C := by
  refine ⟨3, ?_⟩
  rw [eval, probe_subst, h1, if_neg (by simp), eval, probe_subst, h2]
  rfl

/-- …and DEFECTS when neither fires. -/
theorem cascade_plays_D_of_both_false {k : Nat} {I_D I_C : Prog} (me opp : Prog)
    (h1 : proofSearch k (probe I_D) = false)
    (h2 : proofSearch k (probe I_C) = false) :
    ∃ N, eval N me opp (.search k (probe I_D) (.const .D)
      (.search k (probe I_C) (.const .C) (.const .D))) = some Action.D := by
  refine ⟨3, ?_⟩
  rw [eval, probe_subst, h1, if_neg (by simp), eval, probe_subst, h2,
      if_neg (by simp)]
  rfl

/-- A run-stage (`.ite` over a frozen self-sim) COPIES what its probed instance
    plays — the behavioral read: true plays, floor-blind. -/
theorem simCopy_plays {I : Prog} {a : Action} (me opp : Prog)
    (h : ∃ N, eval N (.bot I) (.bot I) I = some a) :
    ∃ N, eval N me opp (.ite (.sim (.bot I) (.bot I)) Action.C (.const .C) (.const .D))
      = some a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 3, ?_⟩
  rw [eval]
  have hg : eval (N + 2) me opp (.sim (.bot I) (.bot I)) = some a := by
    rw [eval]
    simp only [Prog.subst]
    rw [eval]
    exact eval_mono_le hN _ (by omega)
  rw [hg]
  cases a with
  | C => simp only [bind, Option.bind]; rw [if_pos (by decide)]; rfl
  | D => simp only [bind, Option.bind]; rw [if_neg (by decide)]; rfl

end PD.Tau
