/-!
# Spike — does "proofs as DATA" REALLY discharge `boxInternalize`? (faithful, anti-cheat)

User's well-founded suspicion: "proofs as data" was tried before (the `search_f`/`Provable_fin`
cycle-break, Wall 2) — it cleared POSITIVITY and then died on SOUNDNESS at the fixpoint. This spike
tests whether the `boxInternalize` substrate hits the SAME wall, with the cheats from the two prior
attempts (`ExplicitSBoxInternalizeSpike`, `FaithfulBudgetAxKSpike`) DELIBERATELY DISALLOWED.

ANTI-CHEAT RULES (the two cheats I made before):
  CHEAT 1 (ExplicitS): trivial atom layer — every atom provable at every budget. DISALLOWED: atoms
    here are NOT freely provable; budgeted provability of the cooperation atoms comes ONLY from an
    INVERSION hypothesis (modelling `ps_k_of_play_dupoc`), exactly as in the real engine.
  CHEAT 2 (FaithfulBudget): budgeted `interp` — `interpAt (.box k φ) := interpAt kIn φ` with atoms
    budget-gated, making axK sound by definition. DISALLOWED: `interp` here is the REAL shape —
    `.plays` UNbudgeted (play exists at SOME fuel), `.box k` budgeted (provable at k).

FAITHFUL MODEL.
  • `Play a` : Prop — "atom a's play happens" (UNbudgeted; models `∃n, play n = a`).
  • `Pf k φ` : the proof-term DATA. Cooperation atoms are provable-at-k ONLY via `invert` carrying the
    inversion fact. `interp` is real-shaped. We ask: can `boxInternalize`'s conclusion be BUILT
    positively + proven sound, WITHOUT a budgeted-interp shortcut and WITHOUT a free atom leaf?

NOT root-imported.
-/

namespace PD.FaithfulSubstrateSpike

abbrev Atom := Nat
inductive TFormula where
  | plays : Atom → TFormula
  | impl  : TFormula → TFormula → TFormula
  | box   : Nat → TFormula → TFormula
deriving DecidableEq
open TFormula

/-- UNbudgeted play existence (models `∃ n, play n p q = some a`). This is what a `.plays` atom's
    `interp` is in the REAL engine — NOT budget-gated. -/
opaque Play : Atom → Prop

/-- The two cooperation atoms (φD = 0, φP = 1) and the INVERSION between them, as the engine has it:
    a play of φD yields budgeted provability of φP at the SAME k (the guard inversion
    `ps_k_of_play_dupoc`). This is the ONLY route to budgeted provability of φP — NO free leaf. -/
def aD : Atom := 0
def aP : Atom := 1

/-- The COMPANION engine fact: at the fixpoint, φD playing entails φP playing (both cooperate). In the
    real engine this is the `dupoc_D_vs_prudent`-style consequence: φD plays C ⟹ proofSearch k φP =
    true ⟹ guards fire ⟹ φP plays C. It is what `Provable_sound` extracts from the inversion's
    conclusion. NOT a cheat — a real theorem; modelled here as a hypothesis to keep the spike honest. -/
axiom play_aD_to_aP : Play aD → Play aP

/-- Proof-term DATA. KEY: NO free atom leaf for the cooperation atoms. The only `.plays`-introduction
    is `invert`, which models the real inversion: from `Play aD` (the play happening) get a proof of
    `.plays aP` AT budget k. So budgeted provability is gated on the play, faithfully. -/
inductive Pf : Nat → TFormula → Type where
  | invert (k : Nat) : Play aD → Pf k (.plays aP)                          -- the guard inversion ONLY
  | boxIntro (kIn K : Nat) (φ : TFormula) : Pf kIn φ → Pf K (.box kIn φ)
  | axK (k : Nat) (φ α : TFormula) : Pf k (.box k (.impl φ α)) → Pf k (.impl (.box k φ) (.box k α))
  -- FIX ATTEMPT for stuck point 1: add modus ponens / application at the Pf level so axK's soundness
  -- arm can RUN the implication proof. Is THIS positive? Both premises are positive Pf VALUES (no
  -- transformer), so it should be kernel-legal — test it.
  | app (k : Nat) (φ α : TFormula) : Pf k (.impl φ α) → Pf k φ → Pf k α

/-- REAL-shaped interp (anti-CHEAT-2): `.plays` UNbudgeted, `.box k` = `∃ data, Pf k φ` (budgeted
    provability — the real `interp .box := Provable k`). -/
def interpF : TFormula → Prop
  | .plays a   => Play a
  | .impl φ α  => interpF φ → interpF α
  | .box k φ   => Nonempty (Pf k φ)

/-- **The faithful soundness test.** Every proof-term denotes its REAL-shaped interp. The `axK` arm
    is the crux: from `interpF (□(φ→α))` = `Nonempty (Pf k (φ→α))`, derive `interpF (□φ → □α)` =
    `Nonempty (Pf k φ) → Nonempty (Pf k α)`. Watch whether this needs the budgeted shortcut. -/
theorem pf_sound : {k : Nat} → {φ : TFormula} → Pf k φ → interpF φ := by
  intro k φ d
  induction d with
  | invert k hplay =>
      -- goal interpF (.plays aP) = Play aP. hplay : Play aD. The companion engine fact closes it:
      exact play_aD_to_aP hplay
  | boxIntro kIn K φ d ih =>
      -- goal interpF (.box kIn φ) = Nonempty (Pf kIn φ). We HAVE d : Pf kIn φ. ⟨d⟩.
      exact ⟨d⟩
  | axK k φ α d ih =>
      -- goal interpF (□φ→□α) = (Nonempty (Pf k φ) → Nonempty (Pf k α)).
      -- ih : interpF (□(φ→α)) = Nonempty (Pf k (φ→α)). WITH `app` we CAN now build Pf k α:
      intro hφ
      obtain ⟨pimpl⟩ := ih           -- pimpl : Pf k (.impl φ α)
      obtain ⟨pφ⟩ := hφ              -- pφ    : Pf k φ
      exact ⟨.app k φ α pimpl pφ⟩    -- application of the proof-data. POSITIVE, SOUND-shaped.
  | app k φ α dimp dφ ihimp ihφ =>
      -- goal interpF α. ihimp : interpF (.impl φ α) = (interpF φ → interpF α); ihφ : interpF φ.
      exact ihimp ihφ

/-- **`boxInternalize` as a THEOREM in the faithful model** (`axK ∘ boxIntro`), no `sorry`. -/
def boxInternalize_faithful (k : Nat) (φ α : TFormula) (himpl : Pf k (.impl φ α)) :
    Pf k (.impl (.box k φ) (.box k α)) :=
  .axK k φ α (.boxIntro k k (.impl φ α) himpl)

/-! ## ANTI-CHEAT SOUNDNESS PROBE — does `app` open a backdoor to a FALSE atom?

The whole "it works" claim is a LIE if `app`/`axK` let us derive a proof of a genuinely false atom.
`aFalse := 2` has NO `invert` (only `aP` does) and we will assert NO `Play aFalse`. If `Pf k
(.plays aFalse)` is derivable, the system is unsound. Test: it must be EMPTY. -/

def aFalse : Atom := 2

/-- `pf_sound` already gives the discipline: a `Pf k (.plays aFalse)` would force `interpF (.plays
    aFalse) = Play aFalse`. If `Play aFalse` is not derivable (we never give it), then no such `Pf`
    can be SOUND — but could one EXIST unsoundly? `pf_sound` says NO: every `Pf` is sound, so a
    `Pf k (.plays aFalse)` yields `Play aFalse`. Thus underivability of `Play aFalse` ⟹ no proof. -/
theorem aFalse_no_play_no_proof (k : Nat) (hno : ¬ Play aFalse) : Pf k (.plays aFalse) → False :=
  fun d => hno (pf_sound d)

/-! ## VERDICT — does proofs-as-DATA discharge `boxInternalize` faithfully? **YES, but with `app`.**

With the TWO prior cheats DISALLOWED (trivial atoms; budgeted interp), the faithful model:
  • `interpF` is REAL-shaped (`.plays` unbudgeted `Play`, `.box k` = `Nonempty (Pf k ·)`);
  • cooperation atoms are provable ONLY via `invert` (the guard inversion), gated on the play;
  • `boxInternalize_faithful = axK ∘ boxIntro` is a THEOREM, `pf_sound` certifies the whole `Pf`
    SOUND (incl. `axK` and `app`), and `aFalse_no_play_no_proof` shows a false atom stays
    underivable (no backdoor). NO `sorry`. `#print axioms` below: only `play_aD_to_aP` (the modelled
    real engine companion fact) + Lean-standard.

**WHAT MADE IT WORK (the honest crux, vs. the prior cheats and the user's past failure):** the data
type needed a MODUS-PONENS / `app` constructor so `axK`'s soundness arm could RUN the implication
proof. `app` is POSITIVE (both premises are `Pf` VALUES, no transformer — kernel-accepted) and SOUND
(`pf_sound`'s `app` arm is plain function application of the interps). This is the piece the abstract
`Prop` engine LACKS at the object level and the prior toys hid: the proof-DATA must be APPLICABLE.

**Caveat carried (NOT dissolved):** the two `invert`/companion facts (`play_aD_to_aP`) are the
PER-LEG guard inversions — the Horn-B / Wall-1 residue. The substrate makes the box-internalization a
sound theorem GIVEN those per-leg facts (which the real engine already proves), but does NOT
manufacture them. So: proofs-as-data + an `app` rule WORKS for `boxInternalize` soundly — the past
failure (`search_f`/`Provable_fin`) was a DIFFERENT predicate (the Π₁ negative false-guard cert, Wall
2), which is genuinely empty and has no `app`-style fix. The two are NOT the same wall. -/

#print axioms boxInternalize_faithful
#print axioms pf_sound
#print axioms aFalse_no_play_no_proof

end PD.FaithfulSubstrateSpike
