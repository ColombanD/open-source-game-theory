import PrisonersDilemma.Tau.Vote

/-!
# Tau/Spec — the bot-spec DSL and its compiler (Phase 5, `DEF4_TVOTE_ROADMAP.md` §6)

**Machinery only** (since the 2026-08-18 per-bot-file reorganization): the spec
TYPES, the compiler, and the vector builder — all generic in the zoo index `ι`.
The concrete zoo lives in the base-bot-style layout: `Tau/Roster.lean` declares the
cast, `Tau/Bots/<TauBot>.lean` holds each bot's spec row and doc (one file per bot,
like `Bots/` for the base zoo), and `Tau/Zoo.lean` assembles them and carries
Gate D1.

The scale layer of the refined Def 4. A base bot is described by a small SPEC — an
ordered list of probe stages plus a default action — and the compiler `inst` turns a
spec zoo into the whole δ-instance closure: `inst Z A T` is bot A's ENTIRE decision
procedure at point mass on hypothesis T. Vectors are then built by mapping the
compiler over a zoo list (`vecOf`), so nothing per-bot is hand-written except the
spec itself and the per-column bit lemmas (`Tau/Certs`) — the mathematics a DSL
cannot generate.

**Implementation note — FUEL, not the WF measure (deviation from §6.3, recorded).**
The roadmap preferred a well-founded `inst` whose `decreasing_by` encodes the
≤1-self-prober condition. Tested and rejected here: WF-compiled definitions do NOT
reduce by `rfl` even at concrete inputs (checked on a toy — `rfl` fails with a
metavariable mismatch), and Gate D1 is BY `rfl`; the 36 byte-identity checks would
all have to go through `simp`-unfolding with a free budget `k`, reviving exactly the
normalization fights Phase 4 recorded. The fuel version is structurally recursive,
fully `rfl`-reducing, and Gate D1 below certifies the compiler output byte-for-byte
— which also catches fuel exhaustion (an exhausted compile emits a default constant
that cannot match the hand-written closure). The wall-detection story moves to the
recorded debt: a generic `Zoo.WellFormed` predicate + fuel-sufficiency lemma, due
when a SECOND zoo instantiates the DSL (for `tauZoo`, D1 IS the certificate).
-/

open PD

namespace PD.Tau

/-! ## The types (§6.1) -/

/-- How a stage consults its probe: `prove` = bounded proof search over the probe
    atom (a `.search` node); `run` = execute the probed instance and read its true
    play (a `.sim`-guarded `.ite`); `proveImpl` = bounded proof search over the
    IMPLICATION atom `probeImpl` — "if I play `test` against them, they play `test`
    against me" (CIMCIC/DIMCID's guard shape, added 2026-08-20).

    `proveImpl` is a genuinely different MODALITY, not sugar for `prove`: the
    implication is provable whenever its CONSEQUENT is (`Pf.weakenImpl`), so a
    `proveImpl` stage fires in strictly more cases than the corresponding `prove`
    stage on the consequent alone would — it is the conditional-commitment reading
    ("I cooperate if that would induce cooperation") rather than the
    evidence-gathering one.

    `proveEq` = bounded proof search over a STRUCTURAL IDENTITY atom
    (`.eq`): "is the probed instance literally this term?" — CupodTrollBot's guard
    shape (2026-08-20). Both directions are decidable in `S` (`Pf.eqRefl` /
    `Pf.eqNeg`), so a `proveEq` bit is never floor-priced: identity is the one
    question the proof system answers completely. -/
inductive Mode | prove | run | proveImpl | proveEq
deriving DecidableEq, Repr

/-- The counterfactual opponent a stage imagines the hypothesis facing: `self` = "me,
    the probing bot" (the self-probe geometry — Dupoc's), or a named zoo member. -/
inductive Target (ι : Type) | self | name (i : ι)
deriving DecidableEq, Repr

/-- One probe stage: consult the hypothesis's instance-vs-`target` in the given mode;
    if the consultation yields `test`, commit `fire`; else fall through to the next
    stage. `test` was added 2026-08-18 when the first lifted bots needed it (OBot
    watches for DEFECTION, GuardianBot proves it); the original zoo's stages all
    test `.C`. -/
structure Stage (ι : Type) where
  mode   : Mode
  target : Target ι
  test   : Action
  fire   : Action
deriving DecidableEq, Repr

/-- A bot spec: its probe cascade plus the default action when every stage falls
    through. Constants are `⟨[], a⟩`. -/
structure Spec (ι : Type) where
  stages : List (Stage ι)
  dflt   : Action
deriving DecidableEq, Repr

/-- A spec zoo: one spec per index, and the shared prover budget every `prove` stage
    searches under. -/
structure Zoo (ι : Type) where
  spec   : ι → Spec ι
  budget : Nat

/-! ## The compiler (§6.2) -/

/-- Fuel-indexed compiler core. `instGo Z fuel A T l d` compiles the remaining stages
    `l` of bot A's cascade at hypothesis T (with default `d`); every recursive call —
    the cascade continuation AND the probed instances — decrements fuel, so the
    recursion is STRUCTURAL and the output reduces by `rfl` (the property Gate D1
    lives on).

    Probed-object resolution (the one place recursion happens):
    * stage target `name B` → `inst Z T B` — the hypothesis's instance seeing B;
    * stage target `self`, `T ≠ A` → `inst Z T A` — the hypothesis's instance seeing ME;
    * stage target `self`, `T = A` → the QUINE: emit the pronoun guard
      (`.plays .self .self .C` / `.sim .self .self`) instead of recursing — a term
      cannot contain itself, and the pronoun is the language's own knot for the
      diagonal (pinned literal by `Zoo.lean`'s `inst_dupoc_quine`).

    **`proveImpl` uses the SELF PRONOUN for the antecedent's subject** (2026-08-20):
    the antecedent is "*I* play `test` against the probed instance", and "I" is the
    term currently being compiled — which cannot contain itself. `.self` is the
    language's knot for exactly that, closed by `subst` at consultation time to the
    running instance (the `.plays .self …` convention base CIMCIC already uses). The
    guard is therefore NOT closed under `subst` — unlike `probe`/`probeD` — so
    `probeImpl` is the atom the guard becomes AFTER substitution, and the
    `probeImpl_subst` lemma is about that closed form, not about this one.

    Fuel exhaustion emits `.const d` — for a well-formed zoo at adequate fuel it is
    unreachable, and Gate D1 certifies that for `tauZoo` (an exhausted compile cannot
    be byte-identical to the hand-written closure). -/
def instGo (Z : Zoo ι) [DecidableEq ι] : Nat → ι → ι → List (Stage ι) → Action → Prog
  | 0, _, _, _, d => .const d
  | _+1, _, _, [], d => .const d
  | fuel+1, A, T, st :: rest, d =>
      let cont := instGo Z fuel A T rest d
      match st.mode, st.target with
      | .prove, .name B =>
          let P := instGo Z fuel T B (Z.spec T).stages (Z.spec T).dflt
          .search Z.budget (.plays (.bot P) (.bot P) st.test) (.const st.fire) cont
      | .prove, .self =>
          if T = A then
            .search Z.budget (.plays .self .self st.test) (.const st.fire) cont
          else
            let P := instGo Z fuel T A (Z.spec T).stages (Z.spec T).dflt
            .search Z.budget (.plays (.bot P) (.bot P) st.test) (.const st.fire) cont
      | .run, .name B =>
          let P := instGo Z fuel T B (Z.spec T).stages (Z.spec T).dflt
          .ite (.sim (.bot P) (.bot P)) st.test (.const st.fire) cont
      | .run, .self =>
          if T = A then
            .ite (.sim .self .self) st.test (.const st.fire) cont
          else
            let P := instGo Z fuel T A (Z.spec T).stages (Z.spec T).dflt
            .ite (.sim (.bot P) (.bot P)) st.test (.const st.fire) cont
      | .proveImpl, .name B =>
          let P := instGo Z fuel T B (Z.spec T).stages (Z.spec T).dflt
          .search Z.budget
            (.impl (.plays .self (.bot P) st.test) (.plays (.bot P) .self st.test))
            (.const st.fire) cont
      | .proveEq, .name B =>
          let P := instGo Z fuel T B (Z.spec T).stages (Z.spec T).dflt
          .search Z.budget (.eq .opp (.bot P)) (.const st.fire) cont
      | .proveEq, .self =>
          if T = A then
            .search Z.budget (.eq .opp .self) (.const st.fire) cont
          else
            let P := instGo Z fuel T A (Z.spec T).stages (Z.spec T).dflt
            .search Z.budget (.eq .opp (.bot P)) (.const st.fire) cont
      | .proveImpl, .self =>
          if T = A then
            .search Z.budget
              (.impl (.plays .self .self st.test) (.plays .self .self st.test))
              (.const st.fire) cont
          else
            let P := instGo Z fuel T A (Z.spec T).stages (Z.spec T).dflt
            .search Z.budget
              (.impl (.plays .self (.bot P) st.test) (.plays (.bot P) .self st.test))
              (.const st.fire) cont

/-- Default compile fuel: generous for any zoo whose probe-nesting depth is modest
    (the 6-template zoo needs < 12; adding bots that only name existing columns does
    not deepen the nesting). Gate-D1-style byte checks are what certify sufficiency
    per zoo. -/
def instFuel : Nat := 16

/-- **THE COMPILER**: `inst Z A T` = bot A's entire lifted decision procedure at
    point mass on hypothesis T. -/
def inst (Z : Zoo ι) [DecidableEq ι] (A T : ι) : Prog :=
  instGo Z instFuel A T (Z.spec A).stages (Z.spec A).dflt

/-! ## Vectors from the compiler (§6.4) -/

/-- The decision vector of bot A over a zoo enumeration, with weights `w : ι → Nat`
    (the N-ary replacement of the fixed-arity `wC wD wTs wTp wL wE` signatures). -/
def vecOf (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) : List ι → VoteList
  | [] => .nil
  | T :: rest => .cons (w T) (inst Z A T) (vecOf Z A w rest)

/-- **The generic bits lemma** — ONE list induction replacing every per-bot
    `.cons`-chain: supply, per hypothesis, what A's instance plays, and the whole
    vector's `VoteBits` follows. Consumed by `phase_of_bits` below (and by the
    scanner-facing per-bot `*Bits` corollaries, whose literal rows it produces by
    defeq on the concrete enumeration). -/
theorem vecOf_bits (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) (b : ι → Action) :
    ∀ order : List ι,
      (∀ T ∈ order, ∃ N, eval N (.bot (inst Z A T)) (.bot (inst Z A T)) (inst Z A T)
                      = some (b T)) →
      VoteBits (vecOf Z A w order) (order.map fun T => (w T, b T))
  | [], _ => .nil
  | T :: rest, h =>
      .cons (h T (List.mem_cons_self ..))
        (vecOf_bits Z A w b rest fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- **THE generic phase theorem** — the entire uniform path from a bit table
    `b : ι → Action` to a phase theorem, zoo-size independent: supply what A's
    instance plays at each hypothesis, and A's tau player thresholds the table's
    C-mass. Every per-bot phase theorem is this plus (a) the bot's witness lemma
    (column facts, the mathematics a DSL cannot generate) and (b) a `simp`
    reduction of `bitMass` to the bot's display mass. -/
theorem phase_of_bits (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) (b : ι → Action)
    (order : List ι) (θ : Nat) (opponent : Prog)
    (h : ∀ T ∈ order, ∃ N, eval N (.bot (inst Z A T)) (.bot (inst Z A T)) (inst Z A T)
          = some (b T)) :
    (θ ≤ bitMass w b order →
      ∃ N, play N (tauPlayer (vecOf Z A w order) θ) opponent = some .C)
    ∧ (¬ θ ≤ bitMass w b order →
      ∃ N, play N (tauPlayer (vecOf Z A w order) θ) opponent = some .D) :=
  tauPlayer_phase_bits θ (vecOf_bits Z A w b order h) opponent

end PD.Tau
