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
when a SECOND zoo instantiates the DSL (for `zoo6`, D1 IS the certificate).
-/

open PD

namespace PD.Tau

/-! ## The types (§6.1) -/

/-- How a stage consults its probe: `prove` = bounded proof search over the probe
    atom (a `.search` node); `run` = execute the probed instance and read its true
    play (a `.sim`-guarded `.ite`). -/
inductive Mode | prove | run
deriving DecidableEq, Repr

/-- The counterfactual opponent a stage imagines the hypothesis facing: `self` = "me,
    the probing bot" (the self-probe geometry — Dupoc's), or a named zoo member. -/
inductive Target (ι : Type) | self | name (i : ι)
deriving DecidableEq, Repr

/-- One probe stage: consult the hypothesis's instance-vs-`target` in the given mode;
    if it cooperates, commit `fire`; else fall through to the next stage. -/
structure Stage (ι : Type) where
  mode   : Mode
  target : Target ι
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

    Fuel exhaustion emits `.const d` — for a well-formed zoo at adequate fuel it is
    unreachable, and Gate D1 certifies that for `zoo6` (an exhausted compile cannot
    be byte-identical to the hand-written closure). -/
def instGo (Z : Zoo ι) [DecidableEq ι] : Nat → ι → ι → List (Stage ι) → Action → Prog
  | 0, _, _, _, d => .const d
  | _+1, _, _, [], d => .const d
  | fuel+1, A, T, st :: rest, d =>
      let cont := instGo Z fuel A T rest d
      match st.mode, st.target with
      | .prove, .name B =>
          .search Z.budget (probe (instGo Z fuel T B (Z.spec T).stages (Z.spec T).dflt))
            (.const st.fire) cont
      | .prove, .self =>
          if T = A then
            .search Z.budget (.plays .self .self Action.C) (.const st.fire) cont
          else
            .search Z.budget (probe (instGo Z fuel T A (Z.spec T).stages (Z.spec T).dflt))
              (.const st.fire) cont
      | .run, .name B =>
          let P := instGo Z fuel T B (Z.spec T).stages (Z.spec T).dflt
          .ite (.sim (.bot P) (.bot P)) Action.C (.const st.fire) cont
      | .run, .self =>
          if T = A then
            .ite (.sim .self .self) Action.C (.const st.fire) cont
          else
            let P := instGo Z fuel T A (Z.spec T).stages (Z.spec T).dflt
            .ite (.sim (.bot P) (.bot P)) Action.C (.const st.fire) cont

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
    vector's `VoteBits` follows. With `tauPlayer_phase_bits` this is the entire
    uniform path from a bit table `b : ι → Action` to a phase theorem. -/
theorem vecOf_bits (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) (b : ι → Action) :
    ∀ order : List ι,
      (∀ T ∈ order, ∃ N, eval N (.bot (inst Z A T)) (.bot (inst Z A T)) (inst Z A T)
                      = some (b T)) →
      VoteBits (vecOf Z A w order) (order.map fun T => (w T, b T))
  | [], _ => .nil
  | T :: rest, h =>
      .cons (h T (List.mem_cons_self ..))
        (vecOf_bits Z A w b rest fun t ht => h t (List.mem_cons_of_mem _ ht))

end PD.Tau
