import PrisonersDilemma.Tau.Vote

/-!
# Tau/Spec — the bot-spec DSL and its compiler (`Research/Notes/TAUBOTS.md`)

**Machinery only** (since the 2026-08-18 per-bot-file reorganization): the spec
TYPES, the compiler, and the vector builder — all generic in the zoo index `ι`.
The concrete zoo lives in the base-bot-style layout: `Tau/Roster.lean` declares the
cast, `Tau/Bots/<TauBot>.lean` holds each bot's spec row and doc (one file per bot,
like `Bots/` for the base zoo), and `Tau/Zoo.lean` assembles them and carries
Gate D1.

The scale layer of the refined Def 4. A base bot is described by a SPEC — its own
source tree with a `Target` hole wherever the base says "`.opp` facing Q" — and the
compiler `inst` turns a spec zoo into the whole δ-instance closure: `inst Z A T` is bot A's ENTIRE decision
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

/-! ## The types (§6.1) — a TREE, since 2026-08-24

**Why a tree and not a stage list.** Def 4 is the UNIFORM SOURCE LIFT: τ(A) is A's
own source with "the opponent facing `Q`" replaced by "the hypothesis's instance
facing `Q`". So the spec language should be `Prog` with a HOLE where the base
source says `.opp` — and that is what `Spec` now is: `Prog` minus the pronouns the
compiler supplies (`.self`/`.opp`/`.bot`), plus `Target` in the hole.

The previous DSL was a LIST of probe stages plus a default action — a decision-list
compression of the same trees. It covered every classifier in the zoo (each stage
= "consult, compare to `test`, commit a constant `fire`, else fall through"), but it
could not say MirrorBot, whose whole program is a bare `.sim` that FORWARDS the
observed play instead of testing it. Encoding the forwarder as a one-stage
threshold test (`if the watch plays C then C else D`) reproduces its behaviour on
the two-valued `Action` type but changes its SHAPE from forwarder to classifier —
and `S` reads shape: a bare `.sim` is legible via `simStep` in both polarities, an
`.ite` needs a reading rule per branch. That mis-encoding is what forced the
(now-retired) `botSysSimStep` rule and blocked the mirror×cupod cells. The tree
DSL says `.sim .self` and the problem does not arise. Every classifier's compiled
term is BYTE-IDENTICAL to what the stage list produced — Gate D1 (`Zoo.lean`) and
every phase theorem's pinned shape certify that by `rfl`. -/

/-- The opposite action — the consequent polarity of a `proveImplD` guard.
    (`Base/Transpose.Action.swap` is the same function, but this layer does not
    import the τ machinery; two lines beat an import for one emission arm.) -/
def otherAction : Action → Action
  | .C => .D
  | .D => .C

/-- The GUARD KIND of a `search` node: which formula, about the resolved probe
    object `P`, the bounded proof search is asked. (`run` — execute the probed
    instance and read its play — is no longer a mode: it is `.ite` over `.sim`,
    exactly as in the base source.)

    `prove` = the probe atom `P plays test against itself`.

    `proveImpl` = the IMPLICATION atom "if I play `test` against them, they play
    `test` against me" (CIMCIC's guard, added 2026-08-20). A genuinely different
    MODALITY, not sugar for `prove`: the implication is provable whenever its
    CONSEQUENT is (`Pf.weakenImpl`), so it fires in strictly more cases — the
    conditional-commitment reading rather than the evidence-gathering one.

    `proveImplD` (2026-08-21) = the ASYMMETRIC-consequent variant: "if I play
    `test`, they play the OPPOSITE back" — DIMCID's guard. Its diagonal is a
    genuine Löb fixpoint on DEFECTION, unlike `proveImpl`'s trivial `implRefl`.

    `proveEq` = a STRUCTURAL IDENTITY atom: **"is the signal I am currently
    treating the lift of B?"** — CupodTrollBot's guard (2026-08-20; RESTATED
    2026-08-24: the original asked about `.opp`, a free pronoun, against a
    counterfactual probe, and was unsatisfiable at every cell). For a NAMED target
    the question is about WHICH hypothesis is in the slot, so the compiler decides
    it from the INDEX and emits a closed, decidably-true-or-false `.eq` — never by
    compiling B's behaviour, which re-enters the mutual-quine wall whenever B
    probes back (Cupod↔CupodTroll). Both directions stay decidable in `S`, so a
    `proveEq` bit is never floor-priced. -/
inductive Mode | prove | proveImpl | proveImplD | proveEq
deriving DecidableEq, Repr

/-- The counterfactual opponent a probe imagines the hypothesis facing: `self` =
    "me, the probing bot" (the self-probe geometry — Dupoc's, Mirror's), or a named
    zoo member. -/
inductive Target (ι : Type) | self | name (i : ι)
deriving DecidableEq, Repr

/-- A bot spec: `Prog` with a `Target` where the base source has "`.opp` facing Q".

    * `const a`                — play `a`
    * `sim t`                  — RUN the hypothesis facing `t` and play what it plays
                                 (base `.sim .opp Q`; MirrorBot is `sim self`)
    * `ite g test p q`         — base `.ite`: run `g`; if it yields `test`, `p`, else `q`
    * `search m t test p q`    — base `.search`: bounded proof search over the
                                 `m`-guard about the hypothesis facing `t`; `p` if
                                 `S` derives it within `Z.budget`, else `q`

    The old stage rows read off directly: `⟨.run, t, test, fire⟩ :: rest` is
    `ite (sim t) test (const fire) rest`, and `⟨.prove, t, test, fire⟩ :: rest` is
    `search .prove t test (const fire) rest`; the default action is the final
    `const`. -/
inductive Spec (ι : Type)
  | const  (a : Action)
  | sim    (t : Target ι)
  | ite    (g : Spec ι) (test : Action) (p q : Spec ι)
  | search (m : Mode) (t : Target ι) (test : Action) (p q : Spec ι)
deriving DecidableEq, Repr

/-- A spec zoo: one spec per index, and the shared prover budget every `search`
    node searches under. -/
structure Zoo (ι : Type) where
  spec   : ι → Spec ι
  budget : Nat

/-! ## Entanglement: which pairs need the binder (§8c.5, 2026-08-20) -/

/-- Does this bot probe "the hypothesis, seeing ME" anywhere in its tree? Exactly
    the property that creates reference cycles: two self-probers `A` and `B` need
    `inst A B ⊃ inst B A ⊃ inst A B`, which no finite tree satisfies. -/
def Spec.selfProbes {ι : Type} : Spec ι → Bool
  | .const _                  => false
  | .sim .self                => true
  | .sim (.name _)            => false
  | .ite g _ p q              => g.selfProbes || p.selfProbes || q.selfProbes
  | .search _ .self _ _ _     => true
  | .search _ (.name _) _ p q => p.selfProbes || q.selfProbes

/-- `A` and `T` are ENTANGLED when both self-probe and they are distinct: the
    2-cycle the `.sys` binder exists to cut. (Same-bot self-probing is the diagonal,
    already cut by the `.self` pronoun; a pair with at most one self-prober bottoms
    out by the §6.3 rank argument.) -/
def Zoo.entangled {ι : Type} [DecidableEq ι] (Z : Zoo ι) (A T : ι) : Bool :=
  A ≠ T && (Z.spec A).selfProbes && (Z.spec T).selfProbes

/-! ## The compiler (§6.2) -/

/-- The guard formula of a `search` node once its probe object is RESOLVED to
    `obj` — `.bot P` for a compiled instance, `.bot (.selfIdx j)` inside a system,
    or the `.self` pronoun on the diagonal (the quine).

    `proveImpl`/`proveImplD` use the SELF PRONOUN for the antecedent's subject
    (2026-08-20): the antecedent is "*I* play `test` against the probed instance",
    and "I" is the term currently being compiled — which cannot contain itself.
    `.self` is the language's knot for exactly that, closed by `subst` at
    consultation time (the `.plays .self …` convention base CIMCIC already uses).
    Those guards are therefore NOT closed under `subst` — unlike `probe`/`probeD` —
    so `probeImpl` is the atom the guard becomes AFTER substitution. -/
def guardOf (m : Mode) (test : Action) (obj : Prog) : Formula :=
  match m with
  | .prove      => .plays obj obj test
  | .proveImpl  => .impl (.plays .self obj test) (.plays obj .self test)
  | .proveImplD => .impl (.plays .self obj test) (.plays obj .self (otherAction test))
  | .proveEq    => .eq obj obj

/-- The index-decided `proveEq` guard for a NAMED target: the guard carries NO
    compiled instance (see `Mode`); the compiler branches on `T = B` exactly as the
    `.self` arms branch on the diagonal, and the `.eq` is the bit's object-language
    witness. -/
def eqGuardOf {ι : Type} [DecidableEq ι] (T B : ι) (test : Action) : Formula :=
  if T = B then .eq (.const test) (.const test)
  else .eq (.const test) (.const (otherAction test))

mutual
/-- **`instAt Z fuel A T`** — bot A's instance at hypothesis T: the ONE place the
    entanglement decision is made. If A and T are a self-probing pair, neither
    instance can contain the other, so emit the 2-member `.sys` system — component
    0 is A-seeing-T, component 1 is T-seeing-A, each probing the other by INDEX —
    and take component 0. Otherwise compile A's tree.

    (Until 2026-08-24 this decision lived inside the self-stage arm of the stage
    compiler and REPLACED that stage — silently discarding the rest of the cascade.
    Harmless for the zoo, where every self-prober's self stage was first and only;
    wrong for a tree, where a `.self` node may sit anywhere. The decision belongs
    to the instance, not to a node.) -/
def instAt (Z : Zoo ι) [DecidableEq ι] : Nat → ι → ι → Prog
  | 0, _, _ => .const .D
  | fuel+1, A, T =>
      if Z.entangled A T then
        .sys (.cons (sysGo Z 1 fuel A T (Z.spec A))
             (.cons (sysGo Z 0 fuel T A (Z.spec T)) .nil)) 0
      else instGo Z fuel A T (Z.spec A)
  termination_by structural fuel _ _ => fuel

/-- Tree compiler for a NON-entangled instance. Probe-object resolution:
    * target `name B` → `.bot (instAt T B)` — the hypothesis's instance seeing B;
    * target `self`, `T ≠ A` → `.bot (instAt T A)` — the hypothesis's instance
      seeing ME (not entangled: `instAt` already ruled that out for this pair);
    * target `self`, `T = A` → the QUINE: the `.self` pronoun instead of a term
      that would have to contain itself — the language's own knot for the
      diagonal (`.plays .self .self C` / `.sim .self .self`, pinned literal by
      `Zoo.lean`'s `inst_dupoc_quine`).

    Every recursive call decrements fuel, so the recursion is STRUCTURAL and the
    output reduces by `rfl` — the property Gate D1 lives on. Fuel exhaustion emits
    `.const .D`; for a well-formed zoo at adequate fuel it is unreachable, and Gate
    D1 certifies that (an exhausted compile cannot be byte-identical to the
    hand-written closure). -/
def instGo (Z : Zoo ι) [DecidableEq ι] : Nat → ι → ι → Spec ι → Prog
  | 0, _, _, _ => .const .D
  | fuel+1, A, T, sp =>
      match sp with
      | .const a => .const a
      | .sim t =>
          let obj : Prog := match t with
            | .self   => if T = A then .self else .bot (instAt Z fuel T A)
            | .name B => .bot (instAt Z fuel T B)
          .sim obj obj
      | .ite g test p q =>
          .ite (instGo Z fuel A T g) test (instGo Z fuel A T p) (instGo Z fuel A T q)
      | .search m t test p q =>
          let pC := instGo Z fuel A T p
          let qC := instGo Z fuel A T q
          match m, t with
          | .proveEq, .name B => .search Z.budget (eqGuardOf T B test) pC qC
          | m, .name B => .search Z.budget (guardOf m test (.bot (instAt Z fuel T B))) pC qC
          | m, .self =>
              let obj : Prog := if T = A then .self else .bot (instAt Z fuel T A)
              .search Z.budget (guardOf m test obj) pC qC
  termination_by structural fuel _ _ _ => fuel

/-- One member of an entangled pair's system, compiled with the PARTNER replaced by
    an indexed pronoun: every `self` target resolves to `.bot (.selfIdx partnerIdx)`
    — frozen, exactly as the off-cycle arms freeze `.bot P` — "the other member of
    my system, whoever that turns out to be" — instead of recursing into a term that
    would have to contain this one. Named targets are OUTSIDE the cycle (third
    parties) and resolve normally. -/
def sysGo (Z : Zoo ι) [DecidableEq ι] (partnerIdx : Nat) : Nat → ι → ι → Spec ι → Prog
  | 0, _, _, _ => .const .D
  | fuel+1, A, T, sp =>
      match sp with
      | .const a => .const a
      | .sim t =>
          let obj : Prog := match t with
            | .self   => .bot (.selfIdx partnerIdx)
            | .name B => .bot (instAt Z fuel T B)
          .sim obj obj
      | .ite g test p q =>
          .ite (sysGo Z partnerIdx fuel A T g) test
            (sysGo Z partnerIdx fuel A T p) (sysGo Z partnerIdx fuel A T q)
      | .search m t test p q =>
          let pC := sysGo Z partnerIdx fuel A T p
          let qC := sysGo Z partnerIdx fuel A T q
          match m, t with
          | .proveEq, .name B => .search Z.budget (eqGuardOf T B test) pC qC
          | m, .name B => .search Z.budget (guardOf m test (.bot (instAt Z fuel T B))) pC qC
          | m, .self => .search Z.budget (guardOf m test (.bot (.selfIdx partnerIdx))) pC qC
  termination_by structural fuel _ _ _ => fuel
end

/-- Default compile fuel: generous for any zoo whose probe-nesting depth is modest
    (the 15-template zoo needs < 12; adding bots that only name existing columns
    does not deepen the nesting). Gate-D1-style byte checks are what certify
    sufficiency per zoo. -/
def instFuel : Nat := 16

/-- **THE COMPILER**: `inst Z A T` = bot A's entire lifted decision procedure at
    point mass on hypothesis T. -/
def inst (Z : Zoo ι) [DecidableEq ι] (A T : ι) : Prog :=
  instAt Z instFuel A T

/-! ## Vectors from the compiler (§6.4) -/

/-- The decision vector of bot A over a zoo enumeration, with weights `w : ι → Nat`
    (the N-ary replacement of the fixed-arity `wC wD wTs wTp wL wE` signatures). -/
def vecOf (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) : List ι → VoteList
  | [] => .nil
  | T :: rest => .cons (w T) (inst Z A T) (vecOf Z A w rest)

theorem vecOf_append (Z : Zoo ι) [DecidableEq ι] (A : ι) (w : ι → Nat) :
    ∀ (l₁ l₂ : List ι), vecOf Z A w (l₁ ++ l₂) = (vecOf Z A w l₁).app (vecOf Z A w l₂)
  | [], _ => rfl
  | T :: rest, l₂ => by
      simp only [List.cons_append, vecOf, VoteList.app, vecOf_append Z A w rest l₂]

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
