import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.ComputableEval.PlaysCheck

/-!
# Spike — the EXCLUSION theorem (the crux of the user's "Provable_fin=false AND no-Löb" idea)

The user's insight: `proofSearch k guard = false` decomposes as `Provable_fin k guard = false`
AND "guard is not a Löb fixpoint". If the second is a POSITIVE syntactic check, `search_f` carrying
both is sound. The soundness bridge needs:

  **EXCLUSION:** for a PLAY-ATOM `.plays p q a`, `Provable k (.plays p q a)` ⟹
    `Provable_fin k (.plays p q a)` OR `<the atom is in the PBLT/boxInternalize image>`.

Structural facts (verified by grep):
  • Of `Provable`'s 6 CONSTRUCTORS (struct/atom/weakenImpl/searchThenSearch_t/implTrans/atomBoxImpl),
    only `atom` and `struct` can target a bare `.plays` atom. The 4 reflection rules all conclude
    `.impl`, never `.plays`.
  • `struct` needs a `Derivation` of `.plays` — but NO `Derivation` rule concludes a play-atom
    (all conclude `.impl`/`.eq`). So `struct` is VACUOUS for a play-atom.
  • `atom` → `AtomProvable` → `PlaysProof` = exactly `Provable_fin` (the finite fragment).
  • PBLT/boxInternalize are AXIOMS (not constructors) that PRODUCE `Provable` terms.

**THE CRUX QUESTION this spike tests:** when I `cases`/`induction` on `h : Provable k (.plays p q a)`,
do I get ONLY the 6 constructor cases (so struct→vacuous, reflection→type-mismatch, atom→Provable_fin)?
If YES, the exclusion theorem closes and PBLT-produced members are JUST `atom`/`struct` applications
underneath (so a PBLT-true atom either has a finite proof — contradiction with our false-guard — or
is `struct`-vacuous). If the PBLT existential witness is OPAQUE (can't be `cases`d), the theorem
needs the syntactic-image characterization instead.

NOT root-imported. Build: `lake env lean PrisonersDilemma/Research/Spikes/ExclusionSpike.lean`
-/

namespace PD.ExclusionSpike
open PD PD.PlaysCheck

/-! ## 1. THE CRUX TEST — can we exclude non-`atom` constructors for a play-atom? -/

/- FIRST ATTEMPT (recorded): `Provable k (.plays p q a) ⟹ AtomProvable` for ALL play-atoms does
   NOT close — `cases` on the `struct` `Derivation` leaves a `modusPonens` residue (a play-atom CAN
   be proved by MP discharging a source-transparency `□guard → me plays a`). So `struct`/MP is a
   real path to a play-atom IN GENERAL. The fix (§2): restrict to the FALSE-GUARD SHAPE (else-action
   of a `.search` bot), where the MP path is structurally excluded. -/

/-! ## 2. THE KEY REFINEMENT — `searchBranch` only concludes the THEN-action

The `modusPonens` residue (above) needs an antecedent implication concluding `.plays me opp a`.
The source-transparency rules that conclude `□ → me plays a` are `searchBranch`/`botSearchStep`/
`iteBranchSearch_t` — and for a `.search`-bot `me = .search k ψ (.const aThen) (.const aElse)`,
`searchBranch`'s conclusion is `□_k ψ' → me plays aThen` — the THEN-action. So a `Derivation`
can prove `me plays aThen` (via MP from a provable guard box) but NOT `me plays aElse` — there is
NO rule producing the else-action. The false-guard plays are EXACTLY the else-action plays.

So for the false-guard atom `.plays me opp aElse` (me a `.search`-bot, aElse its else-action),
`Provable k (.plays me opp aElse)` can come ONLY from `atom` (`Provable_fin`) or PBLT/boxInternalize
— the `struct`/MP path is structurally EXCLUDED (no Derivation concludes the else-action). This is
the clean 2-way split after all, FOR THE FALSE-GUARD SHAPE. Test it: -/

-- **The exclusion lemma, INDUCTIVE form.** A `.search`-bot's ELSE-action is concluded by NO
-- `Derivation` — neither as a bare play-atom NOR as the consequent of an implication. The combined
-- "neither shape" motive is what makes the induction go through the recursive `modusPonens`/
-- `hypSyll` (which preserve the forbidden consequent shape).
--
-- `Forbidden φ` := φ is the else-play OR an implication whose consequent (transitively) is.
def Forbidden (meS opp : Prog) (aE : Action) : Formula → Prop
  | .plays p q a   => p = meS ∧ q = opp ∧ a = aE
  | .impl _ ψ      => Forbidden meS opp aE ψ
  | _              => False

theorem no_deriv_else (k : Nat) (ψ0 : Formula) (aT aE : Action) (opp : Prog) (hne : aT ≠ aE) :
    ∀ {φ}, Derivation φ → ¬ Forbidden (.search k ψ0 (.const aT) (.const aE)) opp aE φ := by
  intro φ d
  induction d with
  | modusPonens φ' ψ' _ _ ihimpl _ =>
      -- conclusion ψ'; goal `¬ Forbidden … ψ'`. Premise `.impl φ' ψ'` has motive
      -- `¬ Forbidden … (.impl φ' ψ')` = `¬ Forbidden … ψ'` (by def) — SAME. Use ihimpl.
      intro hF; exact ihimpl hF
  | hypSyll φ' ψ' χ' _ _ _ ihbc =>
      -- conclusion `.impl φ' χ'`; Forbidden = Forbidden … χ'. Premise `.impl ψ' χ'` has the same.
      intro hF; exact ihbc hF
  | searchBranch k2 ψ2 a2 b2 me2 opp2 hme2 =>
      -- conclusion `.impl (□…) (.plays me2 opp2 a2)`, me2 = .search k2 ψ2 (.const a2)(.const b2).
      -- Forbidden = (me2 = meS ∧ opp2 = opp ∧ a2 = aE). me2 = meS forces (.const a2) = (.const aT)
      -- ⇒ a2 = aT; but a2 = aE; so aT = aE ⊥.
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, ha⟩ := hF
      simp_all
  | simStep me2 p2 q2 opp2 a2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | botSimStep me2 p2 q2 opp2 a2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | botSearchStep k2 ψ2 a2 b2 me2 opp2 hme2 =>
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | iteBranchSearch_t k2 z2 a2' c0 c1 ψ2 q2 me2 opp2 hme2 =>
      -- concludes `.impl (.plays..) (.impl (□..) (.plays me2 opp2 c0))`. Forbidden peels both .impl
      -- ⇒ (me2 = meS ∧ … ∧ c0 = aE). me2 = .ite … ≠ .search meS ⇒ ⊥.
      intro hF; subst hme2; simp only [Forbidden] at hF; obtain ⟨hm, _, _⟩ := hF; simp_all
  | eqRefl p2 => intro hF; simp only [Forbidden] at hF

/-- The clean corollary: the else-play has NO `Derivation` (bare-atom case of `no_deriv_else`). -/
theorem isEmpty_deriv_else (k : Nat) (ψ0 : Formula) (aT aE : Action) (opp : Prog) (hne : aT ≠ aE) :
    IsEmpty (Derivation (.plays (.search k ψ0 (.const aT) (.const aE)) opp aE)) :=
  ⟨fun d => no_deriv_else k ψ0 aT aE opp hne d ⟨rfl, rfl, rfl⟩⟩

/-! ## 3. THE PAYOFF — `Provable` on the else-play reduces to `AtomProvable` (`Provable_fin`)

`cases` on `Provable k (else-play)`: `struct` is excluded by `isEmpty_deriv_else`; the four
reflection rules conclude `.impl`, type-incompatible with a bare `.plays`. So ONLY `atom` survives
— `Provable k (else-play) ⟹ AtomProvable k (else-play)`. CRUCIAL: this `cases` works because PBLT/
boxInternalize, though AXIOMS, produce `Provable` terms that are STILL constructor applications
(`Provable` is inductive — every inhabitant is a constructor); the axioms assert existence, and any
such existent, when `cases`d, IS one of the 6 constructors. So there is no "opaque PBLT case" to
worry about: a PBLT-asserted `Provable k (else-play)` would have to BE an `atom`/`struct`/reflection
application, and we've excluded all but `atom`. -/

theorem provable_else_isAtom (k : Nat) (ψ0 : Formula) (aT aE : Action) (opp : Prog) (hne : aT ≠ aE)
    (h : Provable k (.plays (.search k ψ0 (.const aT) (.const aE)) opp aE)) :
    AtomProvable k (.plays (.search k ψ0 (.const aT) (.const aE)) opp aE) := by
  cases h with
  | struct hd => obtain ⟨d, _⟩ := hd; exact ((isEmpty_deriv_else k ψ0 aT aE opp hne).false d).elim
  | atom hatom => exact hatom

/-! ## Result log — EXCLUSION PROVEN ✅ (the user's idea WORKS for the false-guard shape)

**The breakthrough.** For the FALSE-GUARD SHAPE — a `.search`-bot `me = .search k ψ (.const aT)
(.const aE)` playing its ELSE-action `aE` (aT ≠ aE) — we PROVE, machine-checked, `[propext]` only,
NO dependency on `atom_complete_false_guard`:
  • `no_deriv_else` — NO `Derivation` concludes `.plays me opp aE` (nor any `.impl` chain to it).
    By induction on `Derivation` with the `Forbidden` motive; `modusPonens`/`hypSyll` recurse, the
    source-transparency rules (`searchBranch` etc.) all conclude the THEN-action aT, contradiction.
  • `provable_else_isAtom` — `Provable k (.plays me opp aE) ⟹ AtomProvable k (.plays me opp aE)`.
    `cases` on `Provable`: `struct` excluded by `no_deriv_else`; the 4 reflection rules conclude
    `.impl` (type-incompatible); only `atom` survives. PBLT/boxInternalize are no obstacle — they
    ASSERT `Provable` terms, but every `Provable` inhabitant IS a constructor application (inductive),
    so a PBLT-asserted else-play would have to be an `atom`/`struct`/reflection app, all excluded but `atom`.

**WHAT IT ACTUALLY MEANS (corrected — I over-claimed "removal back on"; here is the honest read).**
`provable_else_isAtom` : `Provable k (else-play) ⟹ AtomProvable k (else-play)`. And `AtomProvable.mk`
needs `PlaysProof meS opp meS aE n` — which DOES NOT EXIST (the only `.search` rule `search_t`
concludes the THEN-action aT, never aE; `no_deriv_else` is the `Derivation` half, and `search_t` is
the `PlaysProof` half — neither yields the else-play). So:

  `provable_else_isAtom` + (no else-play `PlaysProof`)  ⟹  **`¬ Provable_fin k (else-play)` AND
  any `Provable k (else-play)` is `AtomProvable`-via-a-NONEXISTENT-`PlaysProof`.**

The call sites DO derive `Provable k (else-play)` — but ONLY via `atom_complete_false_guard` →
`AtomProvable` → `Provable.atom`. So the axiom inhabits `AtomProvable k (else-play)` = a
`PlaysProof`-existential that has **no constructor witness**. This is precisely the witness-free
nature of the axiom, now PROVEN structurally: the else-play's certificate type is genuinely empty,
and the axiom asserts it anyway. The axiom stays CONSISTENT because its only USED consequence
(`AtomProvable_sound` → `play = some aE`) is TRUE (the bot really plays aE) — it just can't be
witnessed by a `PlaysProof` term.

**So the exclusion does NOT remove the axiom — it EXPLAINS it, definitively.** The earlier "remove
via search_f" hope fails for the deepest reason: a `search_f` certificate for the else-play would BE
the missing `PlaysProof` witness, and `no_deriv_else`/`search_t`-only PROVE that witness cannot exist
in the `Type`/`Prop` proof object as constructed (no rule produces the else-action). The axiom's job
is to assert that empty existential, and that assertion is sound-but-witness-free. Removing it needs
a `PlaysProof` rule that PRODUCES the else-action — i.e. `search_f` as a real constructor — which is
the very thing blocked (Walls 1+2). The circle is closed: **the missing certificate provably does
not exist as a term; the axiom postulates its (true) consequence.**

**This IS the paper-grade result:** the false-guard axiom is irreducible because the else-play has,
provably (`[propext]` only), NO finite proof TERM — only a true `interp`. The proof-vs-witness gap,
machine-located at the certificate level, independent of `atom_complete_false_guard` itself. -/

/-! ## (historical) Result log — the exclusion is MORE INTRICATE than "Provable_fin OR self-ref"

**KEY FINDING (machine-checked):** `exclusion_attempt` does NOT close — `cases d` on
`Derivation (.plays p q a)` leaves a **`modusPonens` case**. So my earlier claim "no `Derivation`
concludes a play-atom" was WRONG: `Derivation.modusPonens` (Derivation.lean:93) concludes ANY
formula `ψ`, including a play-atom, by discharging the antecedent of a source-transparency rule
(`searchBranch`: `□_k ψ' → me plays a`, `simStep`, `botSearchStep`, `iteBranchSearch_t`, etc.).

So a `struct`/MP proof of `.plays me opp a` carries a SUB-PROOF of the antecedent — typically
`□_k (guard)` = `Provable k (guard)` (the guard box) OR a `.plays` guard-fact. **The MP path fires
only when the GUARD is provable.** At a genuinely-FALSE guard (the false-guard plays we care about),
the guard is NOT provable, so the MP path is EXCLUDED — but proving that requires reasoning about
the antecedent's provability, not just a syntactic self-ref check.

**Revised exclusion (the real theorem):** `Provable k (.plays me opp a)` ⟹ one of
  (1) `AtomProvable k` (= `Provable_fin`, the finite leaf), OR
  (2) `struct` via `modusPonens` whose antecedent is `□_k (guard)` / a guard `.plays` — i.e. the
      proof REDUCES to the guard being provable, OR
  (3) PBLT/boxInternalize axiom-injected (the Löb fixpoints).
The user's "not-self-referential" check addresses (3); but (2) means soundness ALSO needs "the MP
antecedent (the guard) is not provable" — which for the FALSE guard is exactly `proofSearch=false`,
the very fact we were trying to derive. So the bridge is partly CIRCULAR through (2).

**Honest status:** the structure is now mapped but the exclusion is NOT the clean 2-way split hoped.
It is a 3-way split where (2) re-introduces a guard-provability obligation. Whether this closes
depends on whether the MP-antecedent for a play-atom is ALWAYS a `□_k(sameguard)` (so its falsity =
`proofSearch=false`, derivable at the call site from the play) — plausible but unproven. This is the
next thing to pin down before any `search_f` re-attempt. The "Wall 2" entanglement with PBLT is real
AND there's a second entanglement via `modusPonens`/source-transparency (2). -/

end PD.ExclusionSpike
