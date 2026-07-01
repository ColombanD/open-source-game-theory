# Route 2b — Proof-Theoretic Normalization Roadmap (discharging `provesN_play_extract`)

**Goal.** Prove `provesN_play_extract`:
`ProvesN (encodeF (.plays pr qr a)) [] (encodeF (.plays pr qr a)) → ∃ n, play n pr qr = some a`.
This is the SOLE remaining hypothesis of `engine_pblt_plays`; discharging it deletes the `PBLT` axiom.

**Why normalization (not a model).** This session PROVED every self-contained model/realizability
interpretation of the object system is unsound (validates `repr`/`ctx` definitionally ⇒ proves false
atoms; see `ConstructiveLobToy.lean §8`). Prior session closed the classical case-split and the naive
back-translation. So the witness MUST be produced by a PROOF-THEORETIC argument that CONSUMES the
engine's `Provable_sound` at the play-atom — i.e. by turning the object proof into engine DATA.

**The engine hooks (verified).**
- `Formula.interp (.plays p q a) = ∃ n, play n p q = some a`  — the play witness we want.
- `Formula.interp (.box n φ)     = Provable n φ`               — engine box = engine provability.
- `Provable_sound : ∀ k φ, Provable k φ → φ.interp`            — engine soundness (a THEOREM).
- `ProvesN.engineLeaf : Provable m φ → ProvesN p Γ (encodeF φ)`— the ONLY way engine facts enter ProvesN.
- Object box `interpN (□a) = ProvesN p [] a`; HBL rules `necN/kN/fourN` mirror engine `boxIntro/axK/box4`.

---

## The core idea: DECIDABLE object box ⇒ RUN `bloeb` to an engine `Provable` witness

The object `bloeb` term proves `p` SYNTACTICALLY. The block on extraction is that `ProvesN`'s `box`
is a bare `Prop` with no computational content. If we make the object box DECIDABLE — `box a` ⇔
"∃ proof term of `a` of size ≤ k", a FINITE search — then the `bloeb` proof term can be EVALUATED:
its `necN` steps become actual bounded-proof witnesses, and the chain computes a `Provable n φ` for
the play-atom `φ`. Then `Provable_sound` gives the play. The witness comes from the engine (via
`Provable_sound`), extracted by RUNNING the constructive term against a decidable box — exactly the
CLAUDE.md crux ("`Provable` collapses to the decidable finite-proof predicate ⇒ eval computable").

This is Critch's own point: BOUNDED provability (∃ proof TERM of size ≤ k) is decidable by
enumeration, unlike RE unbounded provability. The object system must be rebuilt so its `box` is that
decidable predicate, and `bloeb` must thread WITNESSES (size-bounded proof terms), not bare `Prop`s.

---

## Milestones (staged, each independently checkable; kill-criteria stated)

### M-N1. Decidable bounded provability for the CONSTRUCTIVE toy proof system.
Over `ConstructiveLobToy.Pf p` (the axiom-free HBL+diagonal term system), define
`Boxable p k φ := ∃ t : Pf p φ, size t ≤ k` and prove `Decidable (Boxable p k φ)` for a FIXED `φ`
(conclusion pins the atoms; recurse on `(k, φ)`). Needs: character-faithful `size` (leaf pays the
embedded formula's size — refactor), + a formula-size bound from proof-size, + the cut-formula search
finite. **Kill-criterion:** if the `mp` cut (unbounded cut formula) cannot be bounded even with
faithful sizes at fixed φ, decidability fails ⇒ the whole decidable-box route is dead; fall back to N5.
**Deliverable:** `instance : Decidable (Boxable p k φ)` + `Boxable_spec`.

### M-N2. Witness-threading `bloeb`: from a bounded Löb premise, a bounded proof of `p`.
Upgrade `Pf.bloeb` to `bloebW : {t : Pf p (□p→p) // size t ≤ k} → {s : Pf p p // size s ≤ g k}` with an
EXPLICIT size bound `g` (the chain is nec/axK/four/S/mp — each a constant or +1, so `g` is linear in
`k` + the diagonal's fixed cost). **This is the "exhibit a size-≤-k proof term" the crux names.**
**Kill-criterion:** if `g k` blows up non-computably (it won't — the chain is fixed-depth), dead.
**Deliverable:** `bloebW` with a proven, closed-form `g`.

### M-N3. RUN the witness against decidable box to get the target's provability.
With M-N1 (decidable box) + M-N2 (bounded proof of `p`), show `Boxable p (g k) p` holds
CONSTRUCTIVELY, and — the crux step — that this DECIDABLE fact, for `p = encodeF(play-atom)`, yields
`∃ m, Provable m φ` in the engine. The bridge: an object bounded-proof of `encodeF φ` maps to an engine
`Provable m φ` by mirroring each object rule to its engine twin (`necN↦boxIntro`, `kN↦axK`,
`fourN↦box4`, `engineLeaf↦id`) — a STRUCTURAL recursion on the (now finite, witness-bearing) object
proof term, which — UNLIKE the `Prop`-level back-translation that couldn't be stated — CAN be stated on
proof TERMS because `repr`/`ctx` are eliminated by M-N2's normalization (the `bloeb` term's `ψ` steps
are internal; its CONCLUSION `p` is engine-shaped, and the witness-threading exposes an engine-mirrorable
skeleton). **Kill-criterion:** if `repr`/`ctx` sub-terms survive into the witness and have no engine
twin (they don't — engine has no diagonal), the structural map breaks ⇒ need M-N4.
**Deliverable:** `objProof_to_Provable : {t : Pf p (encodeF φ) // size ≤ k} → ∃ m, Provable m φ`.

### M-N4. (Contingency for M-N3) Semantic bridge for the diagonal sub-terms.
If `repr`/`ctx` witnesses survive normalization, they conclude `iff`s about `gApp`/`betaA` — NOT
engine formulas. But their ROLE in `bloeb` is to establish `Provable n φ` for the play-atom via the
Löb closure. Show that a witness-bearing object proof of a PLAY-ATOM (not an arbitrary formula) whose
only non-engine steps are `repr`/`ctx` around the SINGLE diagonal `ψ := betaA p` can be collapsed:
the diagonal establishes `proofSearch`-truth of the play-atom's guard, which the engine reads directly.
This is where the engine's `.search`-bot self-reference (Path B, revisited with WITNESSES this time)
may finally substitute for the object diagonal — the bot IS the fixpoint, and now we carry the proof
term to make it compute. **Kill-criterion:** if the collapse still needs the outcome, route 2b via
normalization is also blocked ⇒ escalate to N5.

### M-N5. Fallback / honest floor.
If M-N1 or M-N3/4 hit a wall, the result banked is: constructive Löb term (M1) + model-extraction
impossibility (M2 negative) + a precise proof-theoretic obstruction. That is a complete, defensible
characterization of the crux — publishable — even without deleting `PBLT`.

### M-N6. Port toy → engine + delete the axiom.
Only after N1–N4 close on the toy: port the decidable-box + witness-threading + rule-mirroring to the
real `ProvesN`/`Provable`, discharge `provesN_play_extract`, wire `engine_pblt_plays` into the 4
consumers (DupocBot, CupodBot, PrudentBot, JustBot), delete `axiom PBLT` → 1 axiom.

---

## Risk assessment (honest)

- **N1 (decidable box)** is the linchpin and the highest-risk NEW content. The `mp`-cut finiteness is
  the crux; the earlier note flagged unbounded atom-codes, but at FIXED φ this is tractable. Real work,
  bounded scope (~the hardest single Lean lemma of the route).
- **N2 (witness threading)** is low-risk mechanical (the chain is fixed-depth; sizes compose linearly).
- **N3 (rule mirroring)** is medium — it's the back-translation, but now on witness-bearing TERMS where
  the diagonal is normalized away. The prior "can't even state it" objection is addressed by M-N2.
- **N4** is the genuine residual research risk (whether the diagonal collapses at play-atoms).
- Overall: N1+N2 are a concrete, worth-doing block that either UNLOCKS the route or KILLS it cleanly
  (kill-criteria stated). Start with N1.

## Immediate next action
Start **M-N1**: refactor `ConstructiveLobToy.Pf.size` to character-faithful, then prove
`Decidable (Boxable p k φ)` at fixed φ. This is self-contained, in the toy, and its outcome (pass/kill)
determines whether the decidable-box route is viable before any engine porting.

---

## M-N1 PROGRESS (2026-07-01) — `Research/Spikes/pblt/MN1_decidable.lean`

**Half done, sorry-free for the proven part.** Character-faithful `Pf.sizeF` (each leaf pays its
CONCLUSION's `Fml.size`; the earlier "leaf pays embedded-atom size" was wrong — axiom schemes repeat
subformulas, so `sizeF_ge_concl` needed conclusion-size charging). Proven:
  • `sizeF_ge_concl : φ.size ≤ t.sizeF` — a bounded proof has a bounded CONCLUSION.
  • `mp_cut_bounded : a.size ≤ (mp f g).sizeF` — the `mp` CUT formula is SIZE-bounded.
So the first half of the decidability obstruction (unbounded `mp` cut) is REMOVED.

**Residual sub-obstruction (the N1 crux, identified precisely):** bounded `Fml.size` ⇏ finite, because
`atom n`/`gApp c` codes range freely. Need an ATOM-CLOSURE invariant: every formula in a `Pf p φ` proof
has atoms/codes tracing to SUBFORMULA-codes of `p` (then the atom set is finite ⇒ decidable). Probe
finding: a bare `atom n`/`gApp c` is concluded by NO rule except `mp` — so bare atoms aren't
syntactically excluded, but no LEAF concludes a bare atom or an implication INTO one (`ax_k` gives
`a→(b→a)`; `repr`/`ctx` conclude iffs over gApp/imp/betaA). Likely invariant (next lemma, one `sorry`
in the spike marks it): every provable formula is imp/iff/box with atoms from `p`'s subformula-codes,
by rule-induction. **This lemma is the make-or-break of N1.** If it holds → decidable box → resume N2.
If it fails → escalate to N4/N5.
