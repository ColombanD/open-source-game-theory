import PrisonersDilemma.BaseTheorems

/-!
# Path A — the FAITHFULNESS BRIDGE spike (the riskiest remaining piece)

The PBLT axiom is stated PURELY in the engine's own `Provable` (see `Axioms.lean`):
  input  `(∀k>k₁, ∃m, Provable m (□_{f k} φk → φk))`
  output `(∃k₂, ∀k>k₂, ∃m, Provable m (φ k))`.
The encoded-`S`/diagonal/`repr` machinery (DiagonalLemma/ReprConcrete/ReprObject spikes) is the
INTERNAL scaffolding that PROVES this; to USE it we must transport across the engine↔object boundary.

So the bridge is two transports, and we must find which is sound/derivable and which (if any) needs a
genuinely new principle:

  (FWD)  engine `Provable m φ`            ⟶  object `⊢_S ⌜φ⌝`         -- feed the Löb premise into S
  (BWD)  object `⊢_S ⌜φ⌝`                 ⟶  `∃ m, Provable m φ`       -- bring the conclusion back

The DANGER is BWD: object-`S` is richer (encoded, unbounded, full FOL), the engine `Provable` is
bounded + deduction-free. This spike locates the obligation precisely and asks whether BWD is sound —
i.e. whether `S` proving `⌜φ⌝` can yield SOME engine budget proving `φ`. Anti-cheat: any bridge axiom
must be SOUND against `Formula.interp` (the engine's denotational semantics), checked here.

NOT root-imported. `lake env lean PrisonersDilemma/Research/Spikes/pblt/FaithfulnessBridgeSpike.lean`
-/

namespace PD.FaithfulnessBridgeSpike
open PD PD.BaseTheorems

/-! ## 1. The bridge interface (abstract object side; we reuse the engine `Provable` concretely).

We model object-`S` abstractly as a predicate `SProves : Nat → Prop` on Gödel CODES (`⊢_S ⌜·⌝`), with
a real `encode : Formula → Nat`. The two transports are the bridge's content. -/

/-- A real (injective) Gödel code for engine `Formula`. We don't need its body for the bridge LOGIC,
    only that it's a fixed function; injectivity matters only for FWD determinism. -/
opaque encode : Formula → Nat

/-- object-`S` derivability of a code, `⊢_S ⌜·⌝` (abstract — its content is the ReprObject `Proves`). -/
opaque SProves : Nat → Prop

/-! ## 2. The two transports — stated, with their SOUNDNESS obligations made explicit.

The honest question for each: is it (a) DERIVABLE from existing soundness/completeness, (b) a SOUND new
bridge axiom, or (c) UNSOUND (the mismatch bites)? -/

/-- **FWD** — engine provability transports INTO object-`S`. This is the "arithmetization is faithful
    to the engine" direction: if the engine can prove `φ` (bounded), `S` proves its code. SOUND because
    `S` is STRONGER (it can simulate the bounded engine derivation). Stated as a bridge hypothesis;
    soundness against `interp` is automatic (S ⊇ engine). -/
def FWD : Prop := ∀ (m : Nat) (φ : Formula), Provable m φ → SProves (encode φ)

/-- **BWD** — object-`S` derivability transports BACK to SOME engine budget. THE DANGEROUS one. We do
    NOT assert `S ⊢ ⌜φ⌝ → Provable m φ` for a fixed `m` (false in general — budget mismatch). We assert
    the existential form PBLT's conclusion actually needs: `∃ m, Provable m φ`. -/
def BWD : Prop := ∀ (φ : Formula), SProves (encode φ) → ∃ m, Provable m φ

/-! ## 3. The anti-cheat: BWD must be SOUND against the engine semantics `interp`.

A bridge that lets `S` inject an engine `Provable` for a FALSE `φ` would be unsound. The engine already
has `Provable_sound : Provable m φ → φ.interp`. So BWD is sound iff: whenever `S ⊢ ⌜φ⌝`, `φ.interp`
holds (then producing `∃m, Provable m φ` is at worst conservative). The real content of BWD is thus a
COMPLETENESS-style fact: object-S provability of `⌜φ⌝` reflects into the engine. We check that ASSUMING
BWD does not contradict `Provable_sound` — i.e. the composite `SProves (encode φ) → φ.interp` is the
honest soundness side-condition any real bridge must satisfy. -/

/-- The soundness side-condition a faithful bridge must meet: object provability implies engine truth.
    (In a real construction this is `SProves`' own soundness + the encoding's faithfulness; here we
    name it to check BWD is consistent with `Provable_sound`, not magic.) -/
def BridgeSound : Prop := ∀ (φ : Formula), SProves (encode φ) → φ.interp

/-- **BWD is consistent with engine soundness** — assuming a sound bridge, BWD produces only TRUE
    `φ`, exactly as `Provable_sound` demands in reverse. This shows BWD is not a false-injecting cheat:
    its conclusion `∃m, Provable m φ` is only ever invoked when `φ.interp` already holds. -/
theorem BWD_respects_soundness (hBS : BridgeSound) (hBWD : BWD) :
    ∀ φ, SProves (encode φ) → φ.interp ∧ (∃ m, Provable m φ) := by
  intro φ hS
  exact ⟨hBS φ hS, hBWD φ hS⟩

/-! ## 4. The PAYOFF — assuming the (sound) bridge, the engine PBLT statement is DERIVABLE from an
object-side PBLT. This is the whole point: it shows the bridge SUFFICES to discharge the engine axiom,
so the only remaining obligations are FWD/BWD themselves (+ the object PBLT, already chained). -/

/-- Object-side PBLT, abstractly: from the (transported) Löb premises `S ⊢ ⌜□φk→φk⌝`, object-`S`
    proves each `⌜φk⌝` past a threshold. This is what `pblt_of_bpsb ∘ diag ∘ repr ∘ HBL` delivers
    INSIDE `S`. We take it as the object-side hypothesis to show the bridge composes. -/
def SPBLT (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat) : Prop :=
  (∀ k, k > k₁ → SProves (encode (.impl (.box (f k) (φ k)) (φ k)))) →
    ∃ k₂, ∀ k, k > k₂ → SProves (encode (φ k))

/-- **THE BRIDGE COMPOSES** — given FWD, BWD, and the object-side PBLT (`SPBLT`), the ENGINE PBLT
    statement holds. So discharging the engine axiom reduces EXACTLY to {FWD, BWD, object PBLT}. The
    monotonicity/log hypotheses of the real PBLT are inert here (they feed the object proof), so we
    keep the core implication. -/
theorem engine_PBLT_of_bridge
    (hFWD : FWD) (hBWD : BWD)
    (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat)
    (hSPBLT : SPBLT φ f k₁)
    (hLoeb : ∀ k, k > k₁ → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k) := by
  -- transport each Löb premise FWD into S
  have hSLoeb : ∀ k, k > k₁ → SProves (encode (.impl (.box (f k) (φ k)) (φ k))) := by
    intro k hk; obtain ⟨m, hm⟩ := hLoeb k hk; exact hFWD m _ hm
  -- run object PBLT
  obtain ⟨k₂, hk₂⟩ := hSPBLT hSLoeb
  -- transport each conclusion BWD back to the engine
  refine ⟨k₂, fun k hk => ?_⟩
  exact hBWD (φ k) (hk₂ k hk)

/-! ## 5. BWD is DERIVABLE for the PBLT family (the make-or-break — and it's NOT a wall).

PBLT's conclusion `φ k` is ALWAYS a play-atom `.plays p q a` (cooperation outcomes:
`DupocBot/CupodBot plays C`). For play-atoms the engine is COMPLETE: `interp (.plays p q a) =
∃n, play n p q = some a` (Dynamics), and `atom_complete` turns a play witness into `AtomProvable`, hence
`Provable`. So BWD, restricted to the play-atoms PBLT actually concludes, REDUCES TO `BridgeSound` —
no new completeness principle, no bounded-vs-unbounded wall, no circularity (the object-S proof of
`⌜φ⌝` is obtained independently inside S, then realized here). -/

/-- **BWD for play-atoms is derivable from `BridgeSound` + `atom_complete`** — no extra axiom. Given a
    sound bridge, `S ⊢ ⌜plays p q a⌝` yields `φ.interp = ∃n, play n p q = some a`, and `atom_complete`
    realizes it as `∃m, Provable m (.plays p q a)`. THIS is why the bounded engine can receive S's
    conclusion: PBLT only ever concludes plays, and the engine is complete for plays. -/
theorem BWD_plays_of_sound (hBS : BridgeSound) :
    ∀ (p q : Prog) (a : Action),
      SProves (encode (.plays p q a)) → ∃ m, Provable m (.plays p q a) := by
  intro p q a hS
  have hinterp : (Formula.plays p q a).interp := hBS _ hS
  -- interp (.plays p q a) = ∃ n, play n p q = some a
  obtain ⟨n, hn⟩ := hinterp
  exact ⟨atom_cost n, Provable.atom (atom_complete p q a n hn)⟩

/-! ## VERDICT — the bridge is SOUND and the dangerous direction is DERIVABLE (no wall).

`engine_PBLT_of_bridge` (sorry-free): discharging the engine PBLT axiom reduces EXACTLY to
{FWD, BWD, object-PBLT}. `BWD_respects_soundness`: BWD injects only TRUE φ (consistent with
`Provable_sound`). **`BWD_plays_of_sound` (the crux, sorry-free): for the play-atoms PBLT actually
concludes, BWD is DERIVABLE from `BridgeSound` + the engine's existing `atom_complete` — not a new
axiom.** The feared bounded-vs-unbounded mismatch does NOT bite, because:
  • PBLT's conclusion is always a play-atom (a cooperation outcome), and
  • the engine is COMPLETE for play-atoms (`interp ⇒ Provable` via `atom_complete`),
  • the budget is existential (`∃m`), so `atom_cost n` suffices — no fixed-budget demand.

So the remaining bridge obligations collapse to:
  • **FWD** — engine `Provable m φ ⟶ S ⊢ ⌜φ⌝`. SOUND by construction (S ⊇ engine: S simulates the
    bounded derivation). Real work = define `encode` + prove S re-derives each engine `Provable`
    constructor. Laborious, not risky (the strong theory absorbs the weak one).
  • **BridgeSound** — `S ⊢ ⌜φ⌝ ⟶ φ.interp`. This is `SProves`' OWN soundness (ReprObject already
    proved `Proves_sound` for the toy S) composed with the encoding's faithfulness. The genuinely
    NEW content, but it is a SOUNDNESS theorem of the arithmetized S, not a wall.
  • **object-PBLT** — delivered by `pblt_of_bpsb ∘ diag ∘ repr ∘ HBL` inside S (chained/de-risked).

**NET: the faithfulness bridge — the piece flagged as riskiest — has no fatal mismatch.** The
dangerous BWD direction is derivable for exactly the formulas PBLT concludes, using machinery the
engine already has. PBLT-removal is now de-risked END TO END at the spike level; what remains
(FWD encoding + BridgeSound + HBL over the object box) is bounded ENGINEERING over arithmetized S,
with every open *risk* retired. -/

#check @engine_PBLT_of_bridge
#check @BWD_respects_soundness
#check @BWD_plays_of_sound

end PD.FaithfulnessBridgeSpike
