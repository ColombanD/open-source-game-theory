import PrisonersDilemma.Program

namespace PD
open Classical

/-!
**The proof system `S`** — the inductive `Derivation` (syntactic shape
rules), the opaque `AtomProvable`, `Provable` (`Derivation`-or-atom), and
the proof-search oracle `proofSearch` *defined* as decidable provability
(no longer an axiom).


The only assumptions that survive are isolated to atomic `.plays` formulas
(σ₁-completeness and atom-soundness — see `AtomProvable` below). These cannot
be made constructive: any concrete definition of atom-provability that handles
`.search`-using programs must consult the truth of their guard `□_k ψ`, whose
meaning *is* `Provable` — closing the self-referential loop
`Provable → AtomProvable → (guard) Provable`. This is the Löb/Gödel
self-reference at the heart of the setup (the same reason critch22 needs PBLT),
not merely an artefact of `play` evaluation; Lean's termination checker rejects
every concrete form of it. So atom-provability stays opaque, pinned by axioms.
-/

-- 1. The derivation system. Each rule must be (i) SOUND — its conclusion's
-- `interp` follows from its premises' (enforced by `Derivation.sound` in
-- BaseTheorems.lean) — and (ii) FAITHFUL to a real proof system `S` (≈ PA, per
-- critch22 Appendix B): it must mirror a genuine capability of `S` and must NOT
-- smuggle in semantic completeness / general reflection that PA lacks. The
-- rules fall into two layers:
--
--   • LOGICAL CORE — game-independent propositional inference S has by virtue of
--     being a logic (modus ponens, hypothetical syllogism). Sound trivially
--     because `.impl`'s `interp` is Lean implication.
--   • SOURCE-TRANSPARENCY BRIDGE — game-specific: "S can read `Prog` source
--     code", one rule per `Prog` construct it inspects (`.search`, `.sim`).
--     Justified by Appendix B(a) (S reasons about computable functions).
--
-- Deliberately ABSENT: any atomic-`plays` rule (would carry a `play` hypothesis
-- → cycle; atoms go through `AtomProvable`), and any *box-level* rule (K,
-- axiom-4) — those are not sound at a fixed budget against this finitary model,
-- so box-level reasoning is confined to the single controlled axiom `PBLT`
-- (exactly as critch22 uses Parametric Bounded Löb, not full GL).
inductive Derivation : Formula → Type where
  -- — Logical core —
  /-- Modus ponens: from `φ → ψ` and `φ`, infer `ψ`. Lets `S` *apply*
      implication-valued guards (needed for CIMCIC-style bots). -/
  | modusPonens (φ ψ : Formula) :
      Derivation (.impl φ ψ) → Derivation φ → Derivation ψ
  /-- Hypothetical syllogism: chain `φ → ψ` and `ψ → χ` into `φ → χ`. Primitive
      (not derivable from `modusPonens`: `Derivation` has no
      implication-introduction to discharge a hypothesis). -/
  | hypSyll (φ ψ χ : Formula) :
      Derivation (.impl φ ψ) → Derivation (.impl ψ χ) → Derivation (.impl φ χ)
  -- — Source-transparency bridge —
  /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
  | searchBranch (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
      (hme : me = .search k ψ (.const a) (.const b)) :
      Derivation (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))
  /-- S can read a `.sim` body: `me` plays `a` iff its closed body does. -/
  | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
      Derivation (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                        (.plays me opponent a))

/-- Proof size; the budget measured by `proofSearch`. -/
def Derivation.size : {φ : Formula} → Derivation φ → Nat
  | _, .searchBranch ..       => 1
  | _, .simStep ..            => 1
  | _, .modusPonens _ _ d e   => d.size + e.size + 1
  | _, .hypSyll _ _ _ d e     => d.size + e.size + 1

-- 2. σ₁ atom-provability as an opaque predicate. It is opaque, not defined,
-- because any concrete definition is self-referential: justifying a `.plays`
-- atom whose subject is a `.search` program requires consulting that program's
-- guard `□_k ψ`, and `□`'s meaning is `Provable` — so `AtomProvable` would
-- depend on `Provable`, which already depends on `AtomProvable` (§3). That is a
-- genuine Löb-style loop (independent of `play`), which Lean's termination
-- checker rejects in every form we tried. The two atom axioms below pin it
-- down instead. Budget-independent: an atom is σ₁-true (hence provable at *some*
-- size) or not — no tight size bound to track, making proof-search
-- budget-monotonicity automatic.
opaque AtomProvable : Formula → Prop

-- 3. Provability in S: derivable by the structural rules within budget `k`, OR
-- an atomic σ₁ fact. This is the truth condition the box modality refers to.
def Provable (k : Nat) (φ : Formula) : Prop :=
  (∃ d : Derivation φ, d.size ≤ k) ∨ AtomProvable φ

-- 4. The proof-search oracle is now a *definition*, not an axiom: bounded
-- provability, reflected into `Bool` for the evaluator's guard. Classical
-- (hence noncomputable), which is correct for a model of an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)

end PD
