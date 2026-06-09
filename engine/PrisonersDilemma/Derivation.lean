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
-- Deliberately ABSENT:
--   • An atomic-`plays` rule: it would carry a `play` hypothesis → cycle;
--     atoms go through `AtomProvable` instead.
--   • GL axiom 4 (`□φ → □□φ`): its soundness obligation is
--     `Provable n φ → Provable m (.box n φ)` — i.e. `S` proving facts about its
--     own provability (reflection). No constructor produces a `.box`-headed
--     conclusion, so this is not a proven-sound rule; it could only be an
--     axiom, and as the general reflection principle it is too strong for a
--     faithful model of a PA-like `S` (inconsistency-risk, and unneeded —
--     critch22's self-fulfilling bots run on Löb, packaged as `PBLT`).
-- The single controlled box principle is therefore `PBLT` (the bounded Löb
-- axiom). GL's K *is* available — but as the derived theorem `K_provable`
-- (budget-respecting), built from `modusPonens` below; it needs no constructor.
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

-- 2. σ₁ atom-provability as an opaque predicate, indexed by budget `k`.
-- `AtomProvable k φ` means "S can prove the atom `φ` within `k` characters".
-- It is opaque, not defined, because any concrete definition is
-- self-referential: justifying a `.plays` atom whose subject is a `.search`
-- program requires consulting that program's guard `□_k ψ`, and `□`'s meaning
-- is `Provable` — so `AtomProvable` would depend on `Provable`, which already
-- depends on `AtomProvable` (§3). A genuine Löb-style loop Lean rejects.
--
-- The budget index is ESSENTIAL: a true atomic play is provable, but generally
-- only once the budget is large enough (its proof has a cost). At a *small*
-- budget a true atom may be unprovable. Dropping this index (the earlier
-- budget-independent version) forces every true play to be provable at every
-- budget — which collapses interactions toward cooperation and makes Critch's
-- Open Problem 3 outcome `outcome(DUPOC,CUPOD) = (D,C)` impossible to even
-- state (DUPOC could never be "unable to prove CUPOD cooperates"). The atom
-- axioms (`atom_complete`, `atom_monotone`, `AtomProvable_sound`) pin it down.
opaque AtomProvable : Nat → Formula → Prop

-- 3. Provability in S within budget `k`: derivable by the structural rules with
-- a derivation of size ≤ `k`, OR an atomic σ₁ fact provable within `k`. This is
-- the truth condition the box modality refers to.
def Provable (k : Nat) (φ : Formula) : Prop :=
  (∃ d : Derivation φ, d.size ≤ k) ∨ AtomProvable k φ

-- 4. The proof-search oracle is now a *definition*, not an axiom: bounded
-- provability, reflected into `Bool` for the evaluator's guard. Classical
-- (hence noncomputable), which is correct for a model of an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)

end PD
