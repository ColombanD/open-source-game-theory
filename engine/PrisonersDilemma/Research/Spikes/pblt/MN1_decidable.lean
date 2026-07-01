import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# ⚠️ SUPERSEDED (2026-07-01) — route (B) tangent (decidable box), NOT the axiom-removal plan.

Pursued decidable bounded provability for the CONSTRUCTIVE route (B) / computable `eval`. Not needed to
remove the `PBLT` axiom (route A, faithful). Kept as a record: the `mp`-cut is size-bounded
(`mp_cut_bounded`), but enumeration is dead (atom-closure false — see the KILL-TEST). See
`PBLT_REMOVAL_ROADMAP.md` and memory `project_pblt_removal_plan` for the actual plan (constructed `Bew`).

---

M-N1 spike: decidability of bounded provability for the toy Pf, at fixed φ.

The crux obstruction: `mp` has an unbounded cut formula. We probe whether a character-faithful
size + a formula-size-bound lemma tames it, BEFORE committing to the full refactor.

Strategy probe: define `Fml.size`, a faithful `Pf.sizeF` where leaves pay their conclusion size,
prove `proof size ≥ conclusion Fml.size` (so bounded proof ⇒ bounded conclusion), and check whether
the `mp` cut formula gets bounded. If yes, decidability is a finite search; if no, route needs N4/N5.
-/

namespace MN1

-- minimal copy of the toy Fml + encode (self-contained probe)
inductive Fml where
  | atom (n : Nat) | gApp (c : Nat) | betaA (b : Fml)
  | imp (a b : Fml) | iff (a b : Fml) | box (k : Nat) (a : Fml)
deriving DecidableEq, Repr, Inhabited

def Fml.size : Fml → Nat
  | .atom _ => 1 | .gApp _ => 1 | .betaA b => b.size + 1
  | .imp a b => a.size + b.size + 1 | .iff a b => a.size + b.size + 1 | .box _ a => a.size + 1

def encode : Fml → Nat
  | .atom n => Nat.pair 0 n | .gApp c => Nat.pair 1 c | .betaA b => Nat.pair 2 (encode b)
  | .imp a b => Nat.pair 3 (Nat.pair (encode a) (encode b))
  | .iff a b => Nat.pair 4 (Nat.pair (encode a) (encode b))
  | .box k a => Nat.pair 5 (Nat.pair k (encode a))
def selfApply (b : Fml) : Fml := .betaA b

inductive Pf (p : Fml) : Fml → Type where
  | ax_k (a b : Fml) : Pf p (.imp a (.imp b a))
  | ax_s (a b c : Fml) : Pf p (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp {a b : Fml} : Pf p (.imp a b) → Pf p a → Pf p b
  | id (a : Fml) : Pf p (.imp a a)
  | iffIntro {a b : Fml} : Pf p (.imp a b) → Pf p (.imp b a) → Pf p (.iff a b)
  | iffF {a b : Fml} : Pf p (.iff a b) → Pf p (.imp a b)
  | iffB {a b : Fml} : Pf p (.iff a b) → Pf p (.imp b a)
  | nec {a : Fml} {k : Nat} : Pf p a → Pf p (.box k a)
  | axK (k : Nat) (a b : Fml) : Pf p (.imp (.box k (.imp a b)) (.imp (.box k a) (.box k b)))
  | four (k : Nat) (a : Fml) : Pf p (.imp (.box k a) (.box k (.box k a)))
  | repr (b : Fml) : Pf p (.iff (.betaA b) (.gApp (encode (selfApply b))))
  | ctx (ψ : Fml) {k : Nat} : Pf p (.iff (.gApp (encode ψ)) (.imp (.box k ψ) p))

/-- The conclusion of a `Pf` term (its `φ` index, as a value — needed to charge each leaf its own
    conclusion size in `sizeF`). -/
def Pf.concl : {p φ : Fml} → Pf p φ → Fml := fun {_ φ} _ => φ

/-- CHARACTER-FAITHFUL size: every leaf pays its CONCLUSION's `Fml.size` (writing the proved formula
    costs at least writing the formula), composites sum children + 1. Then `concl.size ≤ sizeF`. -/
def Pf.sizeF : {p φ : Fml} → Pf p φ → Nat
  | _, _, .ax_k a b      => (Fml.imp a (.imp b a)).size
  | _, _, .ax_s a b c    => (Fml.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))).size
  | _, _, .mp f g        => f.sizeF + g.sizeF + 1
  | _, _, .id a          => (Fml.imp a a).size
  | _, _, .iffIntro f g  => f.sizeF + g.sizeF + 1
  | _, _, .iffF f        => f.sizeF + 1
  | _, _, .iffB f        => f.sizeF + 1
  | _, _, .nec f         => f.sizeF + 1
  | _, _, .axK k a b     => (Fml.imp (.box k (.imp a b)) (.imp (.box k a) (.box k b))).size
  | _, _, .four k a      => (Fml.imp (.box k a) (.box k (.box k a))).size
  | _, _, .repr b        => (Fml.iff (.betaA b) (.gApp (encode (selfApply b)))).size
  | pp, _, .ctx ψ        => (Fml.iff (.gApp (encode ψ)) (.imp (.box 0 ψ) pp)).size  -- k erased in size; use 0

/-- The KEY lemma for decidability: proof size bounds conclusion size. Bounded proof ⇒ bounded
    conclusion ⇒ (with bounded atoms) finite search space ⇒ decidable. -/
theorem sizeF_ge_concl {p φ : Fml} (t : Pf p φ) : φ.size ≤ t.sizeF := by
  induction t with
  | ax_k a b => simp [Pf.sizeF]
  | ax_s a b c => simp [Pf.sizeF]
  | mp f g ihf ihg => simp only [Pf.sizeF] at *; simp only [Fml.size] at ihf; omega
  | id a => simp [Pf.sizeF]
  | iffIntro f g ihf ihg => simp only [Pf.sizeF] at *; simp only [Fml.size] at ihf ihg ⊢; omega
  | iffF f ih => simp only [Pf.sizeF] at *; simp only [Fml.size] at ih ⊢; omega
  | iffB f ih => simp only [Pf.sizeF] at *; simp only [Fml.size] at ih ⊢; omega
  | nec f ih => simp only [Pf.sizeF] at *; simp only [Fml.size]; omega
  | axK k a b => simp [Pf.sizeF]
  | four k a => simp [Pf.sizeF]
  | repr b => simp [Pf.sizeF]
  | ctx ψ => simp only [Pf.sizeF, Fml.size]; omega

/-- The CUT-BOUND lemma: in `mp f g`, the cut formula (`g`'s conclusion `a`) has size ≤ sizeF (mp f g).
    This is what makes the `mp` search finite. Follows from sizeF_ge_concl on g. -/
theorem mp_cut_bounded {p a b : Fml} (f : Pf p (.imp a b)) (g : Pf p a) :
    a.size ≤ (Pf.mp f g).sizeF := by
  have := sizeF_ge_concl g
  simp only [Pf.sizeF]; omega

/-! ## VERDICT — M-N1 half done: the size-cut is TAMED; atom-boundedness is the residual sub-obstruction.

PROVEN (this spike, sorry-free):
  • character-faithful `sizeF` (each leaf pays its conclusion's `Fml.size`);
  • `sizeF_ge_concl` — a proof of size ≤ k has conclusion of `Fml.size ≤ k`;
  • `mp_cut_bounded` — the `mp` cut formula has `Fml.size ≤ sizeF`, so it is SIZE-bounded.
So the first half of the decidability obstruction (unbounded cut formula) is REMOVED: with faithful
sizes, a bounded proof's cut formulas are size-bounded.

REMAINING sub-obstruction (the real N1 risk): formulas of bounded `Fml.size` are STILL infinite,
because `atom n`/`gApp c` range over all codes. So "finitely many cut formulas of size ≤ k" needs the
ATOMS to be drawn from a finite set. This is NOT closed under the rules: `mp` can cut through a
`repr b`/`ctx ψ` introducing `encode`-codes of ARBITRARY `b`/`ψ`. Two ways forward:
  (a) prove the provable formulas are atom-restricted: no rule concludes a bare `atom n`, and every
      `gApp c`/`betaA b` in a proof of φ traces to a code of a SUBFORMULA of φ or p (a subformula-code
      closure lemma). If this holds, the atom set is finite ⇒ decidable. LIKELY TRUE, real work.
  (b) if (a) fails (a proof of φ genuinely needs an unrelated `repr b`), N1's decidable-box route is
      blocked at the toy level ⇒ escalate to N4 (semantic collapse of the diagonal) or N5 (floor).

NEXT: attempt (a) — the subformula-code closure lemma. This is the crux of N1. -/

#check @sizeF_ge_concl
#check @mp_cut_bounded

-- PROBE (atom-reachability): a bare `atom n`/`gApp c` is concluded by NO rule except `mp` (`cases`
-- leaves only that case). So bare atoms aren't syntactically excluded — the atom-closure question is
-- whether they are ever REACHED. The KILL-TEST below settles it NEGATIVELY (closure is false).

-- KILL-TEST: are there INFINITELY MANY distinct size-bounded proofs (at some fixed conclusion shape)?
-- repr (atom m) : Pf p (iff (betaA (atom m)) (gApp (encode (betaA (atom m))))) has sizeF = 4 for ALL m.
-- So {repr (atom m) | m : Nat} are infinitely many DISTINCT proofs of size 4, with distinct
-- conclusions (distinct m). This means: the set of size-<=-4 proofs is INFINITE. Confirm the sizes:
example (p : Fml) (m : Nat) : (Pf.repr (p := p) (.atom m)).sizeF = 4 := by
  simp [Pf.sizeF, Fml.size]

-- And distinct m give distinct conclusions (so distinct proofs), via encode injectivity on betaA:
example (p : Fml) (m1 m2 : Nat) (h : m1 ≠ m2) :
    (Pf.repr (p := p) (.atom m1)).concl ≠ (Pf.repr (p := p) (.atom m2)).concl := by
  simp only [Pf.concl, ne_eq]
  intro hc; apply h
  simp only [Fml.iff.injEq, Fml.betaA.injEq, Fml.atom.injEq] at hc
  exact hc.1

/-! ## FINDING — N1's NAIVE ENUMERATION is DEAD; the atom-closure invariant is FALSE (machine-checked).

Two machine-checked facts:
  1. `{repr (atom m) | m : Nat}` are ∞-many size-4 proofs with DISTINCT conclusions ⇒ the size-bounded
     proof SPACE is infinite, and the atom-closure invariant (proof atoms ⊆ subformula-codes of `p`) is
     FALSE — `repr (atom m)` introduces the fresh code `m` at bounded size.
  2. At a FIXED conclusion φ, the `mp` cut ranges over ∞-many PROVABLE cut formulas: if φ is provable,
     `ax_k : φ → (a → φ)` + mp gives `Pf p (a → φ)` for EVERY `a`, so `mp` re-derives φ through ANY
     provable `a`; `{repr (atom m)}` supplies ∞-many. So cut-formula ENUMERATION at fixed φ is infinite.

⇒ `Decidable (Boxable p k φ)` cannot be obtained by "enumerate bounded proofs / cut formulas".

HONEST SCOPE OF THIS NEGATIVE (do not overclaim): this kills the ENUMERATION method, NOT decidability
itself — `Boxable` is a `Prop` ("≥1 proof exists"), which could still be decidable by a cleverer
(non-enumerative) argument. But any such argument needs proofs in a NORMAL FORM whose cuts are
subformula-bounded — i.e. a CUT-ELIMINATION for the toy. For a system WITH the Löb diagonal (`repr`/
`ctx`), cut-elimination is exactly the open modal-fixpoint normalization problem; NOT available free.
This is the SAME root cause as real `Provable`/`proofSearch` being `noncomputable`.

CONSEQUENCE for the route: the "decidable box by enumeration" framing of M-N1→N3 is closed. But note
what N2/N3 ACTUALLY need is WEAKER than full decidability: they need to RUN the SPECIFIC `bloeb` term
(a fixed, known proof) to an engine witness — NOT decide arbitrary provability. So the enumeration death
does not necessarily kill N2/N3; re-scope N1 to "the bloeb term normalizes", not "box is decidable".
Next: pursue N2 (witness-threading the KNOWN bloeb term) directly, sidestepping general decidability. -/

end MN1
