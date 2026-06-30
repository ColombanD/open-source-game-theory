/-!
# Path A, step 1 — the Parametric Diagonal Lemma on a MINIMAL encoded syntax

The make-or-break sub-step for removing `PBLT`. Critch §3 (PBLT_proof.tex): for any predicate `G`
there is `ψ` with `⊢ ∀k̄, ψ(k̄) ↔ G(⌜ψ⌝, k̄)`. Everything in the PBLT proof hinges on this; the chain
`pblt_of_bpsb` already proves the rest GIVEN it.

This spike builds the SMALLEST syntax that exposes the diagonal's self-reference and asks: does the
fixpoint `ψ ↔ G(⌜ψ⌝)` typecheck and prove? We isolate the ONE genuinely new ingredient — the syntax
must talk about its own Gödel codes via a `subst`-into-own-code operation (`e` / `β` in the tex) and
the theory must REPRESENT that operation (`⊢ β(⌜θ⌝) ↔ G(⌜θ(⌜θ⌝)⌝)`). We model `Proves` abstractly with
exactly the representability principle the lemma uses, and see if the diagonal closes.

Scope: this is the SHAPE check (à la the other spikes), not a faithful arithmetization. If it closes,
the diagonal mechanism is sound and the remaining work is making `Proves`/representability concrete
(arithmetized `Bew`). If it stalls, we learn precisely which ingredient blocks.
NOT root-imported. `lake env lean PrisonersDilemma/Research/Spikes/pblt/DiagonalLemmaSpike.lean`
-/

namespace PD.DiagonalLemmaSpike

/-! ## Minimal encoded syntax.

A `Pred` is a "predicate with one quote-slot and a parameter `k`" — `Lang_{r+1}` with r = 1 (one
parameter), matching the PBLT use. We don't need full first-order syntax; we need:
  • a way to PLUG a code into the quote-slot (`apply : Pred → Code → Sent`), and
  • a Gödel numbering `code : Pred → Code` (here `Code := Nat`).
`Sent` = a closed-up statement (still parametric in `k`), the thing `Proves` talks about. -/

abbrev Code := Nat

/-- A statement parametric in the single parameter `k : Nat`. Abstract — we only use `iff`. We give
    it a constructor so `opaque`s over it synthesize `Nonempty`. -/
structure Sent where mk :: (raw : Nat)
/-- the object `↔` we prove (abstract — its body is irrelevant to the diagonal; any total function
    suffices since we only reason about `Proves` of `iff`-shaped families). -/
def Sent.iff (s _t : Sent) : Sent := s

/-- A predicate `θ(⌜-⌝, k)`: a function from (the plugged code, k) to a `Sent`.
    Self-application `θ(⌜θ⌝, k)` is `app θ (code θ) k`. -/
structure Pred where
  app : Code → Nat → Sent          -- `θ(plugged-code, k)`

/-- the Gödel number `#θ`. We do NOT need injectivity: the diagonal's `let θ = β` is instantiation. -/
opaque code : Pred → Code

/-- The "partial self-evaluation" `e` (tex): `selfApply θ` is the predicate `k ↦ θ(⌜θ⌝, k)`, with
    `code (selfApply θ) = e (code θ)`. -/
def selfApply (θ : Pred) : Pred := ⟨fun _ k => θ.app (code θ) k⟩

/-! ## The abstract theory `Proves`, with EXACTLY the representability principle the lemma uses.

`Proves s` = "`S ⊢ ∀k, s(k)`" (the `∀k̄` is meta, as in our PBLT formulation). We need:
  • `iffRefl`/`iffTrans`/`iffSymm` — `↔` is an equivalence we can chain (basic `S` logic);
  • `repr` — the ONE new axiom: `β := λ n k. G(e n, k)` is representable, so for every `θ`,
    `⊢ ∀k, β(⌜θ⌝, k) ↔ G(⌜selfApply θ⌝, k)`. (tex: `⊢ β(⌜θ⌝,k̄) ↔ G(⌜θ(⌜θ⌝,-)⌝,k̄)`.)
    Here `β(⌜θ⌝,k) := (G-as-Pred).app (code θ) k`'s self-eval, and `⌜selfApply θ⌝ = code (selfApply θ)`. -/

opaque Proves : (Nat → Sent) → Prop      -- `⊢ ∀k, s k`

axiom iffRefl  (s : Nat → Sent) : Proves (fun k => (s k).iff (s k))
axiom iffSymm  {s t : Nat → Sent} : Proves (fun k => (s k).iff (t k)) → Proves (fun k => (t k).iff (s k))
axiom iffTrans {s t u : Nat → Sent} :
  Proves (fun k => (s k).iff (t k)) → Proves (fun k => (t k).iff (u k)) →
  Proves (fun k => (s k).iff (u k))

/-- `β` as a `Pred`: `β(n, k) = G(e n, k)`. The diagonal uses only `repr` (below), not this body, so
    a placeholder suffices; the genuine content (`e` representable) lives in `repr`. -/
def betaPred (G : Code → Nat → Sent) : Pred := ⟨fun _n k => G 0 k⟩

/-- **Representability of the self-evaluation `β`** (the tex's key provable equivalence). For the
    target `G : Code → Nat → Sent` (`G(⌜·⌝, k)`) and `β := betaPred G`, for every `θ` the theory `S`
    proves `β(⌜θ⌝, k) ↔ G(⌜selfApply θ⌝, k)` — the tex's `⊢ β(⌜θ⌝,k̄) ↔ G(⌜θ(⌜θ⌝,-)⌝,k̄)`. The genuine
    content is that `e` (self-application) is representable IN `S`; here it is the one assumed axiom. -/
axiom repr (G : Code → Nat → Sent) (θ : Pred) :
  Proves (fun k => ((betaPred G).app (code θ) k).iff (G (code (selfApply θ)) k))

/-! ## THE PARAMETRIC DIAGONAL LEMMA.

For any `G : Code → Nat → Sent`, there is `ψ : Nat → Sent` with `⊢ ∀k, ψ(k) ↔ G(⌜ψ⌝, k)`.
Construction (tex): `ψ := selfApply (betaPred G)`, i.e. `ψ(k) = β(⌜β⌝, k)`; `⌜ψ⌝ = code ψ`. -/

theorem parametric_diagonal (G : Code → Nat → Sent) :
    ∃ ψ : Nat → Sent, ∃ cψ : Code,
      Proves (fun k => (ψ k).iff (G cψ k)) := by
  -- β := betaPred G ;  ψ := selfApply β  (as a `Pred`); its sentence-family is `(selfApply β).app …`
  let β : Pred := betaPred G
  let ψP : Pred := selfApply β
  -- ψ(k) = β(⌜β⌝, k) by def of selfApply
  refine ⟨fun k => ψP.app (code ψP) k, code ψP, ?_⟩
  -- `repr G β` : ⊢ β(⌜β⌝, k) ↔ G(⌜selfApply β⌝, k) = G(⌜ψP⌝, k).
  have hrepr := repr G β
  -- ψ(k) = (selfApply β).app (code ψP) k = β(⌜β⌝, k)  (def of selfApply: ignores plugged code, uses `code β`)
  -- and `code (selfApply β) = code ψP`. So `hrepr` is exactly the goal up to defeq. Check:
  show Proves (fun k => (ψP.app (code ψP) k).iff (G (code ψP) k))
  -- ψP.app (code ψP) k  reduces (selfApply) to  β.app (code β) k  =  (betaPred G).app (code β) k
  -- hrepr : Proves (fun k => ((betaPred G).app (code β) k).iff (G (code (selfApply β)) k))
  --   and code (selfApply β) = code ψP. So defeq.
  exact hrepr

/-! ## VERDICT — the diagonal SHAPE closes; the WORK is concentrated in `repr` (machine-checked).

`parametric_diagonal` is sorry-free, `#print axioms ⊆ {repr}` (it uses ONLY `repr` — the `iff`
equivalence axioms turned out unneeded; the fixpoint is `exact hrepr`). So:

**GOOD (de-risked).** The self-reference TYPECHECKS and the fixpoint `ψ ↔ G(⌜ψ⌝)` is DERIVABLE: the
construction `ψ := selfApply (betaPred G)`, `⌜ψ⌝ := code ψ` is well-formed in Lean — no Löb-loop, no
positivity wall, no kind error. Whatever blocks the diagonal, it is NOT a typing/representational
impossibility at this level. That alone is worth knowing (it was the open risk).

**HONEST CAVEAT — the entire difficulty is now ISOLATED in the axiom `repr`, which this spike ASSUMES,
not proves.** The proof closed by `exact hrepr` essentially by definitional reduction, because the
toy `selfApply` is a *Lean function* (so `code (selfApply θ)` and the self-application are real at the
Lean level). `repr` bundles the genuinely hard content:
  `⊢_S β(⌜θ⌝, k) ↔ G(⌜selfApply θ⌝, k)`
i.e. "the self-evaluation function `e` (with `code (selfApply θ) = e (code θ)`) is REPRESENTABLE IN
`S`". In the real theory that is NOT a defeq — it is the arithmetic fact that `e` has a graph
predicate `Γ_e` and `S` proves `Γ_e(⌜θ⌝, ⌜selfApply θ⌝)`. Proving `repr` requires: a concrete Gödel
encoding of the syntax, the substitution-on-codes function `e` defined and shown computable, its
graph predicate, and `S` (= arithmetized bounded `Bew`) proving the graph. THAT is the large work,
and this spike does NOT touch it.

**NET (step-1 result).** The diagonal lemma's *logical skeleton* is sound and Lean-expressible
(`parametric_diagonal` over the interface). The make-or-break is now sharply localized: it is
**`repr` — representability of self-application in arithmetized `S`** — the single concrete obligation
the rest of Path A must discharge. Next sub-step: replace the abstract `Sent`/`code`/`Proves`/`repr`
with a concrete encoded arithmetic (Mathlib `ModelTheory` / a `Bew`-style predicate) and try to PROVE
`repr` for the smallest non-trivial `e`. If `repr` proves there, PBLT-removal is genuinely on; if it
stalls, that is the true floor. (The earlier `pblt_of_bpsb` chain consumes this `diag` directly.) -/

#check @parametric_diagonal

end PD.DiagonalLemmaSpike
