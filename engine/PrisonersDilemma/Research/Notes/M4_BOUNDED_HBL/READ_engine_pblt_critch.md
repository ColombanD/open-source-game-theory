# READ — the engine's Löb machinery and Critch's PBLT, verbatim (for the arithmetized M4 instance)

Read-only extraction, 2026-09-11, branch `colomban-arith-m3`. Every quoted block is
verbatim from the file named above it, with `file:line` ranges. Paragraphs marked
**ANALYSIS** are the reader's own; everything else is the source text.

Engine root: `engine/PrisonersDilemma/` (namespace `PD`; Löb material in
`PD.BaseTheorems`). Paper: `critch22.pdf` (41 PDF pages; page numbers below are PDF
page numbers, which coincide with the printed page numbers).

---

## 1. `Base/BoundedGL.lean` — the abstract interface, in full

### 1.1 The structure (`Base/BoundedGL.lean:93-143`)

```lean
/-- **Bounded GL, abstract**: budget-indexed modal schemes with explicit transcript costs,
    over an abstract sentence type. The `→/□/diag` fragment. Every field is the same-named
    `Pf` constructor of `ProofSystem.lean` with `Formula` replaced by `Sent` (binder shapes
    included — `mp`/`implTrans` carry an implicit output budget `{k}`, the rest an explicit
    `K`), so `pfBoundedGL` below is literally `mp := Pf.mp` etc. -/
structure BoundedGL (Sent : Type) where
  imp  : Sent → Sent → Sent
  box  : Nat → Sent → Sent
  diag : Nat → Sent → Sent
  size : Sent → Nat
  Proves : Nat → Sent → Prop
  /-- Budget monotonicity (`Pf_mono`). -/
  mono : ∀ {k₁ : Nat} {φ : Sent}, Proves k₁ φ → ∀ {k₂ : Nat}, k₁ ≤ k₂ → Proves k₂ φ
  /-- Modus ponens, transcript = both subtrees + conclusion (`Pf.mp`). -/
  mp : ∀ {k : Nat} (m₁ m₂ : Nat) (φ α : Sent),
    Proves m₁ (imp φ α) → Proves m₂ φ → m₁ + m₂ + size α ≤ k → Proves k α
  /-- Transitivity of implication (`Pf.implTrans`). -/
  implTrans : ∀ {k : Nat} (φ ψ χ : Sent) (a b : Nat),
    Proves a (imp φ ψ) → Proves b (imp ψ χ) → a + b + size (imp φ χ) ≤ k →
    Proves k (imp φ χ)
  /-- Closed S-composition (`Pf.impS2`). -/
  impS2 : ∀ (φ ψ χ : Sent) (m₁ m₂ K : Nat),
    Proves m₁ (imp φ (imp ψ χ)) → Proves m₂ (imp φ ψ) → m₁ + m₂ + size (imp φ χ) ≤ K →
    Proves K (imp φ χ)
  /-- Bounded necessitation, HBL D1 (`Pf.boxIntro`). -/
  boxIntro : ∀ (kIn K : Nat) (φ : Sent),
    Proves kIn φ → kIn + size (box kIn φ) ≤ K → Proves K (box kIn φ)
  /-- Bounded K-distribution as an object formula, HBL D2 (`Pf.axKf`). -/
  axKf : ∀ (a b c K : Nat) (φ α : Sent),
    a + b + size α ≤ c →
    size (imp (box a (imp φ α)) (imp (box b φ) (box c α))) ≤ K →
    Proves K (imp (box a (imp φ α)) (imp (box b φ) (box c α)))
  /-- Bounded 4 / object necessitation, HBL D3 (`Pf.box4`). -/
  box4 : ∀ (a b K : Nat) (φ : Sent),
    a + size (box a φ) ≤ b →
    size (imp (box a φ) (box b (box a φ))) ≤ K →
    Proves K (imp (box a φ) (box b (box a φ)))
  /-- Upward box-subscript monotonicity (`Pf.boxMono`). -/
  boxMono : ∀ (a b K : Nat) (φ : Sent),
    a ≤ b → size (imp (box a φ) (box b φ)) ≤ K → Proves K (imp (box a φ) (box b φ))
  /-- Löb-fixpoint leg, forward: `ψ → (□_g ψ → tgt)` for `ψ := diag g tgt`, GATED on a held
      Löb premise whose transcript it charges (`Pf.diagF`). -/
  diagF : ∀ (pm fb g K : Nat) (tgt : Sent),
    Proves pm (imp (box fb tgt) tgt) →
    pm + size (imp (diag g tgt) (imp (box g (diag g tgt)) tgt)) ≤ K →
    Proves K (imp (diag g tgt) (imp (box g (diag g tgt)) tgt))
  /-- Löb-fixpoint leg, backward: `(□_g ψ → tgt) → ψ` (`Pf.diagB`). -/
  diagB : ∀ (pm fb g K : Nat) (tgt : Sent),
    Proves pm (imp (box fb tgt) tgt) →
    pm + size (imp (imp (box g (diag g tgt)) tgt) (diag g tgt)) ≤ K →
    Proves K (imp (imp (box g (diag g tgt)) tgt) (diag g tgt))
```

Field-by-field cost table (read off the statement; `|·|` = `size`):

| field | premises | cost side-condition | conclusion |
|---|---|---|---|
| `mono` | `Proves k₁ φ` | `k₁ ≤ k₂` | `Proves k₂ φ` |
| `mp` | `Proves m₁ (φ→α)`, `Proves m₂ φ` | `m₁ + m₂ + |α| ≤ k` | `Proves k α` |
| `implTrans` | `Proves a (φ→ψ)`, `Proves b (ψ→χ)` | `a + b + |φ→χ| ≤ k` | `Proves k (φ→χ)` |
| `impS2` | `Proves m₁ (φ→(ψ→χ))`, `Proves m₂ (φ→ψ)` | `m₁ + m₂ + |φ→χ| ≤ K` | `Proves K (φ→χ)` |
| `boxIntro` (D1) | `Proves kIn φ` | `kIn + |□_kIn φ| ≤ K` | `Proves K (□_kIn φ)` |
| `axKf` (D2, object) | — | gate `a + b + |α| ≤ c`; `|□_a(φ→α) → (□_b φ → □_c α)| ≤ K` | `Proves K (□_a(φ→α) → (□_b φ → □_c α))` |
| `box4` (D3, object) | — | gate `a + |□_a φ| ≤ b`; `|□_a φ → □_b □_a φ| ≤ K` | `Proves K (□_a φ → □_b □_a φ)` |
| `boxMono` | — | `a ≤ b`; `|□_a φ → □_b φ| ≤ K` | `Proves K (□_a φ → □_b φ)` |
| `diagF` | `Proves pm (□_fb tgt → tgt)` (the GATE) | `pm + |ψ → (□_g ψ → tgt)| ≤ K`, `ψ := diag g tgt` | `Proves K (ψ → (□_g ψ → tgt))` |
| `diagB` | `Proves pm (□_fb tgt → tgt)` (the GATE) | `pm + |(□_g ψ → tgt) → ψ| ≤ K` | `Proves K ((□_g ψ → tgt) → ψ)` |

The header explains what is deliberately NOT a field (`Base/BoundedGL.lean:35-42`):

> **Field ↔ constructor** (`ProofSystem.lean`, family B glue and family C Löb machinery):
> `mono` = `Pf_mono`; `mp`/`implTrans`/`impS2` = `Pf.mp`/`Pf.implTrans`/`Pf.impS2`;
> `boxIntro` (HBL D1) / `axKf` (HBL D2, object form) / `box4` (HBL D3) / `boxMono` /
> `diagF` / `diagB` = the same-named `Pf` constructors. Deliberately EXCLUDED: `neg` and the
> propositional `contrapose`/`negElim`/`implK`/`implS`/`implRefl`/`weakenImpl` (unused by the
> three theorems), the rule-form `axK` (unused; `axKf` + `mp` up to slack), and EVERY
> source-reading rule (`atom`, `searchBranch`, `simStep`, …, `atomBoxImpl`) — the atom theory
> is the model-specific half of `S` and stays per-rule.

and why the diag legs are gated (`Base/BoundedGL.lean:44-51`):

> **The gate is kept.** `diagF`/`diagB` demand a HELD Löb premise `Proves pm (imp (box fb tgt)
> tgt)` and charge its transcript `pm`, unlike the textbook unconditional diagonal lemma.
> Three reasons: it is strictly WEAKER as a scheme, so any ungated model discharges it a
> fortiori (nothing is lost for a future arithmetized instance — state the ungated law, derive
> the gated one by monotonicity); the generic derivation always holds `hLoeb` when it takes a
> leg; and in the engine the gate is load-bearing for the exclusion censuses (`Base/Exclusion`
> reaches the tail invariant on a leg's conclusion through the induction hypothesis ON THE
> GATE PREMISE — an ungated leg would have no IH there).

and the one engine-specific commitment (`Base/BoundedGL.lean:53-61`):

> **`SizeExact` is the ONE engine-specific commitment.** `Formula.size`-shaped costs
> (`size (imp φ ψ) = |φ| + |ψ| + 1`, `size (box k φ) = numCost k + |φ| + 1`, same for
> `diag`). Only the asymptotic wrappers `pblt`/`pblt_bounded` consult it — their 21
> side-conditions are discharged by rewriting with these equations and `omega`. Inequality
> laws with additive slack do NOT suffice (`omega` cannot see through the nested
> `size (imp (diag g φ) …)` atoms; tested in the spike's design pass), and a Gödel-coded
> model (`box k φ := Bew_k(⌜φ⌝)`, size LINEAR in `|φ|` with a constant) would not satisfy
> even those — such a model gets `bloeb`/`mutual_loeb` for free and owes its own asymptotic
> wrapper. That is a v2 item, recorded in the design note.

The open obligation, in the file's own words (`Base/BoundedGL.lean:75-82`):

> THE OPEN OBLIGATION: an arithmetized model over PA (a
> budget-indexed provability predicate validating these ten schemes at these costs) — no
> costed derivability conditions are formalized in any prover; Foundation's
> `RestrictedProvability` (`∃ d < 2^e, Proof T d φ`, with the classical no-short-proof
> lower bound for its Gödel sentence) is the closest object and has none of the schemes.
> Its Solovay-style converse ("is this the complete logic of bounded provability?") is the
> precise form of the faithfulness question of the 2026-08-20 entry.

### 1.2 `SizeExact` (`Base/BoundedGL.lean:145-151`)

```lean
structure BoundedGL.SizeExact {Sent : Type} (B : BoundedGL Sent) : Prop where
  size_imp  : ∀ φ ψ, B.size (B.imp φ ψ) = B.size φ + B.size ψ + 1
  size_box  : ∀ k φ, B.size (B.box k φ) = numCost k + B.size φ + 1
  size_diag : ∀ g φ, B.size (B.diag g φ) = numCost g + B.size φ + 1
```

### 1.3 `pfBoundedGL` — which constructor discharges which field (`Base/BoundedGL.lean:153-173`)

```lean
def pfBoundedGL : BoundedGL Formula where
  imp := .impl
  box := .box
  diag := .diag
  size := Formula.size
  Proves := Pf
  mono := Pf_mono
  mp := Pf.mp
  implTrans := Pf.implTrans
  impS2 := Pf.impS2
  boxIntro := Pf.boxIntro
  axKf := Pf.axKf
  box4 := Pf.box4
  boxMono := Pf.boxMono
  diagF := Pf.diagF
  diagB := Pf.diagB

theorem pfBoundedGL_sizeExact : pfBoundedGL.SizeExact :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
```

### 1.4 `BoundedGL.mutual_loeb` (`Base/BoundedGL.lean:179-220`)

```lean
theorem mutual_loeb (A C : Sent) (kP kD fb n m c pA pB : Nat)
    (d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ K : Nat)
    (legPD : B.Proves pA (B.imp (B.box kP A) C))
    (legDP : B.Proves pB (B.imp (B.box kD C) A))
    (H1 : fb ≤ kP)
    (H2 : B.size (B.imp (B.box fb A) (B.box kP A)) ≤ d₁)
    (H3 : d₁ + pA + B.size (B.imp (B.box fb A) C) ≤ d₂)
    (H4 : d₂ ≤ n)
    (H5 : n + B.size (B.box n (B.imp (B.box fb A) C)) ≤ d₃)
    (H6 : n + m + B.size C ≤ c)
    (H7 : B.size (B.imp (B.box n (B.imp (B.box fb A) C))
            (B.imp (B.box m (B.box fb A)) (B.box c C))) ≤ d₄)
    (H8 : d₄ + d₃ + B.size (B.imp (B.box m (B.box fb A)) (B.box c C)) ≤ d₅)
    (H9 : fb + B.size (B.box fb A) ≤ m)
    (H10 : B.size (B.imp (B.box fb A) (B.box m (B.box fb A))) ≤ d₆)
    (H11 : d₆ + d₅ + B.size (B.imp (B.box fb A) (B.box c C)) ≤ d₇)
    (H12 : c ≤ kD)
    (H13 : B.size (B.imp (B.box c C) (B.box kD C)) ≤ d₈)
    (H14 : d₇ + d₈ + B.size (B.imp (B.box fb A) (B.box kD C)) ≤ d₉)
    (H15 : d₉ + pB + B.size (B.imp (B.box fb A) A) ≤ K) :
    B.Proves K (B.imp (B.box fb A) A) := by
  have s1 : B.Proves d₁ (B.imp (B.box fb A) (B.box kP A)) := B.boxMono fb kP d₁ A H1 H2
  have s2 : B.Proves d₂ (B.imp (B.box fb A) C) :=
    B.implTrans _ _ _ d₁ pA s1 legPD H3
  have s3 : B.Proves d₃ (B.box n (B.imp (B.box fb A) C)) :=
    B.boxIntro n d₃ _ (B.mono s2 H4) H5
  have s4 : B.Proves d₄ (B.imp (B.box n (B.imp (B.box fb A) C))
      (B.imp (B.box m (B.box fb A)) (B.box c C))) :=
    B.axKf n m c d₄ (B.box fb A) C H6 H7
  have s5 : B.Proves d₅ (B.imp (B.box m (B.box fb A)) (B.box c C)) :=
    B.mp d₄ d₃ _ _ s4 s3 H8
  have s6 : B.Proves d₆ (B.imp (B.box fb A) (B.box m (B.box fb A))) :=
    B.box4 fb m d₆ A H9 H10
  have s7 : B.Proves d₇ (B.imp (B.box fb A) (B.box c C)) :=
    B.implTrans _ _ _ d₆ d₅ s6 s5 H11
  have s8 : B.Proves d₈ (B.imp (B.box c C) (B.box kD C)) := B.boxMono c kD d₈ C H12 H13
  have s9 : B.Proves d₉ (B.imp (B.box fb A) (B.box kD C)) :=
    B.implTrans _ _ _ d₇ d₈ s7 s8 H14
  exact B.implTrans _ _ _ d₉ pB s9 legDP H15
```

**ANALYSIS — field order and budget flow of `mutual_loeb`.** Ten steps, fields in order:
`boxMono` (s1, lowers the antecedent subscript UP onto leg 1's literal `kP`) → `implTrans`
(s2: `□_fb A → C` at `d₂ = d₁ + pA + |□_fb A → C|`) → `mono`+`boxIntro` (s3: necessitate s2 at
subscript `n ≥ d₂`, cost `d₃ = n + |□_n(…)|`) → `axKf` (s4, K-instance landing at
`c ≥ n + m + |C|`) → `mp` (s5) → `box4` (s6: `□_fb A → □_m □_fb A`, gate `m ≥ fb + |□_fb A|`)
→ `implTrans` (s7) → `boxMono` (s8: `□_c C → □_kD C`, needs `c ≤ kD`) → `implTrans` (s9)
→ `implTrans` with leg 2 (final, `K = d₉ + pB + |□_fb A → A|`). The output subscript `fb` is
FREE and must satisfy `fb ≤ kP` and `fb + |□_fb A| + n + |C| ≤ c ≤ kD` — i.e. `fb` sits
strictly below both legs' literals by an `O(log k)`-sized gap (the consumers take
`fb = k − 64·V`, §2.3 below). Note the subscript `m` is only constrained by `H9`, and `c` by
`H6`/`H12`: the K-distribution's OUTPUT subscript `c` must fit under leg 2's box `kD` — this is
the "K-distribution pushes the intermediate subscript above `k`" wall the Loeb.lean header
describes, resolved by lowering `fb`.

### 1.5 `BoundedGL.bloeb` (`Base/BoundedGL.lean:222-285`)

```lean
/-- **Bounded Löb, generic** — `Base/Loeb.bloeb_engine` against the interface: the 14-step
    internalized GL derivation from the tight premise `□_fb φ → φ`, fixpoint at the free
    subscript `g` (`H19 : c₁₃ ≤ g` absorbs the fixpoint's whole transcript). Uses only
    `diagF/diagB/boxIntro/axKf/box4/boxMono/implTrans/impS2/mp/mono` — no size law. -/
theorem bloeb (φ : Sent) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ K : Nat)
    (hLoeb : B.Proves pm (B.imp (B.box fb φ) φ))
    (H1 : pm + B.size (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)) ≤ c₁)
    (H2 : pm + B.size (B.imp (B.imp (B.box g (B.diag g φ)) φ) (B.diag g φ)) ≤ c₂)
    (H3 : c₁ ≤ n₁)
    (H4 : n₁ + B.size (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ))) ≤ c₃)
    (H5 : n₁ + g + B.size (B.imp (B.box g (B.diag g φ)) φ) ≤ n₃)
    (H6 : B.size (B.imp (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)))
            (B.imp (B.box g (B.diag g φ)) (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ)))) ≤ c₄)
    (H7 : c₄ + c₃ + B.size (B.imp (B.box g (B.diag g φ))
            (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))) ≤ c₅)
    (H8 : n₃ + n₄ + B.size φ ≤ n₅)
    (H9 : B.size (B.imp (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))
            (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) ≤ c₆)
    (H10 : g + B.size (B.box g (B.diag g φ)) ≤ n₄)
    (H11 : B.size (B.imp (B.box g (B.diag g φ)) (B.box n₄ (B.box g (B.diag g φ)))) ≤ c₇)
    (H12 : c₅ + c₆ + B.size (B.imp (B.box g (B.diag g φ))
            (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) ≤ c₈)
    (H13 : c₈ + c₇ + B.size (B.imp (B.box g (B.diag g φ)) (B.box n₅ φ)) ≤ c₉)
    (H14 : n₅ ≤ fb)
    (H15 : B.size (B.imp (B.box n₅ φ) (B.box fb φ)) ≤ c₁₀)
    (H16 : c₉ + c₁₀ + B.size (B.imp (B.box g (B.diag g φ)) (B.box fb φ)) ≤ c₁₁)
    (H17 : c₁₁ + pm + B.size (B.imp (B.box g (B.diag g φ)) φ) ≤ c₁₂)
    (H18 : c₂ + c₁₂ + B.size (B.diag g φ) ≤ c₁₃)
    (H19 : c₁₃ ≤ g)
    (H20 : g + B.size (B.box g (B.diag g φ)) ≤ c₁₄)
    (H21 : c₁₂ + c₁₄ + B.size φ ≤ K) :
    B.Proves K φ := by
  have legF : B.Proves c₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)) :=
    B.diagF pm fb g c₁ φ hLoeb H1
  have legB : B.Proves c₂ (B.imp (B.imp (B.box g (B.diag g φ)) φ) (B.diag g φ)) :=
    B.diagB pm fb g c₂ φ hLoeb H2
  have hnec : B.Proves c₃ (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ))) :=
    B.boxIntro n₁ c₃ _ (B.mono legF H3) H4
  have hK1 : B.Proves c₄ (B.imp (B.box n₁ (B.imp (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ)))
      (B.imp (B.box g (B.diag g φ)) (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ)))) :=
    B.axKf n₁ g n₃ c₄ (B.diag g φ) (B.imp (B.box g (B.diag g φ)) φ) H5 H6
  have h2 : B.Proves c₅ (B.imp (B.box g (B.diag g φ)) (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))) :=
    B.mp c₄ c₃ _ _ hK1 hnec H7
  have hK2 : B.Proves c₆ (B.imp (B.box n₃ (B.imp (B.box g (B.diag g φ)) φ))
      (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) :=
    B.axKf n₃ n₄ n₅ c₆ (B.box g (B.diag g φ)) φ H8 H9
  have hfour : B.Proves c₇ (B.imp (B.box g (B.diag g φ)) (B.box n₄ (B.box g (B.diag g φ)))) :=
    B.box4 g n₄ c₇ (B.diag g φ) H10 H11
  have h4 : B.Proves c₈ (B.imp (B.box g (B.diag g φ))
      (B.imp (B.box n₄ (B.box g (B.diag g φ))) (B.box n₅ φ))) :=
    B.implTrans _ _ _ c₅ c₆ h2 hK2 H12
  have h6 : B.Proves c₉ (B.imp (B.box g (B.diag g φ)) (B.box n₅ φ)) :=
    B.impS2 _ _ _ c₈ c₇ c₉ h4 hfour H13
  have hmono : B.Proves c₁₀ (B.imp (B.box n₅ φ) (B.box fb φ)) :=
    B.boxMono n₅ fb c₁₀ φ H14 H15
  have h6' : B.Proves c₁₁ (B.imp (B.box g (B.diag g φ)) (B.box fb φ)) :=
    B.implTrans _ _ _ c₉ c₁₀ h6 hmono H16
  have hE : B.Proves c₁₂ (B.imp (B.box g (B.diag g φ)) φ) :=
    B.implTrans _ _ _ c₁₁ pm h6' hLoeb H17
  have hF : B.Proves c₁₃ (B.diag g φ) := B.mp c₂ c₁₂ _ _ legB hE H18
  have hG : B.Proves c₁₄ (B.box g (B.diag g φ)) :=
    B.boxIntro g c₁₄ _ (B.mono hF H19) H20
  exact B.mp c₁₂ c₁₄ _ _ hE hG H21
```

**ANALYSIS — the 14 steps of `bloeb`, with the field used, its gate, and its transcript.**
Write `ψ := diag g φ` (the fixpoint sentence, at box subscript `g`).

| step | field | conclusion | transcript | gate / consumed hypothesis |
|---|---|---|---|---|
| legF | `diagF` | `ψ → (□_g ψ → φ)` | `c₁ ≥ pm + |…|` (H1) | held `hLoeb` at `pm` |
| legB | `diagB` | `(□_g ψ → φ) → ψ` | `c₂ ≥ pm + |…|` (H2) | held `hLoeb` at `pm` |
| hnec | `mono` + `boxIntro` | `□_{n₁}(ψ → (□_g ψ → φ))` | `c₃ ≥ n₁ + |□_{n₁}(…)|` (H4) | `c₁ ≤ n₁` (H3) |
| hK1 | `axKf n₁ g n₃` | `□_{n₁}(ψ→(□_gψ→φ)) → (□_g ψ → □_{n₃}(□_gψ→φ))` | `c₄ ≥ |instance|` (H6) | `n₁ + g + |□_gψ→φ| ≤ n₃` (H5) |
| h2 | `mp` | `□_g ψ → □_{n₃}(□_g ψ → φ)` | `c₅ ≥ c₄ + c₃ + |…|` (H7) | — |
| hK2 | `axKf n₃ n₄ n₅` | `□_{n₃}(□_gψ→φ) → (□_{n₄}□_gψ → □_{n₅} φ)` | `c₆ ≥ |instance|` (H9) | `n₃ + n₄ + |φ| ≤ n₅` (H8) |
| hfour | `box4 g n₄` | `□_g ψ → □_{n₄} □_g ψ` | `c₇ ≥ |instance|` (H11) | `g + |□_g ψ| ≤ n₄` (H10) |
| h4 | `implTrans` | `□_g ψ → (□_{n₄}□_gψ → □_{n₅} φ)` | `c₈ ≥ c₅ + c₆ + |…|` (H12) | — |
| h6 | `impS2` | `□_g ψ → □_{n₅} φ` | `c₉ ≥ c₈ + c₇ + |…|` (H13) | — |
| hmono | `boxMono n₅ fb` | `□_{n₅} φ → □_fb φ` | `c₁₀ ≥ |instance|` (H15) | `n₅ ≤ fb` (H14) — THE master constraint |
| h6' | `implTrans` | `□_g ψ → □_fb φ` | `c₁₁ ≥ c₉ + c₁₀ + |…|` (H16) | — |
| hE | `implTrans` with `hLoeb` | `□_g ψ → φ` | `c₁₂ ≥ c₁₁ + pm + |□_gψ→φ|` (H17) | — |
| hF | `mp` (legB, hE) | `ψ` | `c₁₃ ≥ c₂ + c₁₂ + |ψ|` (H18) | — |
| hG | `mono` + `boxIntro g` | `□_g ψ` | `c₁₄ ≥ g + |□_g ψ|` (H20) | `c₁₃ ≤ g` (H19) — fixpoint absorbs its own proof |
| final | `mp` (hE, hG) | `φ` | `K ≥ c₁₂ + c₁₄ + |φ|` (H21) | — |

Two things this table makes explicit for the arithmetized instance:
1. There are FOUR box subscripts besides the source literal `fb`: the fixpoint subscript `g`
   (must dominate the fixpoint's whole transcript, `H19`), and the three K-stage subscripts
   `n₁ < n₃`, `n₄`, `n₅` with `n₁ + g + |□_gψ→φ| ≤ n₃`, `g + |□_gψ| ≤ n₄`,
   `n₃ + n₄ + |φ| ≤ n₅ ≤ fb`. So `fb` must exceed roughly `4·g + O(|φ| + log)`. The chain is
   "Critch's `g ≺ f` dance" (`Base/Loeb.lean:89`).
2. `hLoeb` is consumed THREE times (legF, legB, hE) and its transcript `pm` is charged each
   time — whence "do NOT weaken `pm` up to `k`" (`Base/Loeb.lean:85-87`).

### 1.6 `BoundedGL.pblt` and `pblt_bounded` (`Base/BoundedGL.lean:287-327`)

```lean
/-- **Parametric bounded Löb (PBLT), generic** — `Base/Loeb.pblt_engine` against the
    interface. The only place the size laws enter: the 21 side-conditions of `bloeb` are
    discharged by rewriting with `hS` and `omega`. -/
theorem pblt (hS : B.SizeExact) (φ : Nat → Sent) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → B.Proves (pm k) (B.imp (B.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + B.size (φ k) + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, B.Proves m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + B.size (φ k) + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, B.bloeb (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [hS.size_imp, hS.size_box, hS.size_diag, numCost]); omega

/-- **PBLT, budget-carrying, generic** — `Base/Loeb.pblt_engine_bounded`. -/
theorem pblt_bounded (hS : B.SizeExact) (φ : Nat → Sent) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → B.Proves (pm k) (B.imp (B.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + B.size (φ k) + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ f k ∧ B.Proves m (φ k) := by
  [identical instantiation; the extra `by omega` discharges `2 * (4096 * W) ≤ f k`]
```

**ANALYSIS — the PBLT instantiation, decoded.** With the unit
`W := pm k + |φ k| + log₂(f k) + 8`, `bloeb`'s parameters are (matching the positional
argument list `(φ) (pm fb g n₁ n₃ n₄ n₅) (c₁ … c₁₄ K)`):

| parameter | value | | parameter | value |
|---|---|---|---|---|
| `pm` | `pm k` | | `c₁, c₂` | `16W, 16W` |
| `fb` | `f k` | | `c₃` | `64W` |
| `g` (fixpoint subscript) | `1024W` | | `c₄, c₅` | `32W, 128W` |
| `n₁` | `32W` | | `c₆, c₇` | `32W, 16W` |
| `n₃` | `2048W` | | `c₈, c₉` | `256W, 512W` |
| `n₄` | `2048W` | | `c₁₀, c₁₁` | `16W, 640W` |
| `n₅` | `8192W` | | `c₁₂, c₁₃` | `704W, 768W` |
| `K` (the output `m`) | `4096W` | | `c₁₄` | `2048W` |

The binding constraints are `H14 : n₅ = 8192W ≤ f k` (exactly `hsz`), `H19 : c₁₃ = 768W ≤ g =
1024W`, `H8 : 2048W + 2048W + |φ| ≤ 8192W`, `H5 : 32W + 1024W + |□_gψ → φ| ≤ 2048W`,
`H10 : 1024W + |□_g ψ| ≤ 2048W`. Every numeral in the chain is `≤ 8192W ≤ f k`, so its
`numCost` is `≤ log₂(f k) + 1 ≤ W` — that is the role of the four `log2_mono` facts. The
resulting budget is **`m = 4096·W = 4096·(pm k + |φ k| + log₂(f k) + 8) ≤ f(k)/2`**. The
condition `hsz` is the engine's concrete form of Critch's `f(k) ≻ O(lg k)`: since `pm k` and
`|φ k|` are themselves `O(log k)` for every zoo bot (`pblt_engine_id`'s `100·log₂k + 1000`
envelopes, §2.2), `hsz` reads `f(k) ≥ C·log₂ k + D` for constants `C, D` — `f = id` satisfies
it eventually by `linear_log2_add_le` (`Base/Asymptotics.lean:77`).

### 1.7 The instances (`Base/BoundedGL.lean:331-341`)

```lean
example : @mutual_loeb = pfBoundedGL.mutual_loeb := rfl
example : @bloeb_engine = pfBoundedGL.bloeb := rfl
example : @pblt_engine = pfBoundedGL.pblt pfBoundedGL_sizeExact := rfl
example : @pblt_engine_bounded = pfBoundedGL.pblt_bounded pfBoundedGL_sizeExact := rfl
```

---

## 2. `Base/Loeb.lean` — the engine's own Löb chain

### 2.1 `mutual_loeb` and `bloeb_engine` (`Base/Loeb.lean:34-54`, `94-122`)

Statements are the `Pf`/`Formula` specializations of §1.4/§1.5, binder for binder (the `rfl`
examples in §1.7 prove that). Header commentary that fixes the cost discipline:

`Base/Loeb.lean:17-27`:
> `mutual_loeb` derives a closed Löb premise from the two object transparency legs
> (`legPD : □_kP A → B`, `legDP : □_kD B → A`). TRANSCRIPT-COST SHAPE (T0 §6,
> `Research/Spikes/transcript/T0Transcript.lean`): the conclusion lives at a LOWERED box
> subscript `fb` (strictly below the legs' source literals) — `□_fb A → □_kP A` feeds leg 1
> via upward `boxMono`, the K-distribution lands at `c ≤ kD` which mono-UPs onto leg 2's box,
> yielding `□_fb A → A` with an O(log k) transcript. `bloeb_engine`/`pblt_engine` then consume
> the premise at `fb`. (The former same-subscript factoring `□_k φP → φP` is UNDERIVABLE under
> transcript cost: K-distribution pushes the intermediate subscript above `k`, and downward
> box-mono is unsound.)

`Base/Loeb.lean:82-92`:
> `bloeb_engine` runs Löb's derivation entirely in `Pf` from the TIGHT premise
> `Pf pm (□_fb φ → φ)` — `pm` is the premise's honest transcript (O(log k) for the
> consumers' single-leaf `searchBranch` / `mutual_loeb` premises; do NOT weaken it up to `k`,
> the chain needs `pm ≪ fb`). The fixpoint sentence `ψ := .diag g φ` lives at the FREE subscript
> `g ≺ fb`: under transcript cost ψ's derivation CONTAINS the premise's derivation, so `□`-ing ψ needs
> `g` to absorb ψ's whole transcript (`H19 : c₁₃ ≤ g`) — Critch's `g ≺ f` dance, validated in
> `Research/Spikes/transcript/T0Transcript.lean` (`bloeb_transcript`, axiom-free). The step
> transcripts `c₁…c₁₄` and the box stages `n₁ n₃ n₄ n₅` are explicit; `pblt_engine` instantiates
> everything as multiples of ONE O(log k) unit and discharges the 21 side-conditions by omega.

The inline step comments in the `Pf` version (`Base/Loeb.lean:123-165`) name the steps:
`legF`/`legB` "(gated on hLoeb, charging its transcript)", `hnec : □_{n₁}(ψ → (□_gψ→φ))`,
`hK1 … [axKf stage 1]`, `h2 : □_g ψ → □_{n₃} ctx`, `hK2 … [axKf stage 2]`,
`hfour : □_g ψ → □_{n₄} □_g ψ`, `h4`, `h6 … [impS2 — S-composition]`,
`hmono … [upward boxMono — new with the transcript model]`, `h6' : □_g ψ → □_{fb} φ`,
`hE : □_g ψ → φ`, `hF : ψ  (contains legB + hE — hence the premise's transcript; H19 : c₁₃ ≤ g
absorbs it)`, `hG`, final `mp`.

### 2.2 The PBLT wrappers (`Base/Loeb.lean:167-259`)

```lean
theorem pblt_engine (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k)                                   -- :172-175

theorem pblt_engine_bounded (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ f k ∧ Pf m (φ k)                     -- :199-202

theorem pblt_engine_id_bounded (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ k ∧ Pf m (φ k)                       -- :219-223

theorem pblt_engine_id (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k)                                   -- :242-246
```

Docstrings (`Base/Loeb.lean:167-171`, `192-198`, `237-241`):
> **Parametric bounded Löb, INTERNAL** — the `PBLT` conclusion as a THEOREM, transcript-cost.
> Premise at its HONEST transcript `pm k` (O(log k) for all consumers — do not weaken to `f k`);
> ONE master headroom bound `8192·(pm k + (φ k).size + log2 (f k) + 8) ≤ f k` instantiates the
> whole chain as multiples of the unit `W := pm + |φ| + log2 (f k) + 8` (T0's assignment:
> `g = 1024·W` absorbs the fixpoint's proof, the largest stage is `n₅ = 8192·W ≤ f k`).

> **PBLT, budget-carrying**: identical to `pblt_engine`, but it also reports that
> the fixpoint's transcript fits in HALF the budget. The engine picks
> `m = 4096·W` while its own size hypothesis forces `8192·W ≤ f k`, so this costs
> nothing extra — it just stops throwing the bound away.
> Needed whenever a Löb bit has to be RE-CERTIFIED at budget `k` (a `proofSearch k`
> gate), rather than merely consumed as an `∃ m` play witness.

> **Consumer-facing PBLT** (`f = id`, the shape every bot theorem uses): tight Löb premise at
> its honest transcript `pm k` (what the `*_loeb_premise` lemmas produce — a single
> transparency leaf, `O(log k)` characters) + generous uniform `10·log2 k + 100` bounds on
> both the play-atom family and the premise transcript (covers every bot in the zoo).
> Replaces the former `PBLT` axiom at all call sites.

The `_id` master bound (`Base/Loeb.lean:247-248`):
> -- master bound: 8192·((100L+1000) + (100L+1000) + L + 8) = 1646592·L + 16449536 ≤ k, eventually.
> obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le 1646592 16449536

### 2.3 The mutual engines (`Base/Loeb.lean:261-362`)

```lean
/-- **Consumer-facing MUTUAL PBLT** (`f = id`): the cross-bot cooperation closer
    (PrudentBot↔DupocBot, JustBot legs, …). Takes the two transparency legs at their honest
    O(log k) transcripts and SAME-`k` source literals, derives the lowered premise via
    `mutual_loeb` (`fb = k − 64·V`), and runs `bloeb_engine` at `fb`. Validated in
    `T0Transcript.lean` §6 (`mutual_pblt_transcript`). -/
theorem mutual_pblt_engine_id (Af Bf : Nat → Formula) (p₁ p₂ : Nat → Nat) (k₁ : Nat)
    (hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000)
    (hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000)
    (hp1 : ∀ k, p₁ k ≤ 100 * Nat.log2 k + 1000)
    (hp2 : ∀ k, p₂ k ≤ 100 * Nat.log2 k + 1000)
    (hL1 : ∀ k, k > k₁ → Pf (p₁ k) (.impl (.box k (Af k)) (Bf k)))
    (hL2 : ∀ k, k > k₁ → Pf (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (Af k) := by                              -- :266-273
  -- master headroom: 131072·V ≤ k with V ≤ 401·log2 k + 4016.
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (131072 * 401) (131072 * 4016)
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  …
  -- the lowered premise subscript: fb + 64V = k
  obtain ⟨fb, hfb⟩ : ∃ fb, 64 * V + fb = k := Nat.le.dest (by omega)
  …
  -- the lowered Löb premise (mutual_loeb): Pf (160V) (□_fb Af → Af)
  have s10 : Pf (160*V) (.impl (.box fb (Af k)) (Af k)) := by
    refine mutual_loeb (Af k) (Bf k) k k fb (16*V) (fb + 8*V) (fb + 32*V) (p₁ k) (p₂ k)
      (8*V) (16*V) (32*V) (16*V) (64*V) (16*V) (96*V) (8*V) (128*V) (160*V)
      (hL1 k hkk₁) (hL2 k hkk₁)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  -- single-leg bloeb at fb
  refine ⟨32768*V, bloeb_engine (Af k) (160*V) fb
    (8192*V) (512*V) (16384*V) (16384*V) (65536*V)
    (256*V) (256*V) (1024*V) (512*V) (2048*V) (512*V) (512*V)
    (3072*V) (4096*V) (256*V) (5120*V) (6144*V) (7168*V) (16384*V) (32768*V)
    s10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [numCost, Formula.size]); omega                          -- :274-310

/-- **Consumer-facing MUTUAL PBLT, STAGGERED** (T3.2b): the cross-bot closer for pairs whose
    legs live at DIFFERENT source budgets — leg 1's box at `kP k ≥ k` (the bigger bot, e.g.
    `PrudentBot (2k+64)`, whose prudence pays the partner's `search_f` floor), leg 2's at `k`.
    The internal chain is unchanged (`fb = k − 64·V ≤ k ≤ kP k` mono-UPs onto leg 1; the
    K-distribution lands at `fb + 32V ≤ k` onto leg 2); `hkPlog` absorbs the bigger numeral. -/
theorem mutual_pblt_engine_staggered (Af Bf : Nat → Formula) (kP : Nat → Nat)
    (p₁ p₂ : Nat → Nat) (k₁ : Nat)
    (hkP : ∀ k, k ≤ kP k)
    (hkPlog : ∀ k, Nat.log2 (kP k) ≤ Nat.log2 k + 8)
    (hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000)
    (hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000)
    (hp1 : ∀ k, p₁ k ≤ 100 * Nat.log2 k + 1000)
    (hp2 : ∀ k, p₂ k ≤ 100 * Nat.log2 k + 1000)
    (hL1 : ∀ k, k > k₁ → Pf (p₁ k) (.impl (.box (kP k) (Af k)) (Bf k)))
    (hL2 : ∀ k, k > k₁ → Pf (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (Af k)                                    -- :317-327
  [same body with `mutual_loeb (Af k) (Bf k) (kP k) k fb …` at :352]
```

**ANALYSIS — the mutual instantiation, decoded.** Unit `V := p₁ k + p₂ k + |Af k| + |Bf k| +
log₂ k + 16`; headroom `131072·V ≤ k`. `mutual_loeb` gets `kP = kD = k` (or `kP k`, `k`),
`fb = k − 64V`, `n = 16V`, `m = fb + 8V`, `c = fb + 32V` (so `c ≤ kD = k` holds with `32V` to
spare), step transcripts `d₁…d₉ = 8V,16V,32V,16V,64V,16V,96V,8V,128V`, output `K = 160V`.
Then `bloeb_engine` at `pm = 160V`, `fb = k − 64V`, `g = 8192V`, `n₁ = 512V`, `n₃ = n₄ = 16384V`,
`n₅ = 65536V` (needs `65536V ≤ fb = k − 64V`, i.e. `65600V ≤ k`), output `m = 32768V`. The
"V" instantiation is the "W" instantiation scaled by 8, because the premise transcript `pm =
160V` is itself a multiple of the unit rather than a summand of it.

### 2.4 The fixpoint sentence `Formula.diag` and the size/cost laws

`Program.lean:84-91` (the `Formula` inductive, inside the `Prog`/`Formula` mutual block):
```lean
  inductive Formula: Type where
    | plays : Prog → Prog → Action → Formula      -- atomic: "p(q.source) == a"
    | impl  : Formula → Formula → Formula         -- φ → ψ (needed for Löb-style hypotheses like □C → C)
    | neg   : Formula → Formula                   -- ¬ φ
    | box   : Nat → Formula → Formula             -- □_n φ: "S derives φ at budget n" (⊢_n φ; its interp is `Pf n φ`)
    | eq    : Prog → Prog → Formula               -- structural identity: "p and q are the same program". The 2nd arg is a frozen literal target (subst does not descend into it); the 1st is the probe (typically `.opp`), which subst resolves to the concrete player.
    | diag  : Nat → Formula → Formula             -- the Löb-fixpoint sentence for target `tgt` at box budget `g`: ψ with ψ ↔ (□_g ψ → tgt). Its meaning (Dynamics.interp) is the fixpoint BY DESIGN — same pattern as `.box` meaning `Pf`; the meta-justification that a faithful arithmetization contains such a sentence is the Reflection layer's DERIVED diagonal (Research/Notes/INTERNALIZATION_ROADMAP.md, I0). Never appears in bot source; used only by the meta Löb chain (bounded Löb / PBLT).
end
```

`Formula.subst` freezes it (`Program.lean`, the `Formula.subst` arm):
```lean
    | .diag g φ,    _, _ => .diag g φ             -- FROZEN (like `.bot`/`.eq`-RHS): the diagonal is a closed meta-construction; subst does not descend
```

`Program.lean:206-215` (numeral cost) and `246-252` (`Formula.size`):
```lean
-- Syntactic size = character count of source. This is the unit the proof system
-- measures budgets in: `□_k φ` means "φ has an `S`-derivation of ≤ k characters", and a
-- derivation's length is bounded in terms of the sizes of the formulas it manipulates.
-- A numeral `k` costs `Nat.log2 k + 1` characters (critch22 Appendix B(b):
-- numbers are written in `O(lg k)` characters), so e.g. `.search`/`.box` pay that
-- for their index. Everything else is `(sum of children) + 1` for the node.
/-- The character cost of writing the numeral `k` (Critch Appendix B(b): numbers are
    written in `O(lg k)` characters). Single source of truth for `Prog.size`,
    `Formula.size` and the proof-step cost `c_guard`. -/
def numCost (k : Nat) : Nat := Nat.log2 k + 1
```
```lean
  def Formula.size : Formula → Nat
    | .plays p q _ => p.size + q.size + 1
    | .impl φ ψ    => φ.size + ψ.size + 1
    | .neg φ       => φ.size + 1
    | .box k φ     => numCost k + φ.size + 1
    | .eq p q      => p.size + q.size + 1
    | .diag g φ    => numCost g + φ.size + 1   -- numeral cost for `g`, like `.box`
```

`Program.lean:217-231` (`Prog.size`, the arms a Löb cell touches):
```lean
  def Prog.size : Prog → Nat
    | .const _        => 1
    | .self           => 1
    | .opp            => 1
    | .bot p          => p.size + 1
    | .sim p q        => p.size + q.size + 1
    | .ite b _ p q    => b.size + p.size + q.size + 1
    | .search k φ p q => numCost k + φ.size + p.size + q.size + 1
    | .tvote v θ p q      => numCost θ + v.vsize + p.size + q.size + 1
    | .sys defs i     => defs.psize + numCost i + 1
    | .selfIdx j      => numCost j + 1
```

`ProofSystem.lean:66-72` (the per-step costs) and `:964-967` (`atom_cost`):
```lean
-- 1. Per-step proof-encoding costs (Critch's `e*`, Appendix B(d)): the character cost
-- of transcribing one `eval` step. Concrete, every step ≥ 1 character, so a fuel-`n`
-- certificate has ≤ `n` steps — what makes the decision procedure terminate.
-- `c_guard k = numCost k` is the `O(lg k)` cost of writing the budget numeral `k`.
def c_leaf  : Nat := 1                          -- leaf step (`.const a`)
def c_node  : Nat := 1                          -- structural step (`.self`/`.opp`/`.bot`/`.sim`/`.ite`)
def c_guard (k : Nat) : Nat := numCost k        -- `.search` guard at budget `k`; grows with `k`
```
```lean
/-- 7. Character budget for a `fuel`-step play's atom certificate. Honest `O(fuel)`
    (Critch's `e*`, Appendix B(d)): `c_node + c_guard fuel` per step, plus a leaf.
    `c_guard fuel` over-approximates every guard budget reachable in the run. -/
def atom_cost (fuel : Nat) : Nat := c_leaf + (c_node + c_guard fuel) * fuel
```

Concrete sizes the Löb cells rely on (from `Theorems/DupocBot/Helpers.lean:411-418`):
> The `searchBranch` derivation concluding
> `□_k (DUPOC plays C vs DUPOC) → (DUPOC plays C vs DUPOC)` is a single leaf whose
> transcript is exactly its conclusion: `5 * log2 k + 33` characters (`DupocBot k` is
> structurally identical to `CupodBot k`, so each costs `log2 k + 7`).

**ANALYSIS (size arithmetic check).** `DupocBot k = .search k (.plays .opp .self C) (.const C)
(.const D)` has size `numCost k + (1+1+1) + 1 + 1 + 1 = log₂k + 7`. So `φ k = .plays (Dupoc k)
(Dupoc k) C` has size `2(log₂k+7)+1 = 2·log₂k + 15`; `□_k (φ k)` has size `(log₂k+1) +
(2log₂k+15) + 1 = 3log₂k + 17`; the leg `□_k φ → φ` has size `(3log₂k+17) + (2log₂k+15) + 1 =
5·log₂k + 33`. The four asymptotic helpers used everywhere: `linear_log2_add_le (A B) : ∃ K,
∀ k ≥ K, A * Nat.log2 k + B ≤ k` (`Base/Asymptotics.lean:77`), `log2_mono` (`:95`),
`log2_le_self` (`:100`), `log2_stagger_le : Nat.log2 (2 * k + 64) ≤ Nat.log2 k + 8` (`:105`).

---

## 3. `ProofSystem.lean` — the constructors, verbatim

The cost doctrine (`ProofSystem.lean:283-286`):
> **Cost model**: every rule's side-condition bounds the CUMULATIVE transcript — leaves pay their
> conclusion's `Formula.size`; combining rules pay both subtrees PLUS their own conclusion. A bounded
> budget therefore genuinely bounds the premise formulas too (the paid-cut property that makes bounded
> search finite).

### 3.1 The execution bridge: `PlaysProof.search_t`/`search_f`, `AtomProvable.mk`, `Pf.atom`

`ProofSystem.lean:188-208`:
```lean
    /-- `.search k φ p q` runs the TRUE-guard branch (`p`) when `S` derives the guard (`⊢_k guard`), so
        `search_t` carries `Pf k (guard)` as its premise. **This is the back-edge that makes the
        block mutual**: execution consults the proof system. -/
    | search_t :
        Pf k (φ.subst me opponent) →
        PlaysProof me opponent p a n →
        PlaysProof me opponent (.search k φ p q) a (n + c_guard k + c_node)
    /-- FALSE-guard branch: `.search k φ p q` runs the else branch when the guard search
        fails. Two design points, both forced:
        * the premise is a Σ₁ REFUTATION `Pf m (.neg guard)`, certifiable from the guard
          subject's actual play (`Pf.atomNeg`) — never mere unprovability `¬ ⊢_k guard` (premising on
          unprovability is a non-monotone fixpoint; the anti-diagonal bot is its paradox);
        * the cost pays the FULL failed budget `k`, the floor: an else-certificate must
          never fit within the budget whose failure it certifies, or `atom_monotone`
          would lift it back and re-fire the guard (a machine-checked inconsistency).
          The floor is also what lets soundness be proven by budget induction.
        Faithful: a PA-style proof that a bounded search fails checks every candidate. -/
    | search_f :
        Pf m (.neg (φ.subst me opponent)) →
        PlaysProof me opponent q a n →
        PlaysProof me opponent (.search k φ p q) a (n + m + k + c_node)
```

`ProofSystem.lean:271-274` and `:291`:
```lean
-- 3. `AtomProvable k φ` — a `PlaysProof` whose run cost fits the budget (`n ≤ k`); the bridge for
-- atomic `.plays` facts (which the reasoning rules cannot read).
  inductive AtomProvable : Nat → Formula → Prop where
    | mk : PlaysProof me opponent me a n → n ≤ k → AtomProvable k (.plays me opponent a)
```
```lean
    | atom : AtomProvable k φ → Pf k φ
```

**ANALYSIS.** Note `search_t` CITES a fired guard at `c_guard k = log₂k + 1` — it does not
re-include the guard's proof. That is the engine's version of Critch's Appendix B(c)
(abbreviations / lemma citation) and is what makes a Löb-fired atom certificate cost
`c_leaf + c_guard k + c_node = log₂k + 3 ≤ k` (the `hGA`/`hGJ`/`hpsD` steps in §4).

### 3.2 The reading rules used by the Löb cells

`ProofSystem.lean:301-305` (`searchBranch`), `:320-325` (`botSearchStep`), `:379-389`
(`searchThenSearch_t`):
```lean
    /-- S can read a `.search` body: a successful guard makes `me` play `a`. -/
    | searchBranch (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .search g ψ (.const a) (.const b)) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
```
```lean
    /-- The `.bot (.search …)` twin of `searchBranch`, sound as `botSimStep` is. Needed
        when a searcher appears `.bot`-wrapped as a PLAYER whose source S must read. -/
    | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        Pf k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
```
```lean
    /-- Stacked `.search` (Critch's PrudentBot shape): `me` plays `c0` when both guards
        hold. Primitive — the then-branch is a `.search`, not a `.const` — and carrying
        the inner proof as a premise collapses the two guards to the single-box
        conclusion `□_{k₁} ψ₁' → me plays c0` the bounded-Löb engine consumes. -/
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        Pf m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        Pf k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
```

### 3.3 Family B glue used by the chain

`ProofSystem.lean:421-428`, `:434-438`:
```lean
    /-- Modus ponens. Transcript: both subtrees plus the conclusion. -/
    | mp (m₁ m₂ : Nat) (φ α : Formula) :
        Pf m₁ (.impl φ α) → Pf m₂ φ → m₁ + m₂ + α.size ≤ k → Pf k α
    /-- Transitivity of implication. Primitive: with no implication introduction, `S`
        cannot derive it from `mp`. -/
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        Pf a (.impl φ ψ) → Pf b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k → Pf k (.impl φ χ)
```
```lean
    /-- Closed composition: from `⊢_{m₁} φ → (ψ → χ)` and `⊢_{m₂} φ → ψ`, infer `⊢_K φ → χ`. The
        rule form suffices because both premises are closed. -/
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        Pf m₁ (.impl φ (.impl ψ χ)) → Pf m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → Pf K (.impl φ χ)
```

### 3.4 Family C — the Löb machinery (`ProofSystem.lean:466-516`)

```lean
    -- ═══ Family C. LÖB MACHINERY — modal / HBL tier (bounded derivability conditions) ═══
    /-- Bounded necessitation (HBL D2): from `⊢_{kIn} φ`, `S` derives `□_{kIn} φ` (at `K`).
        Sound with no axiom — `⊨ □_{kIn} φ` IS `⊢_{kIn} φ` (`Pf kIn φ`). -/
    | boxIntro (kIn K : Nat) (φ : Formula) :
        Pf kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        Pf K (.box kIn φ)
    /-- Bounded Σ₁-completeness for play-atoms, certificate-carrying: it fires only when a
        size-≤-`kBox` transcript exists, which keeps it on the sound Σ₁ side (not the
        GL-excluded converse necessitation). -/
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvable kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        Pf k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    /-- GL axiom K, rule form: from `⊢_m □_a (φ → α)`, infer `⊢_K □_b φ → □_c α`. -/
    | axK (a b c m K : Nat) (φ α : Formula) :
        Pf m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        Pf K (.impl (.box b φ) (.box c α))
    /-- GL axiom K as an object formula — Löb's middle step needs it premise-free. -/
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        Pf K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    /-- GL axiom 4 / object necessitation, `□_a φ → □_b (□_a φ)`. Its interp is the
        identity `Pf a φ → Pf a φ`. -/
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        Pf K (.impl (.box a φ) (.box b (.box a φ)))
    /-- Upward box-subscript monotonicity, `□_a φ → □_b φ` for `a ≤ b`: the transcript
        model lands K-distribution outputs at computed subscripts that must be weakened up
        onto the consumers' source-literal boxes. -/
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        Pf K (.impl (.box a φ) (.box b φ))
    /-- Löb-fixpoint leg, forward: `ψ → (□_g ψ → tgt)` for `ψ := .diag g tgt`. Sound with
        no axiom (`ψ.interp` IS `Pf g ψ → tgt.interp`). Gated on the Löb premise
        `Pf pm (□_fb tgt → tgt)`, which the Löb chain always has and which preserves the
        exclusion invariants. -/
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        Pf pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        Pf K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    /-- Löb-fixpoint leg, backward: `(□_g ψ → tgt) → ψ`. Sound as `diagF`. -/
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        Pf pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        Pf K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
```

(Note the docstring of `boxIntro` says "HBL D2" while `BoundedGL.lean:117` calls the same
field "HBL D1"; the BoundedGL file's numbering — D1 = necessitation, D2 = K-distribution,
D3 = 4 — is the one used in this note.)

### 3.5 Monotonicity, the oracle, and semantics

`ProofSystem.lean:887-896`:
```lean
/-- A ≤k₁-transcript proof is a ≤k₂-transcript proof (`k₁ ≤ k₂`). Structural under the transcript
    cost model: EVERY rule's final side-condition is `… ≤ k` with `k` the output budget, so each
    constructor re-applies with the bound relaxed — plain `cases`, no recursion. -/
…
theorem Pf_mono : ∀ {k₁ : Nat} {φ : Formula}, Pf k₁ φ →
    ∀ {k₂ : Nat}, k₁ ≤ k₂ → Pf k₂ φ := by
```
`ProofSystem.lean:960-962`:
```lean
-- 6. The proof-search oracle: bounded `S`-provability (`⊢_k φ`) reflected into `Bool` for the
-- evaluator's guard. Classical (hence noncomputable), correct for an oracle.
noncomputable def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Pf k φ)
```
`Base/AtomCerts.lean:187-189`:
```lean
theorem proofSearch_spec (k : Nat) (φ : Formula) :
    proofSearch k φ = true ↔ Pf k φ := by
  unfold proofSearch; exact decide_eq_true_iff
```
`Base/Soundness.lean:103-106`, `:143-144`, `:179-181`:
```lean
theorem sound_upto : ∀ B : Nat,
    (∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
      ∃ N, eval N me opponent body = some a)
    ∧ (∀ k φ, Pf k φ → k ≤ B → φ.interp) := by
```
```lean
theorem Pf_sound : ∀ k φ, Pf k φ → φ.interp :=
  fun k φ h => (sound_upto k).2 k φ h le_rfl
```
```lean
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp :=
  fun k φ hk => Pf_sound k φ ((proofSearch_spec k φ).1 hk)
```

`Dynamics.lean:148-162` (the semantics — `.box` and `.diag` clauses):
```lean
-- Denotational semantics: maps a syntactic `Formula` to a Lean proposition
-- (truth, written `⊨ φ`). `.plays` is fuel-existential so theorems need not commit to a
-- budget; the box clause is `Pf n φ` (`⊨ □_n φ` IS `⊢_n φ` — the proof system's own
-- provability, not a separate oracle).
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => Pf n φ
  | .eq p q      => p = q
  | .diag g φ    => Pf g (.diag g φ) → φ.interp
  -- `.diag g φ` IS the Löb-fixpoint sentence for target `φ` at box budget `g`: its meaning is
  -- `interp (□_g (.diag g φ) → φ)` BY DEFINITION (legal: recursion descends only into `φ`; `Pf`
  -- does not recurse through `interp`). Same design pattern as `.box n φ ↦ Pf n φ`; the
  -- meta-justification is the Reflection layer's DERIVED diagonal (INTERNALIZATION_ROADMAP.md I0).
```
`Dynamics.lean:34-37` (the evaluator's search arm) and `:140-146`:
```lean
    | .search k φ p q =>
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q
```
```lean
noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)
```

**ANALYSIS.** In the engine, `□_n φ` and `diag g φ` are CONNECTIVES whose truth is DEFINED as
`Pf n φ` and as the fixpoint; nothing is coded. That is why `boxIntro`, `box4`, `diagF`,
`diagB` are "sound with no axiom" (`boxIntro`: `⊨ □_kIn φ` IS the premise; `box4`'s interp
is the identity `Pf a φ → Pf a φ`; the diag legs' interp is the fixpoint by definition). The
arithmetized instance has to EARN each of these as PA theorems about a coded predicate.

---

## 4. The Löbian outcome theorems

### 4.1 The statement template (`Outcome/Spec.lean:52-67`)

```lean
abbrev OutcomeAt (pad : Nat) (L R : Prog) (r : Option Outcome) : Prop :=
  ∀ fuel, outcome (fuel + pad) L R = r

abbrev OutcomeSpec (b : BudgetRegime) (pad : Nat)
    (L R : Nat → Prog) (r : Option Outcome) : Prop :=
  match b with
  | .nobudget  => OutcomeAt pad (L 0) (R 0) r
  | .universal => ∀ k, OutcomeAt pad (L k) (R k) r
  | .eventual  => ∃ k₂, ∀ k, k₂ < k → OutcomeAt pad (L k) (R k) r
```
with `BudgetRegime` (`Outcome/Spec.lean:25-32`): `nobudget | universal | eventual`
("Holds at every SUFFICIENTLY LARGE budget: `∃ k₂, ∀ k > k₂`"). The docstring at `:34-51`
explains why the Löbian cells carry a literal pad:
> `Formula.interp` reads `.plays p q a` as `∃ n, play n p q = some a`, so a
> play obtained from `Pf_sound` comes with an unbounded fuel — but that witness never
> needs bounding: fuel is consumed per program node while the budget `k` is a numeral
> inside `.search`, so every zoo match is DETERMINED at a structural pad independent of
> `k`, and fuel determinism pins the value there (`Base/Helpers.outcome_at_of_ex`,
> `play_at_of_ex`, with the totality lemmas `play_search_const_total`,
> `play_ite_total`, `play_sim_opp_self_total`). The Löbian cells carry pads 2–6 like
> every other cell.

### 4.2 `Base/Helpers.lean` — `play_at_of_ex`, `outcome_at_of_ex`, totality

`Base/Helpers.lean:116-145`:
```lean
/-- **From an existential fuel witness to the cofinite form at a pad.** … -/
theorem play_at_of_ex {p q : Prog} {a : Action} {pad : Nat}
    (hex : ∃ n, play n p q = some a) (htot : ∃ b, play pad p q = some b) :
    ∀ fuel, play (fuel + pad) p q = some a := by
  obtain ⟨n, hn⟩ := hex
  obtain ⟨b, hb⟩ := htot
  obtain rfl : b = a := play_unique hb hn
  intro fuel
  exact PD.BaseTheorems.eval_mono_le hb _ (Nat.le_add_left _ _)

/-- `play_at_of_ex` at the `outcome` level. -/
theorem outcome_at_of_ex {p q : Prog} {r : Outcome} {pad : Nat}
    (hex : ∃ n, outcome n p q = some r) (htot : ∃ r', outcome pad p q = some r') :
    ∀ fuel, outcome (fuel + pad) p q = some r := by
  obtain ⟨n, hn⟩ := hex
  obtain ⟨r', hr⟩ := htot
  have h1 := outcome_mono_le hn (max n pad) (Nat.le_max_left _ _)
  have h2 := outcome_mono_le hr (max n pad) (Nat.le_max_right _ _)
  rw [h1] at h2
  obtain rfl : r' = r := (Option.some.inj h2).symm
  intro fuel
  exact outcome_mono_le hr _ (Nat.le_add_left _ _)
```
`Base/Helpers.lean:147-155`:
```lean
/-- A one-guard searcher with constant leaves is determined at fuel 2 against ANY
    opponent, whichever way the oracle decides — the totality fact `play_at_of_ex`
    needs for `DupocBot`/`CupodBot`-shaped bots. -/
theorem play_search_const_total (k : Nat) (φ : Formula) (a b : Action) (opp : Prog)
    (fuel : Nat) :
    ∃ c, play (fuel + 2) (.search k φ (.const a) (.const b)) opp = some c := by
```
Also `play_unique` (`:109-114`, fuel determinism), `outcome_mono_le` (`:93-105`),
`outcome_of_plays` (`:222-226`), `outcome_total_of_plays` (`:159-164`).

### 4.3 The bots

`Bots/DupocBot.lean:6-11`:
```lean
-- Defect unless proof of opponent cooperating is found within k steps.
def DupocBot (k : Nat) : Prog :=
  .search k
    (.plays .opp .self Action.C)
    (.const Action.C)
    (.const Action.D)
```
`Bots/LlmGenerations/PrudentBot.lean:15-22`:
```lean
def PrudentBot (k : Nat) : Prog :=
  .search k
    (.plays .opp .self Action.C)        -- can I prove opp cooperates with me?
    (.search k                          -- ...if so, also check opp is not a sucker
      (.plays .opp (.bot DefectBot) Action.D)  -- can I prove opp defects vs DefectBot?
      (.const Action.C)                 -- both proven → cooperate
      (.const Action.D))                -- opp is exploitable → defect
    (.const Action.D)                   -- can't prove opp cooperates → defect
```
`Bots/LlmGenerations/JustBot.lean:17-21`:
```lean
def JustBot (k : Nat) : Prog :=
  .search k
    (.plays .opp (.bot (DupocBot k)) Action.C)
    (.const Action.C)
    (.const Action.D)
```

### 4.4 `Theorems/DupocBot/vs_DupocBot.lean` — self-cooperation, IN FULL (`:1-48`)

```lean
import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DUPOC self-play cooperates, for `k` large enough — critch22 Theorem 3.7.
    Direct application of PBLT with `φ k = .plays (DupocBot k) (DupocBot k) .C`,
    `f = id`, `k₁ = 0`. The Löb premise comes from `dupoc_loeb_premise`,
    soundness collapses bounded provability to a `play` witness, and self-play
    symmetry makes the same `play` discharge both legs of `outcome`. -/
@[outcome]
theorem outcome_DupocBot_vs_DupocBot :
    OutcomeSpec .eventual 2 DupocBot DupocBot (some (.C, .C)) := by
  let φ : Nat → Formula := fun k => .plays (DupocBot k) (DupocBot k) .C
  -- `dupoc_loeb_premise` supplies the S-derivation of the premise at its HONEST transcript,
  -- `⊢_{5·log2 k + 33} (□_k φ → φ)` —
  -- exactly `pblt_engine_id`'s premise shape (the Löb chain needs `pm ≪ k`).
  have hLoeb :
      ∀ k, k > 0 →
        Pf (5 * Nat.log2 k + 33) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact dupoc_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (DupocBot k) (DupocBot k) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpm : ∀ k, 5 * Nat.log2 k + 33 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 5 * Nat.log2 k + 33) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk fuel => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  -- Soundness yields the play at SOME fuel; the match is determined at fuel 2 whatever
  -- the oracle says, so determinism pins the value there and monotonicity does the rest.
  have hex : ∃ n, play n (DupocBot k) (DupocBot k) = some .C := Pf_sound m (φ k) hm
  have htot : ∃ b, play 2 (DupocBot k) (DupocBot k) = some b :=
    play_search_const_total k _ _ _ _ 0
  have hC : play (fuel + 2) (DupocBot k) (DupocBot k) = some .C := play_at_of_ex hex htot fuel
  exact outcome_of_plays _ _ _ _ _ hC hC

end PD.Theorems
```

The Löb premise it consumes (`Theorems/DupocBot/Helpers.lean:423-429`):
```lean
theorem dupoc_loeb_premise (k : Nat) :
    Pf (5 * Nat.log2 k + 33)
      (.impl (.box k (.plays (DupocBot k) (DupocBot k) .C))
             (.plays (DupocBot k) (DupocBot k) .C)) := by
  refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (DupocBot k) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
  omega
```

**ANALYSIS — the statement and the "fits its own budget" step.** Regime `.eventual`, pad `2`:
`∃ k₂, ∀ k > k₂, ∀ fuel, outcome (fuel+2) (DupocBot k) (DupocBot k) = some (C, C)`. Löb theorem
invoked: `pblt_engine_id` (`f = id`, `k₁ = 0`) with `φ k := plays (Dupoc k) (Dupoc k) C` and
premise transcript `pm k = 5·log₂k + 33` (one `searchBranch` leaf). It yields `∃ m, Pf m (φ k)`
with (by the `_bounded` twin, not used here) `2m ≤ k`. **The engine does NOT discharge "fits
inside k" explicitly in this cell**: it applies `Pf_sound m (φ k) hm` to get the TRUE play
`∃ n, play n (Dupoc k) (Dupoc k) = some C` — and since Dupoc plays `C` only if its guard fired,
the fit is implicit in soundness (`sound_upto` proves the `.plays` interp from the certificate,
and a `Pf m (φ k)` with `m ≤ k/2` gives `Pf k (φ k)` by `Pf_mono`, hence `proofSearch k (φ k) =
true`, hence the `C` branch). Then `play_search_const_total` (determined at fuel 2 either way)
+ `play_at_of_ex` (fuel determinism) pin `C` at every `fuel + 2`. Where a cell needs the fit
EXPLICITLY (a guard re-certified at `k`), it uses the `search_t`-cite certificate — see
`hGA`/`hGJ` in §4.6 and `hpsD` in §4.5 — or `pblt_engine_id_bounded`.

### 4.5 `Theorems/PrudentBot/vs_DupocBot.lean` — the staggered mutual-Löb companion

The two legs (`:156-181`):
```lean
/-- Leg 1 (staggered): `□_{2k+64} φD → φP` — `PrudentBot (2k+64)`'s stacked-search read;
    the inner prudence premise `prudence_dupoc` fits its literal (`k + log2 k + 15 ≤ 2k+64`),
    and the rule CITES the inner search (`c_guard`), keeping the leg's transcript O(log k). -/
theorem prudent_dupoc_legPD (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box (2*k+64) (.plays (DupocBot k) (PrudentBot (2*k+64)) .C))
             (.plays (PrudentBot (2*k+64)) (DupocBot k) .C)) := by
  have hlk := log2_le_self k
  have hlg := log2_stagger_le k
  refine Pf.searchThenSearch_t (2*k+64) (2*k+64) (k + Nat.log2 k + 15)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (PrudentBot (2*k+64)) (DupocBot k) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_dupoc k) (by omega) ?_
  simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, DupocBot, PrudentBot,
    DefectBot, c_guard]
  omega

/-- Leg 2 (staggered): `□_k φP → φD` — `DupocBot k`'s `searchBranch` leaf. -/
theorem prudent_dupoc_legDP (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (PrudentBot (2*k+64)) (DupocBot k) .C))
             (.plays (DupocBot k) (PrudentBot (2*k+64)) .C)) := by
  have hlg := log2_stagger_le k
  refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (PrudentBot (2*k+64)) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, PrudentBot, DefectBot]
  omega
```
The prudence certificate the inner search needs (`:141-154`), at the `search_f` floor:
```lean
theorem prudence_dupoc (k : Nat) :
    Pf (k + Nat.log2 k + 15) (.plays (DupocBot k) (.bot DefectBot) .D) := by
  have hneg : Pf (Nat.log2 k + 13)
      (.neg (.plays (.bot DefectBot) (DupocBot k) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (DupocBot k) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [numCost, Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_top k (Nat.log2 k + 13) (.plays .opp .self .C) .C .D
    (.bot DefectBot) hneg
  exact Pf.atom (atom_monotone _ _ _ (by omega) hcert)
```
The theorem and its Löb invocation (`:210-271`):
```lean
/-- **PrudentBot (2k+64) vs DupocBot k → (C, C)** for all large enough `k` — cooperation
    returns at a budget STAGGER (Prudent's extra budget pays Dupoc's `search_f` floor).
    Not the matrix cell (the cell is the shared-budget value, `outcome_PrudentBot_vs_DupocBot
    = (D, D)` below); kept as the staggered companion, `_staggered` keeps it out of the
    census. -/
@[outcome_companion]
theorem outcome_PrudentBot_vs_DupocBot_staggered :
    OutcomeSpec .eventual 4
      (fun k => PrudentBot (2*k+64)) DupocBot (some (.C, .C)) := by
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  have hsD : ∀ k, (Formula.plays (DupocBot k) (PrudentBot (2*k+64)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by …
  have hsP : ∀ k, (Formula.plays (PrudentBot (2*k+64)) (DupocBot k) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by …
  have hpb : ∀ k, 30 * Nat.log2 k + 700 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_staggered
    (fun k => Formula.plays (DupocBot k) (PrudentBot (2*k+64)) .C)
    (fun k => Formula.plays (PrudentBot (2*k+64)) (DupocBot k) .C)
    (fun k => 2*k+64)
    (fun k => 30 * Nat.log2 k + 700) (fun k => 30 * Nat.log2 k + 700) 0
    (fun k => by show k ≤ 2*k+64; omega) log2_stagger_le hsD hsP hpb hpb
    (fun k _ => prudent_dupoc_legPD k)
    (fun k _ => prudent_dupoc_legDP k)
  refine ⟨max k₂ KL, fun k hk fuel => ?_⟩
  …
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hplayD⟩ := Pf_sound m _ hm
  -- Dupoc's guard fired (inversion from its actual cooperative play)
  have hpsP : proofSearch k (.plays (PrudentBot (2*k+64)) (DupocBot k) .C) = true :=
    ps_k_of_play_dupoc_any k n (PrudentBot (2*k+64)) hplayD
  -- Dupoc's play atom, certified through its fired search (search_t cites)
  have hpsD : proofSearch (2*k+64)
      (.plays (DupocBot k) (PrudentBot (2*k+64)) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hpsP) PlaysProof.const, ?_⟩ :
        AtomProvable (2*k+64) (.plays (DupocBot k) (PrudentBot (2*k+64)) .C)))
    show c_leaf + c_guard k + c_node ≤ 2*k+64
    …
  -- Prudent's inner prudence guard at its own (bigger) literal
  have hprud : proofSearch (2*k+64) (.plays (DupocBot k) (.bot DefectBot) .D) = true := by
    refine (proofSearch_spec _ _).2 (Pf_mono (prudence_dupoc k) ?_)
    …
  refine outcome_mono_le (N := 4) ?_ (fuel + 4) (by omega)
  have hA : play 4 (PrudentBot (2*k+64)) (DupocBot k) = some .C := by
    simpa using prudent_eval_both_true (2*k+64) 1 (DupocBot k) hpsD hprud
  have hB : play 4 (DupocBot k) (PrudentBot (2*k+64)) = some .C := by
    simpa using dupoc_C_vs_any k 2 (PrudentBot (2*k+64)) hpsP
  exact outcome_of_plays _ _ _ _ _ hA hB
```
The same-budget CELL (`:324-333`) is `(D, D)`:
```lean
@[outcome]
theorem outcome_PrudentBot_vs_DupocBot :
    OutcomeSpec .universal 3 PrudentBot DupocBot (some (.D, .D)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (PrudentBot_plays_D_against_DupocBot_samek k fuel)
    (by simpa [Nat.add_assoc] using DupocBot_plays_D_against_PrudentBot_samek k (fuel + 1))
```
and the file records why (`:116-128`, `:133-139`): PrudentBot's prudence fact "DupocBot k defects
vs `.bot DefectBot`" is an ELSE-play of Dupoc's search, priced at the `search_f` floor `k +
log₂k + 15`, unpayable inside a same-`k` inner search — "the bounded analogue of MIRI
PrudentBot's PA+1 prudence".

**ANALYSIS.** The Löb structure: `A := plays (Dupoc k) (Prudent(2k+64)) C`, `B := plays
(Prudent(2k+64)) (Dupoc k) C`, legs `□_{2k+64} A → B` (via `searchThenSearch_t`, whose inner
premise `prudence_dupoc k` at `k + log₂k + 15 ≤ 2k+64` is CITED at `c_guard (2k+64)`) and
`□_k B → A` (`searchBranch`). `mutual_pblt_engine_staggered` gives `∃ m, Pf m A`. Then
soundness → true play of Dupoc (`hplayD`) → inversion `ps_k_of_play_dupoc_any` gives
`proofSearch k B = true` (Dupoc's guard fired) → `hpsD` re-certifies `A` at `2k+64` by a
`search_t`-cite at cost `c_leaf + c_guard k + c_node` — an EXPLICIT fit — → both plays at fuel 4.

### 4.6 `Theorems/JustBot/vs_DupocBot.lean` — statement + Löb invocation (`:19-58`)

```lean
@[outcome]
theorem outcome_JustBot_vs_DupocBot :
    OutcomeSpec .eventual 2
      JustBot DupocBot (some (.C, .C)) := by
  let φ : Nat → Formula :=
    fun k => Formula.plays (DupocBot k) (.bot (DupocBot k)) .C
-- The two transparency legs, transcript-tight; `mutual_pblt_engine_id` lowers the premise
  -- subscript internally and runs the Löb chain (the old same-subscript `mutual_loeb`
  -- factoring is underivable under transcript cost).
  have legPD : ∀ k, Pf (30 * Nat.log2 k + 300)
      (.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
             (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)) := by
    intro k
    refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (DupocBot k) rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
    omega
  have legDP : ∀ k, Pf (30 * Nat.log2 k + 300)
      (.impl (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
             (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) := by
    intro k
    refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (.bot (DupocBot k)) rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
    omega
  …
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_id φ
    (fun k => Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
    (fun k => 30 * Nat.log2 k + 300) (fun k => 30 * Nat.log2 k + 300) 0
    hφsz hsB hpb hpb (fun k _ => legPD k) (fun k _ => legDP k)
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  refine ⟨max k₂ KL, fun k hk fuel => outcome_at_of_ex ?_ ?_ fuel⟩
```
and the explicit fit (`:96-104`, then `:109-117` identically for JustBot's own guard):
```lean
    have hGA : proofSearch k
        (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C) = true := by
      -- hand certificate: Dupoc's search FIRED (hBtrue) — search_t ∘ const
      refine (proofSearch_spec _ _).2 (Pf.atom
        (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hBtrue) PlaysProof.const, ?_⟩ :
          AtomProvable k (.plays (DupocBot k) (.bot (DupocBot k)) .C)))
      show c_leaf + c_guard k + c_node ≤ k
      simp only [numCost, c_leaf, c_guard, c_node]
      omega
```

**ANALYSIS.** JustBot itself is not a Löb participant; the Löb pair is Dupoc k vs its own
FROZEN copy `.bot (Dupoc k)` (legs `botSearchStep`/`searchBranch`, same `k`), closed by
`mutual_pblt_engine_id`. The `.bot` barrier is what makes the two sides different formulas
(so `mutual`, not single-leg, Löb). The fit `c_leaf + c_guard k + c_node = log₂k + 3 ≤ k` is
discharged with `linear_log2_add_le 1 3` (giving `KL` with `log₂k + 3 ≤ k` for `k ≥ KL`).

---

## 5. Critch 2022 (`critch22.pdf`) — verbatim extracts

Text extracted with `pypdf` (pdftoppm is not installed); ligatures/spacing normalized only
where the extraction split words. Page numbers are the printed ones (= PDF page index).

### 5.1 The agents (pp. 9–10)

p. 9:
> The following class of agents are called CUPOD for "Cooperate Unless Proof
> of Defection", defined by a function CUPOD that constructs an agent CUPOD(k)
> for each k ≥ 0. Specifically, CUPOD(k) is a particular agent that behaves as
> follows: CUPOD(k)(opp_source) searches for a proof, in k characters or less,
> that the opponent opp is going to defect against CUPOD(k). If a proof of
> defection is found, CUPOD(k) defects; otherwise it "gives the benefit of the
> doubt" to its opponent and cooperates:
> ```
> # "Cooperate Unless Proof Of Defection" (CUPOD):
> def CUPOD(k):
>   def CUPOD_k(opp_source):
>     if proof_search(k, opp_source, "opp(CUPOD_k.source) == D"):
>       return D
>     else:
>       return C
>   CUPOD_k.source = ... # the last 5 lines with k filled in
>   return CUPOD_k
> ```
> Next we have DUPOC, for "Defect Unless Proof of Cooperation", the mirror
> image of CUPOD. DUPOC(k) will defect unless it finds affirmative proof, in k
> characters or less, that its opponent is going to cooperate:
> ```
> # "Defect Unless Proof Of Cooperation" (DUPOC):
> def DUPOC(k):
> ```
p. 10:
> ```
>   def DUPOC_k(opp_source):
>     if proof_search(k, opp_source, "opp(DUPOC_k.source) == C"):
>       return C
>     else:
>       return D
>   DUPOC_k.source = ... # the last 5 lines with k filled in
>   return DUPOC_k
> ```

p. 9, the search procedure:
> ```
> # proof_search checks each generated proof string to see
> # if it encodes a valid proof of a given hypothesis:
> def proof_search(length_bound, opp_source, hypothesis):
>   for proof in string_generator(length_bound):
>     if proof_checker(opp_source, proof, hypothesis):
>       return True
>   # otherwise, if no valid proof of hypothesis is found:
>   return False
> ```

**ANALYSIS (naming).** Critch 2022 has no agent called "FairBot"; DUPOC is the bounded
analogue of FairBot (LaVictoire et al. 2014, cited as [47]), and the engine's `DupocBot`
is its transcription. PrudentBot appears in this paper ONLY as an open problem (p. 26,
below); the engine's `PrudentBot` is the bounded transcription of LaVictoire et al.'s.

### 5.2 Notation 3.5 (p. 13)

> **Notation 3.5** (S, ⊢, □, and ≻).
> • S stands for the formal proof system being used by the agents; see
>   Appendix B for more details about it.
> • ⊢ xyz... means "the statement 'xyz...' can be proved using the proof
>   system S.
> • □_k(xyz...) means "a natural number exists which, taken as a string,
>   encodes a proof of xyz..., and that proof when written in the proof
>   language of S requires at most k characters of text."
> • f(k) ≻ O(lg k) means there is some positive constant c > 0 and some
>   threshold k̂ such that for all k > k̂, f(k) > c lg k.

### 5.3 Lemma 3.6 — PBLT, statement and proof (p. 13)

> **Lemma 3.6** (PBLT: Parametric Bounded Löb Theorem). Let p[k]
> be a formula with a single unquantified variable k in the proof language of
> the a proof system S, satisfying the conditions in Appendix B. Suppose that
> k₁ ∈ ℕ and f : ℕ → ℕ is an increasing computable function satisfying
> f(k) ≻ O(lg k), and S can verify that the formula p[k] is "potentially self-
> fulfilling for large k" in the sense that
>
>   ⊢ (∀k > k₁) ( □_{f(k)}(p[k]) → p[k] ).
>
> Then there is some threshold k₂ ∈ ℕ such that
>
>   ⊢ (∀k > k₂)(p[k]).
>
> *Proof of Lemma 3.6.* This is a special case of Critch [18, Theorem 4.2] where
> the proof expansion function e(k) is in O(k). Specifically, in this paper we
> have assumed (see Appendix B) that a proof can be expanded and checked
> in time linear in the length of the proof, i.e., e(k) = e* · k for some constant
> e*. This assumption makes the condition f(k) ≻ O(lg k) sufficient to apply
> Critch [18, Theorem 4.2], as described by Critch [18, Section 4.2].

(Reference [18] is Critch, *A parametric, resource-bounded generalization of Löb's theorem,
and a robust cooperation criterion for open-source game theory*, JSL 2019 — NOT in this PDF;
its Theorem 4.2 is the general-`e(k)` PBLT and its Definition 4.1 the "proof expansion
function".)

### 5.4 Theorems 3.4 and 3.7 and their proofs (pp. 13–14)

p. 13:
> **Theorem 3.4.** For k large, outcome(CUPOD(k),CUPOD(k)) == (D,D).
> …
> *Proof of Theorem 3.4.* This follows directly from PBLT, via the substitutions
> p[k]=(CUPOD(k)(CUPOD(k).source) == D), f(k) = k, and k₁ = 0.

p. 14:
> **Theorem 3.7.** For k large, outcome(DUPOC(k),DUPOC(k)) == (C,C).
> *Proof.* This follows directly from PBLT, via the substitutions
> p[k] = ((DUPOC(k)(DUPOC(k).source) == C), f(k) = k, and k₁ = 0.

### 5.5 The proof sketch, §3.4 (pp. 14–15)

p. 14:
> A key feature of the proof of Löb's theorem, and PBLT which underlies
> Theorems 3.4 and 3.7, is the ability to a construct a statement that in some
> sense refers to itself. This self-reference ability allows the proof to avoid the
> stack overflow problem one might otherwise expect. In broad brushstrokes,
> the proof of PBLT follows a similar structure to the classical modal proof
> of Löb's theorem [22], which can be summarized in words for the case of
> Theorem 3.7 as follows:
> 1. We construct a sentence Ψ that says "If this sentence is verified, then
>    the agents will cooperate," using a theorem in logic called the modal
>    fixed point theorem.
> 2. We show that if Ψ can be verified by the agents, then mutual cooper-
>    ation can also be verified by the agents, without using any facts about
>    the agents' strategies other than their ability to find proofs of a certain
>    length.

p. 15:
> 3. We use the fact that verifying mutual cooperation causes the agents to
>    cooperate, to show that Ψ is true.
> 4. Finally, we use the above proof of Ψ to construct a formal verification
>    of Ψ, which implies (by Ψ!) that cooperation occurs.
> …
> **Definition 3.8.** Let S be the formal (proof) system used by proof_checker.
> ⊢ X means "the proof system S can prove X", and □X means "a natural
> number exists which encodes (via a Gödel encoding) a proof of X within the
> proof language and rules of S.".
> **Open Problem 1.** Löb's theorem states that ⊢ (□C → C) implies
> ⊢ (C). We conjecture that Löb's Theorem can be proven without the
> use of the modal fixed point Ψ ↔ (□Ψ → C), by constructing an entire
> proof that refers to itself …

**ANALYSIS (map to the engine).** Step 1 = `diag g φ` with `diagF`/`diagB` (the modal fixed
point `Ψ ↔ (□_g Ψ → φ)`); step 2 = `hnec`…`h6'` (`□_g Ψ → □_fb φ`, using only `boxIntro`,
`axKf`×2, `box4`, `boxMono` — "no facts about the strategies"); step 3 = `hE` then `hF`
(`Ψ` itself, using the Löb premise `hLoeb`, the ONE strategy fact); step 4 = `hG` (`□_g Ψ`,
needing `c₁₃ ≤ g`) and the final `mp` (`φ`).

### 5.6 The cross-agent (mutual) uses of PBLT (pp. 21–24)

p. 21, Theorem 5.2(a) (CIMCIC self-play):
> **Theorem 5.2.** For large k,
> a) outcome(CIMCIC(k),CIMCIC(k)) == (C,C)
> b) outcome(DUPOC(k),CIMCIC(k)) == (C,C)
> *Proof of (a).* A short proof of the outcome (C,C) will lead, in a few addi-
> tional lines comprising some number of characters c, to a proof of the material
> implication
> "(CIMCIC_k(CIMCIC_k.source)==C)=>(CIMCIC_k(CIMCIC_k.source)==C)"
> This in turn will cause the agents to cooperate, bringing about the outcome
> (C,C). Thus, we have a "self-fulfilling prophecy" situation of the kind where
> PBLT can be applied. Specifically, if we let f(k) = ⌊k/2⌋, k₁ = 2c, and p[k]
> be the statement
> "outcome(CIMCIC(k),CIMCIC(k))==(C,C)"
> then the conditions of PBLT are satisfied. Therefore, for some constant k₂,
> we have ⊢ (∀k > k₂)(p[k]).

p. 22, Theorem 5.2(b) (the cross-agent case — Critch's "mutual Löb"):
> *Proof of (b).* Again, a short proof of the outcome (C,C) will lead, in a few
> additional lines comprising some number of characters c, to a proof of CIM-
> CICs' cooperation condition, namely
> "(CIMCIC_k(DUPOC_k.source)==C)=>(DUPOC_k(CIMCIC_k.source)==C)"
> as well as DUPOC's cooperation condition,
> "CIMCIC(k)(DUPOC(k).source)==C"
> Thus, letting f(k) = ⌊k/2⌋, k₁ = 2c, and p[k] be the statement
> "outcome(DUPOC(k),CIMCIC(k))==(C,C)"
> satisfies the conditions of PBLT. Therefore, for some constant k₂, we have
> ⊢ (∀k > k₂)(p[k]).

p. 18, Open Problem 3 (the red cell, PROVEN in the engine 2026-08-20):
> **Open Problem 3.** For large values of k, we conjecture that
> outcome(DUPOC(k),CUPOD(k))==(D,C). Is this the case?
> *Why this problem is challenging.* … It seems we need some way to reason about one
> agent's proof search running out, while the other agent is unable to prove
> that the first agent's proof search runs out.

**ANALYSIS.** Critch closes cross-agent cells with a SINGLE PBLT on the CONJUNCTION
`p[k] = outcome(...) == (C,C)` at `f(k) = ⌊k/2⌋`: a proof of the pair of length `≤ ⌊k/2⌋` plus
`c` extra characters gives each agent's guard fact within its own budget `k` (this is where
`k₁ = 2c` comes from: `⌊k/2⌋ + c ≤ k` for `k > 2c`). The engine instead keeps the two
play-atoms SEPARATE (`Formula` has no conjunction), derives the single-sentence Löb premise
`□_fb A → A` from the two legs by `mutual_loeb` (10 steps, §1.4), and runs `bloeb` on `A`
alone; `B`'s guard is then recovered by soundness + inversion (§4.5–4.6). The engine's
`fb = k − 64V` plays the role of Critch's `⌊k/2⌋`.

### 5.7 PrudentBot in Critch 2022 (p. 26)

> LaVictoire et al. [47] exhibit a computationally unbounded agent called
> PrudentBot, which is similar to DUPOC except that it uses employs an
> additional proof search that allows it to defect against CooperateBot. Such
> agents are particularly interesting at a population scale because they have
> the potential to drive CooperateBots out of existence, which in turn would
> make it more difficult for DefectBot to survive. Hence we ask:
> **Open Problem 9.** Does a computationally bounded version of Pru-
> dentBot [47] exist?
> If so, questions regarding population dynamics among CooperateBots,
> DefectBots, DUPOCs, and PrudentBots would be interesting to examine,
> especially if the game payoffs take into account the additional cost of proof-
> searching incurred by PrudentBot.

### 5.8 Appendix B — the proof-system assumptions (pp. 40–41)

p. 40:
> **Appendix B. Proof system assumptions**
> We have assumed that the proof system S employed by proof_checker
> has the following properties typical of real-world proof systems, as discussed
> by Critch [18, §2.2]:

p. 41:
> a) S can write down expressions that represent arbitrary computable func-
>    tions.
> b) S can write down a number k using O(lg(k)) characters.
> c) S allows for the definition and expansion of abbreviations in the middle
>    of proofs.
> d) There exists a constant e* with the following property: Suppose we are
>    given a proof ρ that is k characters long. Then, it is possible to write
>    out another proof E(ρ) of length at most e* · k, that checks the steps of
>    ρ and verifies that ρ is a valid proof [18, §4.2]. We call this number e* a
>    "proof expansion constant." In the notation and terminology of Critch
>    [18, Definition 4.1], it defines a "proof expansion function", e(k) = e*·k.
>
> Note that Critch [18] operates under the more general assumption that
> e(k) can be any increasing computable function of k. However, since proofs
> written in realistic formal proof systems can be checked in linear time [18],
> we focus in this paper on the simpler special case where e(k) can be taken
> to be a linear function e* · k.

The §6.1 restatement of what PBLT needs (p. 24):
> The following features of the agents' reasoning capabilities are key to the
> proof of PBLT, and hence to the results of this paper:
> 1. The proof language for representing the agents' beliefs needs to be
>    expressive enough to represent numbers and computable functions and
>    to introduce and expand abbreviations.
> 2. There must be a process the agents can follow for deriving beliefs from
>    other beliefs (writing a proof is such a process).

---

## 6. ANALYSIS — the arithmetized instance

Target instance: `Sent := LSentence ℒ_PA` (closed), `Proves k σ := PA ⊢_k σ` ("there is a
PA proof of `σ` of length ≤ k"), `box k σ := □_k σ` := the arithmetic sentence
`∃p (Prf_PA(p, ⌜σ⌝) ∧ len(p) ≤ k̄)` with `k̄` a (binary-efficient) numeral, `size σ :=` the
symbol length of `σ` under the package's coding, `diag g σ :=` the diagonal-lemma fixpoint of
`x ↦ (□_g x → σ)`.

### 6.1 Field-by-field: demanded cost vs plausible PA cost

Notation: `|σ|` = symbol length; `ℓ(p)` = proof length; `c` = an absolute constant depending
only on the PA axiomatization/coding; `e*` = Critch's proof-expansion constant (B(d)).

| field | demanded (engine) | plausible actual PA cost | verdict |
|---|---|---|---|
| `mono` | `k₁ ≤ k₂ → Proves k₂` | exact (a proof of length ≤ k₁ has length ≤ k₂) | **free** |
| `mp` | `m₁ + m₂ + |α|` | concatenate both proofs, add one MP line writing `α`: `m₁ + m₂ + |α| + c_mp` (line delimiter / rule tag) | plausible up to `+c`; exact if `size` is defined as `|·| + c_line` (but then `SizeExact.size_imp` fails — see 6.2) |
| `implTrans` | `a + b + |φ→χ|` | Hilbert-style: instances of `(ψ→χ)→(φ→(ψ→χ))`, then S-axiom `(φ→(ψ→χ))→((φ→ψ)→(φ→χ))`, 3 MPs: `a + b + c·(|φ| + |ψ| + |χ|)`. The CUT FORMULA `ψ` is charged; the engine does not charge it. | plausible ONLY with abbreviations (Critch B(c)): `ψ` was already written inside the premise proofs, so cite it by name; then `a + b + c·|φ→χ| + c'`. Without abbreviations `|ψ| ≤ a` gives at best a multiplicative `(1 + c)·(a+b)` — a rescaled `Proves` |
| `impS2` | `m₁ + m₂ + |φ→χ|` | S-axiom instance (size `~ 3|φ| + 2|ψ| + 2|χ|`) + 2 MPs: `m₁ + m₂ + c·(|φ|+|ψ|+|χ|)` | same as `implTrans`: needs abbreviation of `ψ`, else a constant-factor rescale |
| `boxIntro` (D1) | `kIn + |□_kIn σ|` | from a proof `ρ` of `σ` with `ℓ(ρ) ≤ kIn`: write the numeral `⌜ρ⌝` and VERIFY `Prf(⌜ρ⌝, ⌜σ⌝)` inside PA — that verification IS Critch's `E(ρ)`, length `e*·kIn`; then `∃`-intro: total `e*·kIn + |□_kIn σ| + c` | **the engine hard-codes `e* = 1`**. For PA `e* > 1` (even the numeral `⌜ρ⌝` alone is `Θ(ℓ(ρ))` symbols under an efficient coding, and the step-check adds more). Either prove `boxIntro` with the field's `kIn` replaced by `e*·kIn` (then `bloeb`'s `H4`, `H20` change shape but stay linear) or define `Proves k σ := PA ⊢_{k/e*} σ` — Critch's own move ("e(k) = e*·k makes f(k) ≻ O(lg k) sufficient") |
| `axKf` (D2, object) | gate `a + b + |α| ≤ c`; cost `|instance|` | PA must PROVE `□_a(φ→α) → (□_b φ → □_c α)`. This is ONE uniform lemma `∀a b c x y (…concat(x,y,⌜α⌝) is a proof of length ≤ a+b+|α|+c_mp …)` proven once about variables; the instance is that lemma + `∀`-instantiations at the numerals `a,b,c` and the codes `⌜φ⌝,⌜α⌝`: `C_K + |instance| + c` | plausible: additive constant `C_K` (the size of the once-proven concatenation lemma) plus the instance. The GATE must read `a + b + |α| + c_mp ≤ c` — one extra constant. This is the field the last two commits are building ("Cut — bounded D2 in rule form with exact length accounting", `e774479`) |
| `box4` (D3, object) | gate `a + |□_a σ| ≤ b`; cost `|instance|` | PA proves `□_a σ → □_b □_a σ`: formalized bounded Σ₁-completeness — "if `p` is a proof of `σ` with `ℓ(p) ≤ a` then there is a proof of `□_a σ` of length ≤ b", by PA-internal induction on `p` (the formalized `E(·)`): a uniform lemma with the gate `e*·a + |□_a σ| + c ≤ b` | plausible up to the SAME `e*` factor as `boxIntro` (it is `boxIntro` internalized). Cost `C_4 + |instance|`. Gate becomes `e*·a + |□_a σ| + c ≤ b` |
| `boxMono` | `a ≤ b`; cost `|instance|` | `ℓ(p) ≤ a ∧ a ≤ b → ℓ(p) ≤ b`: a `Δ₀` fact about numerals; `C_mono + |instance|` | **plausible, additive constant** |
| `diagF`/`diagB` | gated on `Proves pm (□_fb σ → σ)`, cost `pm + |instance|` | PA proves `Ψ_g ↔ (□_g Ψ_g → σ)` UNGATED by the diagonal lemma: `Ψ_g := θ(⌜θ⌝)` with `θ(x) := □_g(sub(x,x)) → σ`; the two directions cost `C_diag + |instance| + (cost of evaluating `sub(⌜θ⌝,⌜θ⌝) = ⌜Ψ_g⌝` inside PA)`, the last being polynomial in `|Ψ_g|` — and `|Ψ_g| = c₁·|σ| + c₂·log g + c₃` (the code `⌜θ⌝` is written once as a numeral, `θ` contains `⌜σ⌝`, so `|Ψ_g| ≈ 2·|σ|·c + …`) | plausible (ungated → gated by `mono`, as `BoundedGL.lean:44-51` says). BUT `SizeExact.size_diag` (`numCost g + |σ| + 1`) is FALSE — the fixpoint sentence is linear in `|σ|` with constant ≥ 2 and carries the substitution machinery. Also the numeral-coding trap (`project_arith_numeral_vacuity`): under Cantor-pair codes the code of a binary numeral is exponential, so `⌜Ψ_g⌝` inside `□_g Ψ_g` must use a length-efficient coding or the box guard never fits |

Two structural remarks on the table:

* **Engine cost = "abbreviated Hilbert proof" cost.** Every engine rule charges "subtrees +
  conclusion" and NOTHING for the cut formula (`implTrans`, `impS2`, `mp` all omit `ψ`/`φ`).
  That is exactly the cost profile of a proof system with Critch's B(c) — each formula is
  written once and cited thereafter. A raw Hilbert-style `PA ⊢_k` (no abbreviations) will not
  validate `implTrans`/`impS2` with additive slack. The honest options: (i) define `Proves`
  over a calculus WITH an abbreviation/lemma-citation rule (a "proof as DAG"/`let`-binding
  calculus — length counts each formula once), or (ii) accept a multiplicative expansion and
  instantiate `bloeb` with `size σ := C·|σ| + D` and the `Hᵢ` discharged with those laws
  (`bloeb`/`mutual_loeb` are cost-shape-free, so this works; only `pblt`'s omega block, which
  needs `SizeExact`, must be re-done by hand — exactly the "owes its own asymptotic wrapper"
  clause of `Base/BoundedGL.lean:59-61`).
* **The engine's `e* = 1` is the load-bearing simplification.** `boxIntro`'s gate `kIn +
  |□_kIn φ| ≤ K` and `box4`'s gate `a + |□_a φ| ≤ b` say a proof can be verified in its own
  length. For PA the proof-checking proof is `e*·ℓ(ρ)`. In `bloeb` this changes `H4` (`n₁ →
  e*·n₁`), `H10` (`g → e*·g`), `H20` (`g → e*·g`) and `mutual_loeb`'s `H5`, `H9` — all still
  linear in the unit, so the `W`-multiples in `pblt` just grow by a factor `≈ e*`, and
  `f(k) ≻ O(lg k)` still suffices. This is precisely what Lemma 3.6's proof says ("e(k) = e*·k
  … makes the condition f(k) ≻ O(lg k) sufficient").

### 6.2 What Critch's Lemma 3.6 actually needs, and in what form

From the statement (p. 13), Appendix B (p. 41) and §6.1 (p. 24), the ingredients are:

1. **A UNIFORM Löb premise**: `⊢ (∀k > k₁)(□_{f(k)} p[k] → p[k])` — ONE PA proof with `k` a
   variable. The engine takes the POINTWISE version `∀ k > k₁, Proves (pm k) (□_{f k} φ_k →
   φ_k)` with `pm k = O(log k)` — a Lean-level `∀` over per-`k` object derivations. The two
   are related by instantiation: from the uniform proof `π` (constant length) one gets each
   instance at cost `|π| + |k̄| + |p[k]| = O(log k)`. For the arithmetized instance the
   pointwise form is what `bloeb` consumes; the uniform form is how one PROVES `pm k = O(log
   k)` (prove `∀k (□_k Play(Dupoc(k),Dupoc(k))=C → Play(…)=C)` once — the arithmetized
   `searchBranch` — then instantiate).
2. **A UNIFORM conclusion** `⊢ (∀k > k₂) p[k]`: Critch's proof (via [18, Thm 4.2]) is itself
   a single `∀k` proof. The engine's `pblt` gives `∃ k₂, ∀ k > k₂, ∃ m, Proves m (φ k)` —
   pointwise again, with `m = 4096W(k) = O(log k)`. The pointwise version suffices for the
   outcome theorems (each instance `Dupoc(k)` only needs ITS proof to be short).
3. **The HBL conditions, bounded**, with the expansion function `e(k) = e*·k` entering
   D1/D3 (B(d)), numerals of length `O(lg k)` (B(b) — the engine's `numCost`), and
   abbreviations (B(c) — the engine's "+conclusion only" cost model). Critch never states D2
   separately: it is the "few additional lines comprising c characters" in every Theorem
   5.x proof, i.e. concatenation + MP at cost `+c`.
4. **The modal fixed point** (§3.4 step 1, p. 14) — `diag` — obtained by the diagonal lemma
   (B(a): "expressions that represent arbitrary computable functions" is what makes `sub`
   representable).
5. **The `O(lg k)` instantiation**: `f(k) ≻ O(lg k)` means `f(k) > c·lg k` for large `k` with
   `c` depending on `e*`, `|p|`'s growth, and the diagonal constants. The engine's concrete
   `c` is `8192·(pm + |φ| + log₂ f + 8) ≤ f` — and since for the zoo `pm, |φ| ≤ 100·log₂k +
   1000`, the master threshold is `1646592·log₂k + 16449536 ≤ k` (`Base/Loeb.lean:247`).
   For PA the constants will be larger (the `C_K`, `C_4`, `C_diag` lemma sizes and `e*`
   enter `W`) but the SHAPE `f(k) ≥ C·log k + D` is unchanged.

So Critch's Lemma 3.6, in the form the arithmetized package needs, is: **`bloeb` (14 HBL steps,
cost-shape-free) + a size law of the form `size(imp) ≤ |φ|+|ψ|+c`, `size(box k φ) ≤ c₁·|φ| +
c₂·log k + c₃`, `size(diag g φ) ≤ c₁'·|φ| + c₂'·log g + c₃'` + the `e*`-scaled D1/D3 gates,
instantiated with `g, n₁, n₃, n₄, n₅` as multiples of a unit `W = O(pm + |φ| + log f(k))`,
under `f(k) ≥ C·W`**. That is Critch's `f(k) ≻ O(lg k)` when `pm, |φ| = O(log k)`.

### 6.3 Dupoc k cooperates with Dupoc k, for all large k — as it would run over PA

Fix the coding and let, for each `k`:

* `D_k` := the PA-definable (primitive recursive) program `Dupoc(k)`; `Play(x, y) = C` the
  `Δ₀`/`Σ₁` formula "program `x` run against source `y` returns `C`" (it is a bounded
  computation: `eval` at fuel 2 whose only unbounded-looking step is `proof_search(k, …)`, a
  search over strings of length ≤ k — bounded by `k`).
* **The sentence family** `σ(k) := Play(⌜D_k⌝, ⌜D_k⌝) = C` (Critch's `p[k]`; the engine's
  `φ k = .plays (DupocBot k) (DupocBot k) .C`). `|σ(k)| = O(log k)` because `D_k`'s source
  contains `k` once as a numeral (engine: `2·log₂k + 15`).
* `f(k) := k` (the search budget is the box subscript — `f = id`, `k₁ = 0`, exactly Critch's
  substitution on p. 14).

**Step 0 — transparency (the arithmetized `searchBranch`).** PA proves, uniformly,
`∀k (□_k σ(k) → σ(k))`: "if there is a PA proof of `σ(k)` of length ≤ k then `proof_search(k,
⌜D_k⌝, ⌜σ(k)⌝)` returns `True` (by the formalized correctness of the search loop against the
formalized proof-checker), so `D_k` takes its `C` branch". Instantiating at `k̄` gives
`PA ⊢_{pm(k)} (□_k σ(k) → σ(k))` with `pm(k) = C_T + O(log k)` — the arithmetized
`dupoc_loeb_premise` (engine: `5·log₂k + 33`). This is the ONLY step that mentions the agents'
strategy (Critch's step 3, p. 15). It needs Appendix B(a) (the evaluator and proof-checker are
representable) and is where the engine's `hLoeb` hypothesis comes from.

**Step 1 — the fixed point (`diag`).** Choose `g = g(k) = Θ(W)` (engine: `1024·W`, `W = pm(k)
+ |σ(k)| + log₂k + 8`). By the diagonal lemma build `Ψ_k` with `PA ⊢ Ψ_k ↔ (□_g Ψ_k → σ(k))`;
both directions have proofs of length `c₁ ≤ C_diag + |Ψ_k| + poly` and `c₂` likewise (the
engine's `legF`, `legB`, whose `pm`-gate the arithmetized instance discharges for free by
`mono`). `|Ψ_k| = O(|σ(k)| + log g) = O(log k)`.

**Step 2 — necessitate the forward leg (D1).** From `PA ⊢_{c₁} (Ψ_k → (□_g Ψ_k → σ(k)))`,
weaken to `n₁ ≥ c₁` and get `PA ⊢_{c₃} □_{n₁}(Ψ_k → (□_g Ψ_k → σ(k)))` with `c₃ = e*·n₁ +
|□_{n₁}(…)| + c` (engine `hnec`, `H4` with `e* = 1`).

**Step 3 — first K-distribution (D2).** `PA ⊢_{c₄} □_{n₁}(Ψ_k → (□_gΨ_k → σ)) → (□_g Ψ_k →
□_{n₃}(□_gΨ_k → σ))` with gate `n₁ + g + |□_gΨ_k → σ| + c_mp ≤ n₃` (engine `hK1`/`H5`); `mp`
with step 2 gives `PA ⊢_{c₅} □_g Ψ_k → □_{n₃}(□_g Ψ_k → σ(k))` (engine `h2`).

**Step 4 — second K-distribution (D2) and 4 (D3).** `PA ⊢_{c₆} □_{n₃}(□_gΨ_k → σ) →
(□_{n₄} □_g Ψ_k → □_{n₅} σ)` with gate `n₃ + n₄ + |σ| + c_mp ≤ n₅` (engine `hK2`/`H8`);
`PA ⊢_{c₇} □_g Ψ_k → □_{n₄} □_g Ψ_k` with gate `e*·g + |□_g Ψ_k| + c ≤ n₄` (engine
`hfour`/`H10`). Compose: `implTrans` then `impS2` give `PA ⊢_{c₉} □_g Ψ_k → □_{n₅} σ(k)`
(engine `h4`, `h6`).

**Step 5 — land on the source literal (boxMono).** Since `n₅ ≤ k = f(k)` (the master
constraint `H14`; engine `n₅ = 8192W ≤ k`), `PA ⊢_{c₁₀} □_{n₅} σ(k) → □_k σ(k)` and
`PA ⊢_{c₁₁} □_g Ψ_k → □_k σ(k)` (engine `hmono`, `h6'`). Steps 2–5 are Critch's step 2
("without using any facts about the agents' strategies other than their ability to find
proofs of a certain length", p. 14).

**Step 6 — use the strategy fact.** `implTrans` with Step 0: `PA ⊢_{c₁₂} □_g Ψ_k → σ(k)`
(engine `hE`, `c₁₂ = c₁₁ + pm + |…|`).

**Step 7 — `Ψ_k` is provable.** `mp` with the backward leg: `PA ⊢_{c₁₃} Ψ_k`, `c₁₃ = c₂ + c₁₂
+ |Ψ_k|` (engine `hF`). Critch's step 3.

**Step 8 — box it (D1 again) — the `g ≺ f` dance.** REQUIRE `c₁₃ ≤ g` (engine `H19`): the
fixpoint's subscript must absorb the fixpoint's own proof, which CONTAINS the Löb premise's
proof (`pm`) — so `g` must be chosen after `pm` is known, and `pm ≪ g ≪ n₄, n₃ ≪ n₅ ≤ k`. Then
`PA ⊢_{c₁₄} □_g Ψ_k`, `c₁₄ = e*·g + |□_g Ψ_k| + c` (engine `hG`). Critch's step 4.

**Step 9 — conclude.** `mp` of Step 6 and Step 8: **`PA ⊢_m σ(k)` with `m = c₁₂ + c₁₄ + |σ(k)|
= O(W) = O(log k)`** (engine `m = 4096·W`).

**Step 10 — "the proof fits inside k" (the ONLY place the budget is compared to the proof).**
All of Steps 1–9 hold for every `k`; the side-conditions are the 21 `Hᵢ`, which reduce (after
choosing every stage as a multiple of `W`) to the single inequality `C·W(k) ≤ k`, i.e. `C·(pm(k)
+ |σ(k)| + log₂k + 8) ≤ k` — true for all `k ≥ k₂` by `linear_log2_add_le` since `pm, |σ| =
O(log k)`. In particular `m ≤ k/2 < k` (engine: `pblt_engine_bounded`'s `2·m ≤ f k`), so:

* **META-level discharge (what the engine's cell does):** `PA ⊢_m σ(k)` with `m ≤ k` means the
  standard model satisfies `□_k σ(k)`; by soundness of PA, `σ(k)` is TRUE, i.e. `Dupoc(k)`
  actually returns `C` against itself — and it does so BECAUSE its `proof_search(k, …)`
  finds a proof of length ≤ m ≤ k (Step 0's contrapositive: `D_k` returns `C` only when the
  search succeeds). Engine: `Pf_sound m (φ k) hm : ∃ n, play n (Dupoc k) (Dupoc k) = some C`,
  then `play_search_const_total` + `play_at_of_ex` pin the value at fuel 2
  (`Theorems/DupocBot/vs_DupocBot.lean:42-46`).
* **OBJECT-level discharge (what a re-certification needs):** from `PA ⊢_m σ(k)` and `m ≤ k`,
  `mono` gives `PA ⊢_k σ(k)`, i.e. the guard `□_k σ(k)` is witnessed — the arithmetized
  `proofSearch_spec`; engine analogue: the `search_t`-cite certificate `c_leaf + c_guard k +
  c_node ≤ k` (`Theorems/JustBot/vs_DupocBot.lean:96-104`).

Both players are the same program, so one `σ(k)` discharges both legs of `outcome` — the
engine's `outcome_of_plays _ _ _ _ _ hC hC`. **Result: `∃ k₂, ∀ k > k₂, outcome(Dupoc(k),
Dupoc(k)) = (C, C)`** — Critch's Theorem 3.7, the engine's `outcome_DupocBot_vs_DupocBot :
OutcomeSpec .eventual 2 DupocBot DupocBot (some (.C, .C))`.

**For the mutual cells (PrudentBot-staggered, JustBot).** Replace Step 0 by TWO transparency
lemmas `PA ⊢_{p₁} (□_{kP} A_k → B_k)` and `PA ⊢_{p₂} (□_{kD} B_k → A_k)` (arithmetized
`searchThenSearch_t`/`botSearchStep` and `searchBranch`) and insert `mutual_loeb`'s ten steps
(boxMono ↑, implTrans, D1, D2, mp, D3, implTrans, boxMono ↑, implTrans, implTrans) to
manufacture `PA ⊢_{160V} (□_fb A_k → A_k)` at the LOWERED subscript `fb = k − 64V`; then run
Steps 1–9 with `f(k) := fb` and `pm := 160V`. The extra constraints are `fb ≤ kP` (trivial)
and `fb + 8V + 16V + |B| ≤ fb + 32V ≤ kD = k` (the K-output must land under leg 2's box).
Critch's version of the same is a single PBLT on the conjunction with `f(k) = ⌊k/2⌋`, `k₁ = 2c`
(p. 21–22) — the arithmetized package may take either route; the engine's route needs no
conjunction in the object language.

### 6.4 Summary of what M4 must deliver, and the traps already known

Must-have (for `bloeb`, cost-shape-free): `mono`, `mp`(+c), `implTrans`/`impS2` (with an
abbreviation mechanism OR a rescaled `Proves`), `boxIntro` and `box4` with `e*`-scaled gates,
`axKf` with gate `a + b + |α| + c ≤ c'`, `boxMono`, and the ungated diagonal legs. Nice-to-have
(for a generic `pblt`): size laws linear-with-constants replacing `SizeExact`, and a hand-written
omega block (the `SizeExact` equalities will NOT hold: `|□_k σ|` and `|Ψ_g|` carry Gödel-code
constants; `Base/BoundedGL.lean:56-61` predicts exactly this). Known traps from the memory
notes: unary numerals made every search fail — use binary descriptions; the Cantor-pair CODE of
a binary numeral term is exponential (`box_guard_never_fits`) — box budgets must be node data
or the coding must be length-efficient; `box` is not compositional under bounded provability
(the D2 gate's `+c_mp` is where this shows up); the `.diag` sentence must be FROZEN under
substitution exactly as the engine freezes it (`Program.lean`, `Formula.subst`'s `.diag` arm).
