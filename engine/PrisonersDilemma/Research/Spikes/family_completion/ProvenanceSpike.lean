import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CIMCIC.vs_DBot

/-!
# Provenance spike — the ite-frontier, worked to the ground (2026-07-28)

Evidence bundle for the LAST open item of the family-completion program
(`Research/Notes/FAMILY_COMPLETION_DESIGN.md`): reading `.ite`-probe layers.
Everything here is kernel-checked against the CURRENT engine.

## §1 — THE CORRECTION: no outcome flips

The design note's earlier draft claimed ite-reading would flip
`llm_outcome_CIMCIC_vs_DBot` from `(D, C)` to `(C, C)`, on the grounds that the probe
antecedent "CIMCIC plays D vs `.bot DefectBot`" is *cheaply certifiable*. That
conflated EVAL-truth with CERTIFIABILITY: the probe play is CIMCIC's own Gödelian
fall-through — its guard instance is vacuously TRUE (both sides false) yet unprovable,
so `search_t` cannot fire it and `search_f` cannot refute it. **The probe atom has NO
certificate at ANY budget** (`cimcic_probe_uncertifiable` below, kernel-checked), so
`mp`-extraction through the hypothetical ite-chain is blocked forever, and the
outcome stands. The same audit clears the whole zoo:

  * probe antecedents of the CIMCIC/EBot family — Gödelian fall-throughs
    (uncertifiable at every budget, as here);
  * probe antecedents of the floor family (Dupoc/Prudent/Just/Cupod) — `search_f`
    else-plays, priced ABOVE the consuming guard's budget by the floor;
  * everything else — semantically false (soundness-blocked).

**Consequence: the ite-reading rule adds expressiveness without flipping any current
outcome.** What it DOES break is the census *architecture*: probe-implication chains
become provable with priced-out antecedents, which the Guarded `TailTo` invariant
cannot see — hence the provenance kernel (§2, §3).

## §2 — The extraction core

`SpineW` packages an implication chain to a target together with PROOFS of every
antecedent and exact transcript bookkeeping; `SpineW.extract` is the kernel-checked
extraction lemma (iterated `mp` at the recorded cost). This is the tool the
provenance census reasons about: a chain endangers the target exactly when a spine
WITNESS exists within budget — so the census prices the witnesses, not the chains.

## §3 — The provenance kernel, designed (integration plan in the note)

The `mp` arm closes cleanly: from a witnessed spine of the conclusion and the
antecedent premise, `SpineW.step` extends the spine and the arithmetic
`m₁ + m₂ + α.size ≤ K` + `K + c ≤ k` gives `m₁ + (m₂ + α.size + c) ≤ k` exactly.
The `implTrans` arm does NOT close by naive extraction (the cut formula's size
escapes the conclusion's ledger — same wall as T48's C2, for the same reason); the
correct route is the SUFFIX-CLASS design: the census class is `TailTo` chains PLUS
all suffixes of the target player's own telescope conclusions, with per-instance
pricing hypotheses for the probe atoms (this file's §1 lemmas are exactly those
hypotheses for the CIMCIC family) and soundness kills for the guard boxes. The two
integration halves:

  (i) **probe-guarded search telescopes** (ite-layers over NON-constant, then-polarity
      descents — the depth-`n` closure of today's `iteBranchSearch_t`): census-safe by
      the same shape kills as today (the floor targets' then-branches are constants),
      integrable by the `searchChain` recipe.
  (ii) **full simulator transparency** (const branches, both polarities — what reads
      DBot outright): requires the suffix-class kernel with pricing hypotheses; flips
      nothing (§1), but re-architects `Base/Exclusion`.
-/

namespace PD.Spikes.Provenance

open PD PD.BaseTheorems PD.Bots PD.Theorems

/-! ## §1 — The correction, kernel-checked -/

/-- **CIMCIC's probe play vs `.bot DefectBot` is TRUE but has NO atom certificate at
    ANY budget**: it is the else-play of CIMCIC's own budget-`k` search, whose guard
    instance is vacuously true — `search_t` dies on the guard census, `search_f` dies
    on soundness (one cannot refute a true formula). The extraction that would flip
    `CIMCIC vs DBot` is therefore blocked forever. -/
theorem cimcic_probe_uncertifiable (k n : Nat) :
    ¬ AtomProvable n (.plays (CIMCIC k) (.bot DefectBot) Action.D) := by
  rintro ⟨cert, -⟩
  cases cert with
  | search_t hg _ =>
      exact cimcic_botDefect_guard_not_provable k hg
  | search_f hneg _ =>
      exact (Pf_sound _ _ hneg) (cimcic_guard_botDefect_interp k)

/-- The kill pattern the provenance kernel's `mp` arm uses: a priced-out antecedent
    contradicts its own witness. -/
theorem priced_antecedent_kills {k m₂ : Nat} {α : Formula}
    (hpriced : ∀ m, m ≤ k → ¬ Pf m α) (h2 : Pf m₂ α) (hm : m₂ ≤ k) : False :=
  hpriced m₂ hm h2

/-! ## §2 — The extraction core -/

/-- An extraction spine: `φ` is an implication chain ending at `T`, together with
    PROOFS of every antecedent and the exact `mp`-transcript bookkeeping. -/
inductive SpineW (T : Formula) : Formula → Nat → Prop
  | tail : SpineW T T 0
  | step {α ψ : Formula} {m c : Nat} :
      Pf m α → SpineW T ψ c → SpineW T (.impl α ψ) (m + ψ.size + c)

/-- **THE EXTRACTION LEMMA**: a proved chain with witnessed antecedents yields the
    tail at exactly the bookkept cost — iterated `mp`, transcript-faithful. -/
theorem SpineW.extract {T : Formula} : ∀ {φ : Formula} {c : Nat},
    SpineW T φ c → ∀ {K : Nat}, Pf K φ → Pf (K + c) T := by
  intro φ c sp
  induction sp with
  | tail => intro K h; simpa using h
  | step hα sp ih =>
      intro K h
      rename_i α ψ m c'
      have hψ : Pf (K + m + ψ.size) ψ := .mp K m α ψ h hα (Nat.le_refl _)
      have := ih hψ
      have heq : K + m + ψ.size + c' = K + (m + ψ.size + c') := by omega
      exact heq ▸ this

/-- The `mp`-arm arithmetic of the provenance kernel, verified in isolation: the
    extended spine's ledger stays within the global budget. -/
theorem mp_arm_ledger {K k m₁ m₂ c : Nat} {α : Formula}
    (hsz : m₁ + m₂ + α.size ≤ K) (hK : K + c ≤ k) :
    m₁ + (m₂ + α.size + c) ≤ k := by omega

/-! ## §4 — The ELSE-polarity census skeleton: the `Bad` invariant (2026-07-28)

Mapped during the (blocked) else-polarity integration, which established that the
Guarded/`TailToS` censuses are falsified by provable box-headed compositions
(`implTrans` of a searcher's `searchBranch` self-read with an else-probe chain).
Three walls were identified; TWO fall to the invariant below, kernel-checked at the
Formula level:

* **the axKf wall** (the modal tier manufactures box-tailed implications with
  arbitrary clean antecedents, defeating every finite tail-set widening) — killed by
  BOX-TRANSPARENCY (`Bad (□ φ) = Bad φ`): the box-content mirrors the implication
  structure, so `boxMono`/`box4`/`axKf`/`atomBoxImpl` conclusions SELF-ANNIHILATE
  (their antecedent is exactly as Bad as their tail — the same mechanism that made
  `implRefl` census-safe under the Guarded invariant);
* **the diag/Löb wall** (Löb-premise shapes `□_fb tgt → tgt` must stay classed and
  recursable, yet their antecedent's content IS the tail) — killed by
  DIAG-TRANSPARENCY plus the SELF-BOX EXEMPTION on antecedents
  (`¬ Bad α ∨ α = □_n ψ`): `diagF` conclusions leave the class, `diagB`'s premise
  stays classed (`bad_lob_premise`), while the dangerous compositions — whose box
  content differs from their consequent — stay excluded (`bad_not_boxHeaded`).

**The RESIDUAL (open — pushed three refinement rounds further, 2026-07-28 second
session; each round below closed the previous hole and exposed the next):**

* **v2→v3a (diag-OPACITY)**: diag-transparency is unnecessary — with `Bad(.diag) =
  False` the diagF/diagB conclusions stay classed via their `¬Bad(diag)` antecedent
  slots and both arms recurse their GATE premises (`Pf pm (□_fb tgt → tgt)`, in-class
  via the exemption). Simpler, and box-targets stop being special for diag.
* **v3b (the SORT SPLIT)**: the exemption generalizes to
  `α = □_n β ∧ BadT β ∧ (β = ψ ∨ boxCore β ≠ boxCore ψ ∨ …)` where `BadT` is the
  class restricted to TARGET-sort base atoms (`St`), excluding GUARD-sort atoms
  (`Sg`, the guard instances). The sort split is what separates the PROVABLE
  box-headed reads (`searchBranch`: box content = a guard instance ∈ Sg → rejected)
  from the UNPROVABLE box-of-target heads (content chains to St → accepted,
  recursable) — box-elim SHAPE alone cannot separate them, since source-reading makes
  S prove GL-invalid box-elim implications by design.
* **v3c (core/tower conditions)**: `boxCore`-comparison excludes the
  boxMono/box4 factories (content core = consequent core) while keeping Löb premises
  (`β = ψ` exactly) and unrelated-cut recursion targets (cores differ); a
  tower-height disjunct would readmit box-tower-elimination shapes
  (`□□γ → γ`, GL-invalid, needed as recursion targets for boxed Löb-targets) — but
  towers cannot be action-refined against the sort split without…
* **the v3 LEAK (impS2 corner)**: for an acceptance-classed conclusion
  `□_n β → χ` with `boxCore β = boxCore ψ` at the cut (box-tower-height mismatch),
  NEITHER premise of `impS2`/`implTrans` is classed, and one of them
  (`.impl γ (□ʲγ)` via `atomBoxImpl`) is genuinely PROVABLE — the recursion has no
  target although the other premise is semantically unprovable.

The pattern — four invariant refinements, each spawning a strictly more exotic
corner (probes → boxes → diag → box-towers) — is the signature of a problem needing
cut-elimination-strength machinery over the modal tier, not another side condition.
Until that exists, the else rule stays out of `S`: it adds NO extractable theorem
(every zoo probe is priced or false, §1), so the omission is consequence-free. -/

/-- The else-polarity census invariant candidate: chains to `S`-atoms through
    non-Bad antecedents, with box/diag TRANSPARENCY and the self-box EXEMPTION. -/
def Bad (S : Formula → Prop) : Formula → Prop
  | .impl α ψ => Bad S ψ ∧ (¬ Bad S α ∨ ∃ n, α = .box n ψ)
  | .box _ φ => Bad S φ
  | .diag _ φ => Bad S φ
  | φ => S φ

@[simp] theorem Bad_impl (S : Formula → Prop) (α ψ : Formula) :
    Bad S (.impl α ψ) ↔ Bad S ψ ∧ (¬ Bad S α ∨ ∃ n, α = .box n ψ) := Iff.rfl
@[simp] theorem Bad_box (S : Formula → Prop) (n : Nat) (φ : Formula) :
    Bad S (.box n φ) ↔ Bad S φ := Iff.rfl
@[simp] theorem Bad_diag (S : Formula → Prop) (g : Nat) (φ : Formula) :
    Bad S (.diag g φ) ↔ Bad S φ := Iff.rfl
@[simp] theorem Bad_plays (S : Formula → Prop) (p q : Prog) (a : Action) :
    Bad S (.plays p q a) ↔ S (.plays p q a) := Iff.rfl

/-- Box-transparency kills the boxMono factory: its conclusion self-annihilates. -/
theorem bad_boxMono_not (S : Formula → Prop) (a b : Nat) (φ : Formula) :
    ¬ Bad S (.impl (.box a φ) (.box b φ)) := by
  rintro ⟨h1, h2 | ⟨n, he⟩⟩
  · exact h2 h1
  · injection he with _ he2
    have := congrArg Formula.size he2
    simp only [Formula.size] at this
    omega

/-- Box-transparency kills box4: its conclusion self-annihilates. -/
theorem bad_box4_not (S : Formula → Prop) (a b : Nat) (φ : Formula) :
    ¬ Bad S (.impl (.box a φ) (.box b (.box a φ))) := by
  rintro ⟨h1, h2 | ⟨n, he⟩⟩
  · exact h2 h1
  · injection he with _ he2
    have := congrArg Formula.size he2
    simp only [Formula.size] at this
    omega

/-- **THE AXKF WALL FALLS**: under box-transparency the axKf conclusion is NEVER in
    the class — whatever `φ`/`α`, the antecedent's content is exactly as Bad as the
    inner chain it guards. -/
theorem bad_axKf_not (S : Formula → Prop) (a b c : Nat) (φ α : Formula) :
    ¬ Bad S (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))) := by
  rintro ⟨⟨hα, hinner⟩, houter | ⟨n, he⟩⟩
  · -- the outer's ¬Bad-condition contradicts the inner's own condition
    refine houter ⟨hα, ?_⟩
    rcases hinner with hφ | ⟨m, he⟩
    · exact Or.inl hφ
    · injection he with _ he2
      exact Or.inr ⟨c, he2⟩
  · injection he with _ he2
    injection he2 with he3 _
    have := congrArg Formula.size he3
    simp only [Formula.size] at this
    omega

/-- Box-transparency kills atomBoxImpl: same atom on both sides annihilates. -/
theorem bad_atomBoxImpl_not (S : Formula → Prop) (kBox : Nat) (p q : Prog) (a : Action) :
    ¬ Bad S (.impl (.plays p q a) (.box kBox (.plays p q a))) := by
  rintro ⟨h1, h2 | ⟨n, he⟩⟩
  · exact h2 h1
  · have := congrArg Formula.size he
    simp only [Formula.size] at this
    omega

/-- Diag-transparency kills diagF: its INNER implication self-annihilates (the boxed
    diag's content is exactly as Bad as the target), so the conclusion never enters
    the class. -/
theorem bad_diagF_not (S : Formula → Prop) (g : Nat) (tgt : Formula) :
    ¬ Bad S (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)) := by
  rintro ⟨⟨htgt, hcond⟩, -⟩
  rcases hcond with h | ⟨n, he⟩
  · exact h htgt
  · injection he with _ he2
    have := congrArg Formula.size he2
    simp only [Formula.size] at this
    omega

/-- **THE DIAG WALL FALLS**: the Löb-premise shape stays IN the class via the
    self-box exemption — `diagB`'s premise is classed and recursable whenever its
    conclusion is. -/
theorem bad_lob_premise (S : Formula → Prop) (fb : Nat) (tgt : Formula)
    (h : Bad S tgt) : Bad S (.impl (.box fb tgt) tgt) :=
  ⟨h, Or.inr ⟨fb, rfl⟩⟩

/-- The else-chain (the counterexample's second leg) is correctly OUT of the class:
    its probe antecedent is a forbidden atom. -/
theorem bad_not_elseChain (S : Formula → Prop) (p q : Prog) (c : Action) (T : Formula)
    (hS : S (.plays p q c)) (hne : Formula.plays p q c ≠ .box 0 T) :
    ¬ Bad S (.impl (.plays p q c) T) := by
  rintro ⟨-, h | ⟨n, he⟩⟩
  · exact h hS
  · exact Formula.noConfusion he

/-- The box-headed composition (the counterexample chain itself, and the
    `searchBranch` self-read leg) is correctly OUT of the class whenever the box
    content is a forbidden atom DIFFERENT from the consequent. -/
theorem bad_not_boxHeaded (S : Formula → Prop) (n : Nat) (β T : Formula)
    (hβ : S β) (hplays : ∃ p q c, β = Formula.plays p q c) (hne : β ≠ T) :
    ¬ Bad S (.impl (.box n β) T) := by
  rintro ⟨-, h | ⟨m, he⟩⟩
  · obtain ⟨p, q, c, rfl⟩ := hplays
    exact h hβ
  · injection he with _ he2
    exact hne he2

end PD.Spikes.Provenance
