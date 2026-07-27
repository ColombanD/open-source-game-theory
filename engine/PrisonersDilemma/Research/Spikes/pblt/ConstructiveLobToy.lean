import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

/-!
# ⚠️ SUPERSEDED (2026-07-01) — route (B) tangent, NOT the axiom-removal plan.

This spike pursued the CONSTRUCTIVE/computable route (B): build a witness-bearing Löb term to make
extraction/`eval` computable. That is NOT what removing the `PBLT` axiom needs (route A, faithful,
does not need witnesses). Kept only as a record: §5 builds an axiom-free constructive Löb TERM (a neat
artifact), §8 REFUTES the realizability extraction as unsound. The actual plan is constructed-`Bew`
formulas → definitional `ContextRepr` — see `PBLT_REMOVAL_ROADMAP.md` and memory
`project_pblt_removal_plan`. Do not treat this file as the current direction.

---

# Route 2b, Milestone 1: constructive bounded Löb on a TOY explicit proof system.

The crux (CLAUDE.md): make `box` = "∃ proof TERM of size ≤ k" — a DECIDABLE finite predicate — and
give a CONSTRUCTIVE bounded Löb that EXHIBITS a size-≤-k proof term for the fixpoint. Then `Provable`
collapses to the decidable predicate ⇒ eval computable ⇒ extraction reads the play off the term.

**This toy DERIVES the Löb term** (no `loeb` constructor). `Pf p φ` (target-indexed, as `ProvesN p`)
carries: the Hilbert core, HBL D1/D2/D3, and the TWO irreducible representability base terms
`repr`/`ctx` (the diagonal lemma's content — what `repr_object`/`ctxUnfold` rest on). From these we
DERIVE the diagonal `ψ ↔ (□ψ→p)` and then the Löb chain `bloeb : Pf p (□p→p) → Pf p p` — every step a
real `Pf` TERM with a computable `size`. Soundness (`Pf.sound`) certifies `repr`/`ctx` inject no
falsehood beyond the target `t`, exactly the real layer's `hp0` discipline.

If this all type-checks sorry-free, milestone 1 succeeds: the constructive fixpoint proof-term exists.
-/

namespace ConstructiveLobToy
open Function

/-! ## 1. Formula language with the diagonal atoms + a genuine encoding. -/

inductive Fml where
  | atom (n : Nat)
  | gApp (c : Nat)
  | betaA (b : Fml)
  | imp  (a b : Fml)
  | iff  (a b : Fml)
  | box  (k : Nat) (a : Fml)
deriving DecidableEq, Repr, Inhabited

def encode : Fml → Nat
  | .atom n   => Nat.pair 0 n
  | .gApp c   => Nat.pair 1 c
  | .betaA b  => Nat.pair 2 (encode b)
  | .imp a b  => Nat.pair 3 (Nat.pair (encode a) (encode b))
  | .iff a b  => Nat.pair 4 (Nat.pair (encode a) (encode b))
  | .box k a  => Nat.pair 5 (Nat.pair k (encode a))

theorem encode_inj : Injective encode := by
  intro x
  induction x with
  | atom n => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | gApp c => intro y h; cases y <;> simp_all [encode, Nat.pair_eq_pair]
  | betaA b ih =>
      intro y h; cases y with
      | betaA b' => simp only [encode, Nat.pair_eq_pair] at h; rw [ih h.2]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | imp a b iha ihb =>
      intro y h; cases y with
      | imp a' b' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, ha, hb⟩ := h; rw [iha ha, ihb hb]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | iff a b iha ihb =>
      intro y h; cases y with
      | iff a' b' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, ha, hb⟩ := h; rw [iha ha, ihb hb]
      | _ => simp_all [encode, Nat.pair_eq_pair]
  | box k a ih =>
      intro y h; cases y with
      | box k' a' => simp only [encode, Nat.pair_eq_pair] at h; obtain ⟨_, hk, ha⟩ := h; rw [hk, ih ha]
      | _ => simp_all [encode, Nat.pair_eq_pair]

/-- The diagonal sentence `ψ_b := β(⌜b⌝)`; its self-reference is genuine: `encode (betaA b)` is a
    concrete `Nat` appearing inside `repr`'s RHS. `selfApply b = betaA b`. -/
def selfApply (b : Fml) : Fml := .betaA b

/-! ## 2. Explicit proof TERMS `Pf p` — HBL toolkit + representability base terms. NO `loeb`.
Target-indexed by `p` (the Löb target), exactly as `ProvesN p`, so `ctx` is scoped to `p`. -/

inductive Pf (p : Fml) : Fml → Type where
  | ax_k   (a b : Fml) : Pf p (.imp a (.imp b a))
  | ax_s   (a b c : Fml) : Pf p (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp     {a b : Fml} : Pf p (.imp a b) → Pf p a → Pf p b
  | id     (a : Fml) : Pf p (.imp a a)
  | iffIntro {a b : Fml} : Pf p (.imp a b) → Pf p (.imp b a) → Pf p (.iff a b)
  | iffF   {a b : Fml} : Pf p (.iff a b) → Pf p (.imp a b)
  | iffB   {a b : Fml} : Pf p (.iff a b) → Pf p (.imp b a)
  | nec    {a : Fml} {k : Nat} : Pf p a → Pf p (.box k a)
  | axK    (k : Nat) (a b : Fml) : Pf p (.imp (.box k (.imp a b)) (.imp (.box k a) (.box k b)))
  | four   (k : Nat) (a : Fml) : Pf p (.imp (.box k a) (.box k (.box k a)))
  /-- `repr`: `β(⌜b⌝) ↔ G(⌜selfApply b⌝)` — the diagonal lemma's representability content. -/
  | repr   (b : Fml) : Pf p (.iff (.betaA b) (.gApp (encode (selfApply b))))
  /-- `ctx`: at ψ's own code, `gApp` unfolds to the Löb context `□ψ→p` (scoped to target `p`). -/
  | ctx    (ψ : Fml) {k : Nat} : Pf p (.iff (.gApp (encode ψ)) (.imp (.box k ψ) p))

def Pf.size : {p φ : Fml} → Pf p φ → Nat
  | _, _, .ax_k _ _      => 1
  | _, _, .ax_s _ _ _    => 1
  | _, _, .mp f g        => f.size + g.size + 1
  | _, _, .id _          => 1
  | _, _, .iffIntro f g  => f.size + g.size + 1
  | _, _, .iffF f        => f.size + 1
  | _, _, .iffB f        => f.size + 1
  | _, _, .nec f         => f.size + 1
  | _, _, .axK _ _ _     => 1
  | _, _, .four _ _      => 1
  | _, _, .repr _        => 1
  | _, _, .ctx _         => 1

/-! ## 3. Derived combinators. -/

def Pf.impTrans {p a b c : Fml} (hab : Pf p (.imp a b)) (hbc : Pf p (.imp b c)) : Pf p (.imp a c) :=
  .mp (.mp (.ax_s a b c) (.mp (.ax_k _ _) hbc)) hab

def Pf.iffTrans {p a b c : Fml} (hab : Pf p (.iff a b)) (hbc : Pf p (.iff b c)) : Pf p (.iff a c) :=
  .iffIntro (Pf.impTrans (.iffF hab) (.iffF hbc)) (Pf.impTrans (.iffB hbc) (.iffB hab))

/-! ## 4. The DIAGONAL, derived: `ψ ↔ (□ψ → p)` for `ψ := betaA p`. -/

def diagSent (p : Fml) : Fml := .betaA p

/-- **The constructive diagonal term**: `ψ ↔ (□ψ → p)`, DERIVED from `repr` + `ctx`. -/
def Pf.diag (p : Fml) (k : Nat) :
    Pf p (.iff (diagSent p) (.imp (.box k (diagSent p)) p)) := by
  have hrepr : Pf p (.iff (diagSent p) (.gApp (encode (diagSent p)))) := by
    have := Pf.repr (p := p) p
    simpa [diagSent, selfApply] using this
  have hctx : Pf p (.iff (.gApp (encode (diagSent p))) (.imp (.box k (diagSent p)) p)) :=
    Pf.ctx (p := p) (diagSent p)
  exact Pf.iffTrans hrepr hctx

/-! ## 5. `bloeb` — the bounded-Löb TERM, derived (mirrors `bloeb_from_legs`). NO axiom, NO `loeb`. -/

/-- **Constructive bounded Löb**: from a proof term of `□p → p`, BUILD a proof term of `p`. -/
def Pf.bloeb (p : Fml) (k : Nat) (hLoeb : Pf p (.imp (.box k p) p)) : Pf p p :=
  let ψ := diagSent p
  let hd := Pf.diag p k                                    -- ψ ↔ (□ψ → p)
  let hψf : Pf p (.imp ψ (.imp (.box k ψ) p)) := .iffF hd
  let hψb : Pf p (.imp (.imp (.box k ψ) p) ψ) := .iffB hd
  -- hA : □ψ → □(□ψ → p)   [nec hψf ; axK]
  let hA : Pf p (.imp (.box k ψ) (.box k (.imp (.box k ψ) p))) :=
    .mp (.axK k ψ (.imp (.box k ψ) p)) (.nec hψf)
  -- hAxK2 : □(□ψ→p) → (□□ψ → □p)   [axK]
  let hAxK2 : Pf p (.imp (.box k (.imp (.box k ψ) p)) (.imp (.box k (.box k ψ)) (.box k p))) :=
    .axK k (.box k ψ) p
  let hA2 : Pf p (.imp (.box k ψ) (.imp (.box k (.box k ψ)) (.box k p))) := Pf.impTrans hA hAxK2
  let hfour : Pf p (.imp (.box k ψ) (.box k (.box k ψ))) := .four k ψ
  -- □ψ → □p by S-combinator (from hA2 : □ψ→(□□ψ→□p) and hfour : □ψ→□□ψ)
  let hDbox : Pf p (.imp (.box k ψ) (.box k p)) :=
    .mp (.mp (.ax_s (.box k ψ) (.box k (.box k ψ)) (.box k p)) hA2) hfour
  -- hE : □ψ → p           [hDbox ; hLoeb]
  let hE : Pf p (.imp (.box k ψ) p) := Pf.impTrans hDbox hLoeb
  -- hF : ψ ; hG : □ψ ; p
  let hF : Pf p ψ := .mp hψb hE
  let hG : Pf p (.box k ψ) := .nec hF
  .mp hE hG

/-! ## 6. The payoff. -/

def Boxable (p : Fml) (k : Nat) (φ : Fml) : Prop := ∃ t : Pf p φ, t.size ≤ k

theorem bloeb_exists (p : Fml) (k : Nat) (h : Pf p (.imp (.box k p) p)) : Nonempty (Pf p p) :=
  ⟨Pf.bloeb p k h⟩

/-! ## 7. SOUNDNESS — the anti-cheat. `repr`/`ctx` are honest (sound relative to the target `t`).

`interp` reads `box a := Nonempty (Pf p a)` and the diagonal atoms via the witnessing valuation `Gval`
(at `encode ψ`: `Nonempty (Pf p ψ) → t`). `t` is the fixed truth of the target `p`. Every rule is
`interp`-sound when `t` holds — including `repr`/`ctx`, whose two sides both collapse to
`Nonempty (Pf p ·) → t` under `Gval`. So `Pf p` proves no falsehood beyond what `t` licenses:
the anti-cheat certifying `bloeb`'s term is not a disguised inconsistency. -/

open Classical in
noncomputable def Gval (p : Fml) (t : Prop) (G0 : Nat → Prop) (c : Nat) : Prop :=
  if h : ∃ ψ, encode ψ = c then (Nonempty (Pf p h.choose) → t) else G0 c

noncomputable def interp (p : Fml) (t : Prop) (G0 : Nat → Prop) : Fml → Prop
  | .atom n   => G0 n
  | .gApp c   => Gval p t G0 c
  | .betaA b  => Gval p t G0 (encode (selfApply b))
  | .imp a b  => interp p t G0 a → interp p t G0 b
  | .iff a b  => interp p t G0 a ↔ interp p t G0 b
  | .box _ a  => Nonempty (Pf p a)

@[simp] theorem interp_atom (p t G0 n) : interp p t G0 (.atom n) = G0 n := rfl
@[simp] theorem interp_gApp (p t G0 c) : interp p t G0 (.gApp c) = Gval p t G0 c := rfl
@[simp] theorem interp_betaA (p t G0 b) :
    interp p t G0 (.betaA b) = Gval p t G0 (encode (selfApply b)) := rfl
@[simp] theorem interp_imp (p t G0 a b) :
    interp p t G0 (.imp a b) = (interp p t G0 a → interp p t G0 b) := rfl
@[simp] theorem interp_iff (p t G0 a b) :
    interp p t G0 (.iff a b) = (interp p t G0 a ↔ interp p t G0 b) := rfl
@[simp] theorem interp_box (p t G0 k a) : interp p t G0 (.box k a) = Nonempty (Pf p a) := rfl

theorem Gval_encode (p t G0) (ψ : Fml) : Gval p t G0 (encode ψ) = (Nonempty (Pf p ψ) → t) := by
  rw [Gval, dif_pos ⟨ψ, rfl⟩,
    show (⟨ψ, rfl⟩ : ∃ ψ', encode ψ' = encode ψ).choose = ψ from
      encode_inj (⟨ψ, rfl⟩ : ∃ ψ', encode ψ' = encode ψ).choose_spec]

/-- **Soundness** — for the Löb target `p` an atom with truth `t = G0 n₀` (`hp : interp p t G0 p = t`),
    every `Pf p`-term is `interp`-true when `t` holds. `repr`/`ctx` are sound via `Gval`. This is the
    anti-cheat: `Pf p` injects no falsehood beyond the target. -/
theorem Pf.sound (p : Fml) (t : Prop) (G0 : Nat → Prop)
    (ht : t) (hp : interp p t G0 p = t) :
    ∀ {φ : Fml}, Pf p φ → interp p t G0 φ := by
  intro φ h
  induction h with
  | ax_k a b => intro ha _; exact ha
  | ax_s a b c => intro habc hab ha; exact (habc ha) (hab ha)
  | mp _ _ ihab iha => exact ihab iha
  | id a => intro ha; exact ha
  | iffIntro _ _ ihab ihba => exact ⟨ihab, ihba⟩
  | iffF _ ih => exact ih.mp
  | iffB _ ih => exact ih.mpr
  | nec hb _ => exact ⟨hb⟩
  | axK k a b => intro hab ha; exact ⟨.mp hab.some ha.some⟩
  | four k a => intro ha; exact ⟨.nec ha.some⟩
  | repr b =>
      show interp p t G0 (.betaA b) ↔ interp p t G0 (.gApp (encode (selfApply b)))
      rw [interp_betaA, interp_gApp]        -- both sides are Gval p t G0 (encode (selfApply b))
  | ctx ψ =>
      show interp p t G0 (.gApp (encode ψ)) ↔ (interp p t G0 (.box _ ψ) → interp p t G0 p)
      rw [interp_gApp, Gval_encode, interp_box, hp]

/-! ### Honest note on consistency (why there is NO unconditional consistency theorem here).

`Pf.sound` is `hp0`-RELATIVE: it needs `hp : interp p t G0 p = t` tying `t` to the target. This is the
FAITHFUL mirror of `provesN_sound`/`provesC_sound`, which need `hp0`. For a FALSE target you cannot make
that consistent, so soundness does not certify a false `p` unprovable — and indeed `Pf p p` for a false
`p` may be inhabited (via the diagonal). This is EXACTLY the `provesN_play_extract` obstruction, in the
toy — the constructed `bloeb` term proves `p` SYNTACTICALLY, and its soundness is outcome-relative. -/

/-! ## 8. Milestone-2 ATTEMPT (realizability) — REFUTED, and WHY (a load-bearing negative result).

The natural idea to escape §7's `hp0`-wall: a witness interpretation `R` where the diagonal atoms
`gApp`/`betaA` are DEFINED as the Löb context (`Ctx c := Nonempty (Pf p ψ) → Rp` at `c = encode ψ`),
so `repr`/`ctx` realize DEFINITIONALLY (`Iff.rfl`), seemingly with no `hp0`. A realizer
`Pf p φ → R p W Rp φ` then type-checks, and `realize (bloeb …) : R p = Rp` would extract the witness.

**This is UNSOUND — machine-checked (`Research/Spikes/pblt/` probes, 2026-07-01).** The realizer holds
even WITHOUT the `hp : Nonempty (Pf p p) → Rp` hypothesis, and then for a FALSE target atom
(`W := fun _ => False`, `Rp := False`) it proves `R p = False` from a Löb premise alone — i.e. it
proves `False`. Reason: defining `Ctx` as the context makes `R` itself an INCONSISTENT model — the
diagonal `ψ := betaA p` gets `R ψ = (Nonempty (Pf p ψ) → Rp)`, and `bloeb` builds `Nonempty (Pf p ψ)`
(via `nec hF`), collapsing `R p` to `Rp` unconditionally. The `hp0`-relativity of §7 was NOT dodged;
it was RELOCATED into `R` being unsound.

**CONCLUSION (definitive).** Sound extraction CANNOT come from a self-contained realizability/model
interpretation of `Pf p` — any interpretation validating `repr`/`ctx` definitionally proves false
atoms. The witness for `p` must come from OUTSIDE the object system: the `hp : Nonempty (Pf p p) → Rp`
hypothesis (engine `Provable_sound`) is IRREDUCIBLE and must be genuinely CONSUMED, not made vacuous.
That means the extraction is exactly `Nonempty (Pf p p) → (play witness)` = a soundness for the object
system AT the play-atoms — which is `provesN_play_extract` itself. So Milestone 2 does NOT reduce below
it either: the constructive term (Milestone 1) exists, but turning it into a witness needs object
soundness at play-atoms, and THAT is the crux, not further reducible. Route 2b's remaining content is
therefore: prove object soundness for play-atoms directly (a proof-theoretic normalization of the
`Pf p p` term to an engine play), NOT a model/realizability argument (all such are unsound, proven). -/

end ConstructiveLobToy
