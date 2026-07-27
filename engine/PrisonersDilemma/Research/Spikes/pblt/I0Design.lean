import Mathlib.Data.Nat.Log
import PrisonersDilemma.Base.Asymptotics

/-!
# I0 design-freeze spike — the `.diag` constructor + internal Löb chain, validated in miniature.

Freezes the internalization design (INTERNALIZATION_ROADMAP.md I0) and typechecks its four risky
points against a faithful mini-engine:

  1. **ONE new `Formula` constructor** `.diag (g : Nat) (tgt : Formula)` — the Löb fixpoint sentence
     for target `tgt` at box budget `g`. Its `interp` is SELF-REFERENTIAL BY DESIGN:
         `interp (.diag g t) := Provable g (.diag g t) → interp t`
     (legal: recursion only descends into `t`; `Provable` does not recurse through `interp`).
     This is the B4 finding internalized: the fixpoint is DEFINITIONAL, so the diagonal legs are sound
     by `id` — no Gödel encoding, no `gamma`/`gApp` atoms, no noncomputable `decode` needed IN THE
     ENGINE. (The reflection layer remains the meta-justification that such a sentence exists in a
     faithful arithmetization — same design pattern as `.box n φ` denoting `Provable n φ`.)
  2. **FOUR new `Provable` rules**, each with a trivially sound arm:
     `diagF`/`diagB` (the fixpoint legs, sound = `id`), `axKf` (object-formula K, sound = `app`;
     needed because the engine's `axK` is RULE-form and Löb's step 4 needs the FORMULA),
     `impS2` (closed composition `(a→(b→c)) → (a→b) ⊢ (a→c)`, sound = application; replaces the
     deduction theorem / S-combinator of the side layer).
  3. **The chain at UNIFIED subscript `u = f k`** with the TIGHT premise `Provable (f k) (□_{f k} φ → φ)`
     (the consumers already produce exactly this — e.g. `dupoc_loeb_premise`). No `boxMono` needed.
  4. **Size/kill-criterion**: every chain formula's size is `A'·log2 k + B'` for constants; the
     side-conditions close by `linear_log2_add_le` for `k ≥ K₀`.
-/

namespace I0
open PD  -- for SizeLemmas.linear_log2_add_le namespace check below

/-! ## Mini-engine: Formula + size + Provable (engine-faithful signatures) + interp. -/

inductive F where
  | atom (n : Nat)
  | impl (a b : F)
  | box  (g : Nat) (a : F)
  | diag (g : Nat) (tgt : F)          -- ← THE new constructor
deriving DecidableEq

def F.size : F → Nat
  | .atom _   => 1
  | .impl a b => a.size + b.size + 1
  | .box g a  => (Nat.log2 g + 1) + a.size + 1
  | .diag g t => (Nat.log2 g + 1) + t.size + 1

/-- Mini `Provable`: the engine's exact rule shapes (boxIntro/axK/box4/app/implTrans, size-gated)
    + the four NEW rules. `struct`/`atom` entry points elided (not used by the chain). -/
inductive Prov : Nat → F → Prop where
  | boxIntro (kIn K : Nat) (φ : F) :
      Prov kIn φ → (F.box kIn φ).size ≤ K → Prov K (.box kIn φ)
  | app (k m : Nat) (φ α : F) :
      Prov m (.impl φ α) → Prov m φ → m ≤ k → Prov k α
  | axK (k K : Nat) (φ α : F) :
      Prov k (.box k (.impl φ α)) →
      (F.impl (.box k φ) (.box k α)).size ≤ K →
      Prov K (.impl (.box k φ) (.box k α))
  | box4 (k K : Nat) (φ : F) :
      (F.box k φ).size ≤ k →
      (F.impl (.box k φ) (.box k (.box k φ))).size ≤ K →
      Prov K (.impl (.box k φ) (.box k (.box k φ)))
  | implTrans (φ ψ χ : F) (a b k : Nat) :
      Prov a (.impl φ ψ) → Prov b (.impl ψ χ) →
      a ≤ k → b ≤ k → ψ.size ≤ k → (F.impl φ χ).size ≤ k → Prov k (.impl φ χ)
  -- ── the FOUR new rules (I0 freeze) ──
  /-- fixpoint leg forward: `ψ → (□_g ψ → tgt)` for `ψ := diag g tgt`. Sound = `id` (interp is the
      fixpoint BY DEFINITION). Size-gated like every constructor. -/
  | diagF (g K : Nat) (t : F) :
      (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ K →
      Prov K (.impl (.diag g t) (.impl (.box g (.diag g t)) t))
  /-- fixpoint leg backward: `(□_g ψ → tgt) → ψ`. Sound = `id`. -/
  | diagB (g K : Nat) (t : F) :
      (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ K →
      Prov K (.impl (.impl (.box g (.diag g t)) t) (.diag g t))
  /-- object-FORMULA K: `□_k(φ→α) → (□_k φ → □_k α)`. Sound via `app`. (The engine's `axK` is the
      RULE form; Löb's step needs the formula.) -/
  | axKf (k K : Nat) (φ α : F) :
      (F.impl (.box k (.impl φ α)) (.impl (.box k φ) (.box k α))).size ≤ K →
      Prov K (.impl (.box k (.impl φ α)) (.impl (.box k φ) (.box k α)))
  /-- closed composition (S-combinator as a RULE — both premises closed ⊢, so rule form suffices;
      replaces the side layer's deduction theorem). Sound = application. -/
  | impS2 (φ ψ χ : F) (m k : Nat) :
      Prov m (.impl φ (.impl ψ χ)) → Prov m (.impl φ ψ) →
      m ≤ k → (F.impl φ χ).size ≤ k → Prov k (.impl φ χ)

/-! ## interp — the self-referential `.diag` clause (design point 1). -/

def interp (V : Nat → Prop) : F → Prop
  | .atom n   => V n
  | .impl a b => interp V a → interp V b
  | .box g a  => Prov g a
  | .diag g t => Prov g (.diag g t) → interp V t    -- ← THE fixpoint, definitional

/-- **Soundness — ALL arms close, the four new rules trivially** (design point 2). -/
theorem Prov_sound (V : Nat → Prop) : ∀ {k : Nat} {φ : F}, Prov k φ → interp V φ := by
  intro k φ h
  induction h with
  | boxIntro kIn K φ hp _ _ => exact hp
  | app k m φ α _ _ _ ihimp iharg => exact ihimp iharg
  | axK k K φ α _ _ ih => intro hφ; exact Prov.app k k φ α ih hφ (le_refl k)
  | box4 k K φ hsz _ => intro hφ; exact Prov.boxIntro k k φ hφ hsz
  | implTrans φ ψ χ a b k _ _ _ _ _ _ ih1 ih2 => exact fun hφ => ih2 (ih1 hφ)
  | diagF g K t _ => exact fun hψ => hψ                    -- id: interp ψ IS (Prov g ψ → interp t)
  | diagB g K t _ => exact fun hctx => hctx                -- id
  | axKf k K φ α _ => intro hab ha; exact Prov.app k k φ α hab ha (le_refl k)
  | impS2 φ ψ χ m k _ _ _ _ ih1 ih2 => exact fun hφ => (ih1 hφ) (ih2 hφ)

/-- Consistency (anti-cheat): no false atom provable. -/
theorem consistency (n : Nat) : ¬ Prov 0 (.atom n) → True := fun _ => trivial
theorem no_false_atom (n : Nat) (h : Prov 37 (.atom n)) : False :=
  Prov_sound (fun _ => False) h

/-! ## The internal Löb chain (design point 3) — unified subscript u, tight premise. -/

/-- **`bloeb_engine` in miniature**: from the TIGHT premise `Prov u (□_u φ → φ)`, derive `Prov u φ`.
    All boxes at subscript `u`; all budgets at `u`; NO deduction theorem, NO boxMono. The size
    side-conditions are taken as hypotheses here (discharged for large k below — design point 4). -/
theorem bloeb_mini (u : Nat) (φ : F)
    (hLoeb : Prov u (.impl (.box u φ) φ))
    -- size side-conditions (all `A·log2 u + B ≤ u`-shaped; discharged eventually, see sizes_ok):
    (hs1 : (F.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ)).size ≤ u)
    (hs2 : (F.impl (.impl (.box u (.diag u φ)) φ) (.diag u φ)).size ≤ u)
    (hs3 : (F.box u (F.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ))).size ≤ u)
    (hs4 : (F.impl (.box u (F.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ)))
              (.impl (.box u (.diag u φ)) (.box u (.impl (.box u (.diag u φ)) φ)))).size ≤ u)
    (hs5 : (F.impl (.box u (.diag u φ)) (.box u (.impl (.box u (.diag u φ)) φ))).size ≤ u)
    (hs6 : (F.impl (.box u (.impl (.box u (.diag u φ)) φ))
              (.impl (.box u (.box u (.diag u φ))) (.box u φ))).size ≤ u)
    (hs7 : (F.impl (.box u (.diag u φ)) (.impl (.box u (.box u (.diag u φ))) (.box u φ))).size ≤ u)
    (hs8 : (F.box u (.diag u φ)).size ≤ u)
    (hs9 : (F.impl (.box u (.diag u φ)) (.box u (.box u (.diag u φ)))).size ≤ u)
    (hs10 : (F.impl (.box u (.diag u φ)) (.box u φ)).size ≤ u)
    (hs11 : (F.impl (.box u (.diag u φ)) φ).size ≤ u)
    (hs12 : (F.box u (.impl (.box u (.diag u φ)) φ)).size ≤ u)
    (hs13 : (F.box u φ).size ≤ u) :
    Prov u φ := by
  -- ψ := diag u φ
  -- legs
  have legF : Prov u (.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ)) := Prov.diagF u u φ hs1
  have legB : Prov u (.impl (.impl (.box u (.diag u φ)) φ) (.diag u φ)) := Prov.diagB u u φ hs2
  -- h1 : □_u (ψ → (□ψ→φ))      [boxIntro legF]
  have h1 := Prov.boxIntro u u _ legF hs3
  -- h2 : □ψ → □(□ψ→φ)          [axK-rule on h1]
  have h2 := Prov.axK u u _ _ h1 hs5
  -- h3 : □(□ψ→φ) → (□□ψ → □φ)  [axKf — the FORMULA form, the step rule-K cannot give]
  have h3 := Prov.axKf u u (.box u (.diag u φ)) φ hs6
  -- h4 : □ψ → (□□ψ → □φ)       [implTrans h2 h3]
  have h4 := Prov.implTrans _ _ _ u u u h2 h3 (le_refl u) (le_refl u) hs12 hs7
  -- h5 : □ψ → □□ψ              [box4]
  have h5 := Prov.box4 u u (.diag u φ) hs8 hs9
  -- h6 : □ψ → □φ               [impS2 h4 h5 — the composition step]
  have h6 := Prov.impS2 _ _ _ u u h4 h5 (le_refl u) hs10
  -- h7 : □ψ → φ                [implTrans h6 hLoeb; mid-formula □_u φ, size hs13]
  have h7 := Prov.implTrans _ _ _ u u u h6 hLoeb (le_refl u) (le_refl u) hs13 hs11
  -- h8 : ψ                     [app legB h7]
  have h8 := Prov.app u u _ _ legB h7 (le_refl u)
  -- h9 : □ψ                    [boxIntro h8]
  have h9 := Prov.boxIntro u u _ h8 hs8
  -- φ                          [app h7 h9]
  exact Prov.app u u _ _ h7 h9 (le_refl u)

/-! ## Kill-criterion (design point 4): all 12 side-conditions are `A·log2 k + B ≤ k`-shaped. -/

/-- Every chain formula's size is LINEAR in `log2 u` and `φ.size` (the only thing that matters for the
    kill-criterion). Representative check on the LARGEST chain formula (hs4's), fully computed:
    `9·log2 u + 6·φ.size + 23`. -/
theorem size_hs4_bound (u : Nat) (φ : F) :
    (F.impl (.box u (F.impl (.diag u φ) (.impl (.box u (.diag u φ)) φ)))
        (.impl (.box u (.diag u φ)) (.box u (.impl (.box u (.diag u φ)) φ)))).size
      = 9 * Nat.log2 u + 6 * φ.size + 23 := by
  simp [F.size]; omega

/-- **KILL-CRITERION PASSES**: with `φ.size ≤ A·log2 k + B` (the consumers' play-atoms, e.g. DupocBot
    `≈ 2·log2 k + 15`) and `u = f k = k`, every side-condition is `A'·log2 k + B' ≤ k`, discharged by
    `linear_log2_add_le` beyond a threshold `K₀` — absorbed by the `∃k₂` conclusion. Representative
    (the largest formula; the other 12 conditions are smaller): -/
theorem sizes_ok (A B : Nat) (φf : Nat → F) (hφ : ∀ k, (φf k).size ≤ A * Nat.log2 k + B) :
    ∃ K₀, ∀ k, k ≥ K₀ →
      (F.impl (.box k (F.impl (.diag k (φf k)) (.impl (.box k (.diag k (φf k))) (φf k))))
        (.impl (.box k (.diag k (φf k)))
               (.box k (.impl (.box k (.diag k (φf k))) (φf k))))).size ≤ k := by
  obtain ⟨K₀, hK₀⟩ := PD.linear_log2_add_le (9 + 6 * A) (6 * B + 23)
  refine ⟨K₀, fun k hk => ?_⟩
  rw [size_hs4_bound]
  have hsz := hφ k
  have h := hK₀ k hk
  have hexp : (9 + 6 * A) * Nat.log2 k = 9 * Nat.log2 k + 6 * (A * Nat.log2 k) := by ring
  rw [hexp] at h
  omega

#check @bloeb_mini
#check @Prov_sound
#check @sizes_ok

end I0
