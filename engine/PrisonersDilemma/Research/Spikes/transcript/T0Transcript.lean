import Mathlib.Data.Nat.Log
import PrisonersDilemma.SizeLemmas

/-!
# T0 spike — transcript-length accounting: the Löb chain closes (kill-criterion for Route B).

`DECIDABILITY_ROADMAP.md` T0. Mini-engine where `Prov k φ` means "φ has a proof whose TOTAL TRANSCRIPT
costs ≤ k characters": every rule ADDS its premises' transcripts plus its own conclusion's size
(Critch's literal cost model — under which bounded proof search is genuinely finite).

THE RISK BEING TESTED: under transcript cost the fixpoint ψ's proof CONTAINS the Löb premise's proof,
so `□`-ing ψ needs its subscript `g` ≥ ψ's proof transcript — Critch's `g ≺ f` subscript dance, which
the conclusion-cost engine never needed. The saving hypothesis: the consumers' tight premises have
O(log k) TRANSCRIPTS (single-leaf `searchBranch` / few-step `mutual_loeb` proofs). We validate:
  1. the additive rule set (incl. upward `boxMono` and ADDITIVE `axKf` — Critch's Implication
     Distribution) is SOUND (`Prov_sound`, box := Prov, diag definitional) + budget-monotone;
  2. `bloeb_transcript` — the full chain with explicit per-step budgets (21 side-conditions);
  3. `pblt_transcript` — KILL-CRITERION: for `f = id`, premise transcript ≤ P·log2 k + Q and target
     size ≤ A·log2 k + B, the chain closes for all large k with everything O(log k).
-/

namespace T0
open PD

/-- `Nat.log2` is monotone. -/
theorem log2_mono {m n : Nat} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  simpa [Nat.log2_eq_log_two] using Nat.log_mono_right h

/-! ## 1. Formulas + transcript-relevant size (numerals pay log2, as the engine). -/

inductive F where
  | atom (n : Nat)
  | impl (a b : F)
  | box  (g : Nat) (a : F)
  | diag (g : Nat) (t : F)
deriving DecidableEq

def F.size : F → Nat
  | .atom _   => 1
  | .impl a b => a.size + b.size + 1
  | .box g a  => (Nat.log2 g + 1) + a.size + 1
  | .diag g t => (Nat.log2 g + 1) + t.size + 1

/-! ## 2. `Prov` with ADDITIVE (transcript) budgets. Each rule's conclusion pays the sum of its
premises' transcripts + its own conclusion's character size (leaves pay conclusion size + gate). -/

inductive Prov : Nat → F → Prop where
  /-- object modus ponens: pays both subproofs + the conclusion. -/
  | app {m₁ m₂ k : Nat} (φ α : F) :
      Prov m₁ (.impl φ α) → Prov m₂ φ → m₁ + m₂ + α.size ≤ k → Prov k α
  /-- necessitation: `□_g φ` pays the INNER transcript (≤ g — the subscript IS the inner budget)
      plus the conclusion. This is Critch's Bounded Necessitation with linear E. -/
  | boxIntro {m g k : Nat} (φ : F) :
      Prov m φ → m ≤ g → m + (F.box g φ).size ≤ k → Prov k (.box g φ)
  /-- UPWARD box-subscript monotonicity (object formula): a ≤g-cost proof is a ≤b-cost proof. -/
  | boxMono {a b k : Nat} (φ : F) :
      a ≤ b → (F.impl (.box a φ) (.box b φ)).size ≤ k →
      Prov k (.impl (.box a φ) (.box b φ))
  /-- ADDITIVE K (Critch's Implication Distribution): combining an `a`-cost proof of `φ→α` with a
      `b`-cost proof of `φ` yields an `(a+b+|α|)`-cost proof of `α`. -/
  | axKf {a b c k : Nat} (φ α : F) :
      a + b + α.size ≤ c →
      (F.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ k →
      Prov k (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
  /-- Bounded Inner Necessitation (four): boxing an `a`-cost proof costs `a + |□_a φ|`. -/
  | four {a b k : Nat} (φ : F) :
      a + (F.box a φ).size ≤ b →
      (F.impl (.box a φ) (.box b (.box a φ))).size ≤ k →
      Prov k (.impl (.box a φ) (.box b (.box a φ)))
  /-- Löb-fixpoint leg forward, GATED on the Löb premise and CHARGING its transcript (conservative —
      matches the engine's exclusion-invariant gate; the chain still closes, see kill-criterion). -/
  | diagF {pm fb g k : Nat} (t : F) :
      Prov pm (.impl (.box fb t) t) →
      pm + (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k →
      Prov k (.impl (.diag g t) (.impl (.box g (.diag g t)) t))
  /-- Löb-fixpoint leg backward (same gate + charge). -/
  | diagB {pm fb g k : Nat} (t : F) :
      Prov pm (.impl (.box fb t) t) →
      pm + (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k →
      Prov k (.impl (.impl (.box g (.diag g t)) t) (.diag g t))
  /-- implication transitivity (charged composition). -/
  | implTrans {m₁ m₂ k : Nat} (φ ψ χ : F) :
      Prov m₁ (.impl φ ψ) → Prov m₂ (.impl ψ χ) →
      m₁ + m₂ + (F.impl φ χ).size ≤ k → Prov k (.impl φ χ)
  /-- closed S-composition (charged). -/
  | impS2 {m₁ m₂ k : Nat} (φ ψ χ : F) :
      Prov m₁ (.impl φ (.impl ψ χ)) → Prov m₂ (.impl φ ψ) →
      m₁ + m₂ + (F.impl φ χ).size ≤ k → Prov k (.impl φ χ)

/-- Budget monotonicity — a ≤j-cost proof is a ≤k-cost proof (j ≤ k). The transcript model's
    analogue of `proofSearch_monotone`; every rule's output condition relaxes. -/
theorem Prov_mono : ∀ {j φ}, Prov j φ → ∀ {k}, j ≤ k → Prov k φ := by
  intro j φ h
  induction h with
  | app φ α h1 h2 hle _ _ =>
      intro k hjk; exact Prov.app φ α h1 h2 (Nat.le_trans hle hjk)
  | boxIntro φ hp hmg hle _ =>
      intro k hjk; exact Prov.boxIntro φ hp hmg (Nat.le_trans hle hjk)
  | boxMono φ hab hle => intro k hjk; exact Prov.boxMono φ hab (Nat.le_trans hle hjk)
  | axKf φ α hg hle => intro k hjk; exact Prov.axKf φ α hg (Nat.le_trans hle hjk)
  | four φ hg hle => intro k hjk; exact Prov.four φ hg (Nat.le_trans hle hjk)
  | diagF t hgate hle _ => intro k hjk; exact Prov.diagF t hgate (Nat.le_trans hle hjk)
  | diagB t hgate hle _ => intro k hjk; exact Prov.diagB t hgate (Nat.le_trans hle hjk)
  | implTrans φ ψ χ h1 h2 hle _ _ =>
      intro k hjk; exact Prov.implTrans φ ψ χ h1 h2 (Nat.le_trans hle hjk)
  | impS2 φ ψ χ h1 h2 hle _ _ =>
      intro k hjk; exact Prov.impS2 φ ψ χ h1 h2 (Nat.le_trans hle hjk)

/-! ## 3. Soundness (anti-cheat): box g φ ↦ Prov g φ; diag definitional (the internalized fixpoint). -/

def interp (V : Nat → Prop) : F → Prop
  | .atom n   => V n
  | .impl a b => interp V a → interp V b
  | .box g a  => Prov g a
  | .diag g t => Prov g (.diag g t) → interp V t

theorem Prov_sound (V : Nat → Prop) : ∀ {k φ}, Prov k φ → interp V φ := by
  intro k φ h
  induction h with
  | app φ α _ _ _ ih1 ih2 => exact ih1 ih2
  | boxIntro φ hp hmg _ _ => exact Prov_mono hp hmg
  | boxMono φ hab _ => exact fun hpa => Prov_mono hpa hab
  | axKf φ α hg _ => exact fun h1 h2 => Prov.app φ α h1 h2 hg
  | four φ hg _ => exact fun hpa => Prov.boxIntro φ hpa (Nat.le_refl _) hg
  | diagF t _ _ _ => exact fun hψ => hψ
  | diagB t _ _ _ => exact fun hctx => hctx
  | implTrans φ ψ χ _ _ _ ih1 ih2 => exact fun hφ => ih2 (ih1 hφ)
  | impS2 φ ψ χ _ _ _ ih1 ih2 => exact fun hφ => (ih1 hφ) (ih2 hφ)

theorem consistency (n : Nat) : ¬ Prov 0 (.atom n) :=
  fun h => Prov_sound (fun _ => False) h

/-! ## 4. `bloeb_transcript` — the Löb chain under transcript accounting.

Subscripts: `g` (the diagonal's box), `n₁` (boxing legF), `n₃ n₄ n₅` (K-distribution stages), `fb`
(the premise's box, = f k). Transcripts `c₁…c₁₄, m` explicit. The 21 side-conditions are hypotheses,
discharged by the kill-criterion below. -/

theorem bloeb_transcript (t : F) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ m : Nat)
    (hLoeb : Prov pm (.impl (.box fb t) t))
    -- legs (gate charged)
    (H1 : pm + (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ c₁)
    (H2 : pm + (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ c₂)
    -- boxIntro legF at subscript n₁
    (H3 : c₁ ≤ n₁)
    (H4 : c₁ + (F.box n₁ (.impl (.diag g t) (.impl (.box g (.diag g t)) t))).size ≤ c₃)
    -- axKf stage 1 (a=n₁, b=g, c=n₃; φ=ψ, α=ctx)
    (H5 : n₁ + g + (F.impl (.box g (.diag g t)) t).size ≤ n₃)
    (H6 : (F.impl (.box n₁ (.impl (.diag g t) (.impl (.box g (.diag g t)) t)))
            (.impl (.box g (.diag g t)) (.box n₃ (.impl (.box g (.diag g t)) t)))).size ≤ c₄)
    -- app (K1 to boxed legF)
    (H7 : c₄ + c₃ + (F.impl (.box g (.diag g t)) (.box n₃ (.impl (.box g (.diag g t)) t))).size ≤ c₅)
    -- axKf stage 2 (a=n₃, b=n₄, c=n₅; φ=□_gψ, α=t)
    (H8 : n₃ + n₄ + t.size ≤ n₅)
    (H9 : (F.impl (.box n₃ (.impl (.box g (.diag g t)) t))
            (.impl (.box n₄ (.box g (.diag g t))) (.box n₅ t))).size ≤ c₆)
    -- four (a=g, b=n₄)
    (H10 : g + (F.box g (.diag g t)).size ≤ n₄)
    (H11 : (F.impl (.box g (.diag g t)) (.box n₄ (.box g (.diag g t)))).size ≤ c₇)
    -- implTrans (h2 ; K2)
    (H12 : c₅ + c₆ + (F.impl (.box g (.diag g t))
            (.impl (.box n₄ (.box g (.diag g t))) (.box n₅ t))).size ≤ c₈)
    -- impS2 (h4 ; four)
    (H13 : c₈ + c₇ + (F.impl (.box g (.diag g t)) (.box n₅ t)).size ≤ c₉)
    -- boxMono n₅ → fb
    (H14 : n₅ ≤ fb)
    (H15 : (F.impl (.box n₅ t) (.box fb t)).size ≤ c₁₀)
    -- implTrans (h6 ; mono)
    (H16 : c₉ + c₁₀ + (F.impl (.box g (.diag g t)) (.box fb t)).size ≤ c₁₁)
    -- implTrans (h6' ; hLoeb)
    (H17 : c₁₁ + pm + (F.impl (.box g (.diag g t)) t).size ≤ c₁₂)
    -- app (legB to hE)
    (H18 : c₂ + c₁₂ + (F.diag g t).size ≤ c₁₃)
    -- boxIntro ψ at subscript g — THE crux condition: g must absorb ψ's whole proof transcript
    (H19 : c₁₃ ≤ g)
    (H20 : c₁₃ + (F.box g (.diag g t)).size ≤ c₁₄)
    -- final app (hE to □ψ)
    (H21 : c₁₂ + c₁₄ + t.size ≤ m) :
    Prov m t := by
  -- legs
  have legF : Prov c₁ (.impl (.diag g t) (.impl (.box g (.diag g t)) t)) :=
    Prov.diagF t hLoeb H1
  have legB : Prov c₂ (.impl (.impl (.box g (.diag g t)) t) (.diag g t)) :=
    Prov.diagB t hLoeb H2
  -- hnec : □_{n₁}(legF)
  have hnec : Prov c₃ (.box n₁ (.impl (.diag g t) (.impl (.box g (.diag g t)) t))) :=
    Prov.boxIntro _ legF H3 H4
  -- K1 : □_{n₁}(ψ→ctx) → (□_g ψ → □_{n₃} ctx)
  have hK1 : Prov c₄ (.impl (.box n₁ (.impl (.diag g t) (.impl (.box g (.diag g t)) t)))
      (.impl (.box g (.diag g t)) (.box n₃ (.impl (.box g (.diag g t)) t)))) :=
    Prov.axKf _ _ H5 H6
  -- h2 : □_g ψ → □_{n₃} ctx
  have h2 : Prov c₅ (.impl (.box g (.diag g t)) (.box n₃ (.impl (.box g (.diag g t)) t))) :=
    Prov.app _ _ hK1 hnec H7
  -- K2 : □_{n₃}(□_gψ→t) → (□_{n₄}□_gψ → □_{n₅} t)
  have hK2 : Prov c₆ (.impl (.box n₃ (.impl (.box g (.diag g t)) t))
      (.impl (.box n₄ (.box g (.diag g t))) (.box n₅ t))) :=
    Prov.axKf _ _ H8 H9
  -- hfour : □_g ψ → □_{n₄} □_g ψ
  have hfour : Prov c₇ (.impl (.box g (.diag g t)) (.box n₄ (.box g (.diag g t)))) :=
    Prov.four _ H10 H11
  -- h4 : □_g ψ → (□_{n₄}□_gψ → □_{n₅} t)
  have h4 : Prov c₈ (.impl (.box g (.diag g t))
      (.impl (.box n₄ (.box g (.diag g t))) (.box n₅ t))) :=
    Prov.implTrans _ _ _ h2 hK2 H12
  -- h6 : □_g ψ → □_{n₅} t
  have h6 : Prov c₉ (.impl (.box g (.diag g t)) (.box n₅ t)) :=
    Prov.impS2 _ _ _ h4 hfour H13
  -- hmono : □_{n₅} t → □_{fb} t   (UPWARD — sound; the piece the conclusion-cost model never needed)
  have hmono : Prov c₁₀ (.impl (.box n₅ t) (.box fb t)) := Prov.boxMono _ H14 H15
  -- h6' : □_g ψ → □_{fb} t
  have h6' : Prov c₁₁ (.impl (.box g (.diag g t)) (.box fb t)) :=
    Prov.implTrans _ _ _ h6 hmono H16
  -- hE : □_g ψ → t
  have hE : Prov c₁₂ (.impl (.box g (.diag g t)) t) :=
    Prov.implTrans _ _ _ h6' hLoeb H17
  -- hF : ψ  (contains legB + hE — hence contains the premise's transcript)
  have hF : Prov c₁₃ (.diag g t) := Prov.app _ _ legB hE H18
  -- hG : □_g ψ  — requires H19 : c₁₃ ≤ g (the g ≻ ψ-transcript condition)
  have hG : Prov c₁₄ (.box g (.diag g t)) := Prov.boxIntro _ hF H19 H20
  exact Prov.app _ _ hE hG H21

/-! ## 5. KILL-CRITERION — for `f = id`, O(log k)-transcript premises, O(log k)-size targets, the
chain closes for all large k. All budgets are multiples of `W := pm + size + log2 k + 8` = O(log k). -/

theorem pblt_transcript (t : Nat → F) (pm : Nat → Nat) (A B P Q : Nat)
    (hs : ∀ k, (t k).size ≤ A * Nat.log2 k + B)
    (hp : ∀ k, pm k ≤ P * Nat.log2 k + Q)
    (hLoeb : ∀ k, Prov (pm k) (.impl (.box k (t k)) (t k))) :
    ∃ K₀, ∀ k, k ≥ K₀ → ∃ m, Prov m (t k) := by
  obtain ⟨K₀, hK₀⟩ := PD.linear_log2_add_le (8192 * (P + A + 1)) (8192 * (Q + B + 8))
  refine ⟨K₀, fun k hk => ?_⟩
  -- the O(log k) unit W and the master headroom 8192·W ≤ k
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + (t k).size + Nat.log2 k + 8 := ⟨_, rfl⟩
  have hpk := hp k
  have hsk := hs k
  have hWk : 8192 * W ≤ k := by
    have h := hK₀ k hk
    have hexp : 8192 * ((P + A + 1) * Nat.log2 k) + 8192 * (Q + B + 8)
        = 8192 * (P + A + 1) * Nat.log2 k + 8192 * (Q + B + 8) := by ring
    -- W ≤ (P+A+1)·log2 k + (Q+B+8)
    have hWle : W ≤ (P + A + 1) * Nat.log2 k + (Q + B + 8) := by
      have : (P + A + 1) * Nat.log2 k = P * Nat.log2 k + A * Nat.log2 k + Nat.log2 k := by ring
      omega
    calc 8192 * W ≤ 8192 * ((P + A + 1) * Nat.log2 k + (Q + B + 8)) :=
          Nat.mul_le_mul_left _ hWle
      _ = 8192 * (P + A + 1) * Nat.log2 k + 8192 * (Q + B + 8) := by ring
      _ ≤ k := h
  -- every chosen subscript is ≤ k, so its numeral's log2 is ≤ log2 k
  have hg_k : 1024 * W ≤ k := by omega
  have hn₁_k : 32 * W ≤ k := by omega
  have hn₃_k : 2048 * W ≤ k := by omega
  have hn₄_k : 2048 * W ≤ k := by omega
  have hn₅_k : 8192 * W ≤ k := hWk
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 k := log2_mono hg_k
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 k := log2_mono hn₁_k
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 k := log2_mono hn₃_k
  have hl₄ : Nat.log2 (2048 * W) ≤ Nat.log2 k := log2_mono hn₄_k
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 k := log2_mono hn₅_k
  have hlfb : Nat.log2 k ≤ Nat.log2 k := Nat.le_refl _
  refine ⟨2048 * W, bloeb_transcript (t k) (pm k) k
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)   -- g n₁ n₃ n₄ n₅
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (832 * W) (2048 * W)
    (hLoeb k)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [F.size]); omega

/-! ## 6. T1 pre-check — the MUTUAL (two-leg) chain closes at EQUAL source budgets.

The engine's `mutual_loeb` (PrudentBot↔DupocBot etc.) currently composes the legs into
`□_k φP → φP` at the FULL subscript `k` and then runs Löb. Under transcript accounting that
factoring breaks: K-distribution pushes the intermediate box subscript ABOVE `k`, and downward
box-mono is unsound. THE FIX (validated here): derive the Löb premise at a LOWERED subscript
`fb := k − 64·V` (V = the O(log k) unit) — mono-UP `□_fb A → □_k A` feeds leg 1, and the
K-distribution then lands at `fb + O(log k) ≤ k`, which mono-UPs onto leg 2's `□_k B`. The result
`Prov O(log k) (□_fb A → A)` feeds the single-leg `bloeb_transcript` unchanged. So same-`k` bot
pairs (PrudentBot k vs DupocBot k) STILL cooperate — no bot re-parameterization needed in T1. -/

theorem mutual_pblt_transcript (Af Bf : Nat → F) (p₁ p₂ : Nat → Nat) (Ac Bc P Q : Nat)
    (hsA : ∀ k, (Af k).size ≤ Ac * Nat.log2 k + Bc)
    (hsB : ∀ k, (Bf k).size ≤ Ac * Nat.log2 k + Bc)
    (hp1 : ∀ k, p₁ k ≤ P * Nat.log2 k + Q)
    (hp2 : ∀ k, p₂ k ≤ P * Nat.log2 k + Q)
    (hL1 : ∀ k, Prov (p₁ k) (.impl (.box k (Af k)) (Bf k)))
    (hL2 : ∀ k, Prov (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ K₀, ∀ k, k ≥ K₀ → ∃ m, Prov m (Af k) := by
  obtain ⟨K₀, hK₀⟩ :=
    PD.linear_log2_add_le (131072 * (2*P + 2*Ac + 1)) (131072 * (2*Q + 2*Bc + 16))
  refine ⟨K₀, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hVk : 131072 * V ≤ k := by
    have h := hK₀ k hk
    have hVle : V ≤ (2*P + 2*Ac + 1) * Nat.log2 k + (2*Q + 2*Bc + 16) := by
      have hexp : (2*P + 2*Ac + 1) * Nat.log2 k
          = 2*(P * Nat.log2 k) + 2*(Ac * Nat.log2 k) + Nat.log2 k := by ring
      omega
    calc 131072 * V
        ≤ 131072 * ((2*P + 2*Ac + 1) * Nat.log2 k + (2*Q + 2*Bc + 16)) :=
          Nat.mul_le_mul_left _ hVle
      _ = 131072 * (2*P + 2*Ac + 1) * Nat.log2 k + 131072 * (2*Q + 2*Bc + 16) := by ring
      _ ≤ k := h
  -- the lowered premise subscript: fb + 64V = k (avoids Nat subtraction)
  obtain ⟨fb, hfb⟩ : ∃ fb, 64 * V + fb = k := Nat.le.dest (by omega)
  -- every subscript in play is ≤ k, so its numeral's log2 is ≤ log2 k
  have hLfb : Nat.log2 fb ≤ Nat.log2 k := log2_mono (by omega)
  have hLm : Nat.log2 (fb + 8*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLc : Nat.log2 (fb + 32*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn : Nat.log2 (16*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₁ : Nat.log2 (512*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLg : Nat.log2 (8192*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₃ : Nat.log2 (16384*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₅ : Nat.log2 (65536*V) ≤ Nat.log2 k := log2_mono (by omega)
  -- ── the lowered-premise derivation: Prov O(log k) (□_fb A → A) ──
  -- s1 : □_fb A → □_k A   (mono-UP onto leg 1's antecedent)
  have s1 : Prov (8*V) (.impl (.box fb (Af k)) (.box k (Af k))) :=
    Prov.boxMono _ (by omega) (by simp only [F.size]; omega)
  -- s2 : □_fb A → B
  have s2 : Prov (16*V) (.impl (.box fb (Af k)) (Bf k)) :=
    Prov.implTrans _ _ _ s1 (hL1 k) (by simp only [F.size]; omega)
  -- s3 : □_{16V}(□_fb A → B)
  have s3 : Prov (32*V) (.box (16*V) (.impl (.box fb (Af k)) (Bf k))) :=
    Prov.boxIntro _ s2 (by omega) (by simp only [F.size]; omega)
  -- s4 : K-distribution landing at fb + 32V (< k — THE fix)
  have s4 : Prov (16*V) (.impl (.box (16*V) (.impl (.box fb (Af k)) (Bf k)))
      (.impl (.box (fb + 8*V) (.box fb (Af k))) (.box (fb + 32*V) (Bf k)))) :=
    Prov.axKf _ _ (by omega) (by simp only [F.size]; omega)
  have s5 : Prov (64*V) (.impl (.box (fb + 8*V) (.box fb (Af k))) (.box (fb + 32*V) (Bf k))) :=
    Prov.app _ _ s4 s3 (by simp only [F.size]; omega)
  -- s6 : □_fb A → □_{fb+8V} □_fb A   (four)
  have s6 : Prov (16*V) (.impl (.box fb (Af k)) (.box (fb + 8*V) (.box fb (Af k)))) :=
    Prov.four _ (by simp only [F.size]; omega) (by simp only [F.size]; omega)
  have s7 : Prov (96*V) (.impl (.box fb (Af k)) (.box (fb + 32*V) (Bf k))) :=
    Prov.implTrans _ _ _ s6 s5 (by simp only [F.size]; omega)
  -- s8 : □_{fb+32V} B → □_k B   (mono-UP onto leg 2's antecedent)
  have s8 : Prov (8*V) (.impl (.box (fb + 32*V) (Bf k)) (.box k (Bf k))) :=
    Prov.boxMono _ (by omega) (by simp only [F.size]; omega)
  have s9 : Prov (128*V) (.impl (.box fb (Af k)) (.box k (Bf k))) :=
    Prov.implTrans _ _ _ s7 s8 (by simp only [F.size]; omega)
  -- s10 : □_fb A → A — the tight Löb premise at the LOWERED subscript, O(log k) transcript
  have s10 : Prov (160*V) (.impl (.box fb (Af k)) (Af k)) :=
    Prov.implTrans _ _ _ s9 (hL2 k) (by simp only [F.size]; omega)
  -- ── single-leg bloeb at fb, unchanged ──
  refine ⟨16384*V, bloeb_transcript (Af k) (160*V) fb
    (8192*V) (512*V) (16384*V) (16384*V) (65536*V)
    (256*V) (256*V) (1024*V) (512*V) (2048*V) (512*V) (512*V)
    (3072*V) (4096*V) (256*V) (5120*V) (6144*V) (7168*V) (8192*V) (16384*V)
    s10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [F.size]); omega

end T0
