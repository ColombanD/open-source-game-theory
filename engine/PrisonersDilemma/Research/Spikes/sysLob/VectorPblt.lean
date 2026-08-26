import PrisonersDilemma.Base.Loeb

/-!
# sysLob Spike A — vector bounded Löb (the Def-5 Route-A go/no-go)

**PROMOTED (Phase 4, 2026-08-13):** the glue (`compUnder`/`postUnder`/`swapAnte`),
the stage lemma and a SIZE-PARAMETRIC `vector2_full_pblt_engine` now live in
`Base/Loeb.lean` (`PD.BaseTheorems`). This file remains the historical spike
(hardcoded `100/1000` envelope); consume the engine versions.

`Research/Notes/TAUBOTS.md` (Def 5, shelved; tag `taubot-def5-research`). Def-5 σ-probing produces FULL-DEPENDENCY mutual
Löb premises — each sentence implied by boxes of ALL entangled sentences (its own
included), the curried shape `□_k φ₁ → (□_k φ₂ → … → φᵢ)` — where the existing engines
(`mutual_pblt_engine_id`/`_staggered`) consume only 2-CYCLES (`□A → B`, `□B → A`).

KILL CRITERION: the vector premises must close at `O(log k)` budgets. Route decision
inside: the ITERATED-UNARY reduction (Smoryński-style, no new `Formula` constructors)
vs an n-ary `Formula.diag`. This spike implements iterated-unary for n = 2 with full
dependencies (both self-loops), the atom every larger n composes from.

## The construction

1. **Glue** (§1): the positive implicational fragment is COMPLETE (`implK` + `implS` +
   `mp`/`implTrans`/`impS2`/`weakenImpl`, Family-B completion 2026-07-28), so
   composition UNDER a fixed antecedent (the B-combinator dance) is derivable:
   `compUnder`, `postUnder`, `swapAnte`. No new rules.
2. **The stage** (§2, the novel step): `loeb_premise_under_box` — from a
   full-dependency premise `⊢ □_u S → (□_w T → T)` build the COMPOUND Löb premise
   `□_fb C → C` for `C := □_u S → T`. Subscript discipline (the mutual_loeb lesson):
   `box4` applies to the PRE-LOWERED side box `□_u S` (`u` a free choice, NOT the
   source literal), so the K-distribution lands at `c = fb + m + |T| ≤ w`, mono-UP
   into the premise's self-box. Lowering the side antecedent is sound (contravariant
   position: `□_u S → □_k S` mono-UP pre-composes).
3. **Assembly** (§3): `vector2_full_pblt_engine` — premises
   `hL1 : □_k A → (□_k B → A)`, `hL2 : □_k A → (□_k B → B)`; stage `hL2` at side
   subscript `xa` → `bloeb_engine` → `⊢ C₁ = □_xa A → B`; swap+stage `hL1` at `yb`
   → `⊢ C₂ = □_yb B → A`; the two are a STAGGERED CYCLE, closed by `mutual_loeb` +
   `bloeb_engine` at `fb₃ ≤ xa`; finally `boxIntro` + `mp` recover `B`.

## Findings (2026-08-13 — SPIKE COMPLETE, all sections compile, zero sorry)

* **VERDICT: vector-Löb gate: PASS.** `vector2_full_pblt_engine` is a theorem on the
  live engine: from the two full-dependency premises (each sentence implied by boxes
  of BOTH, self-loops included) both sentences are provable past a threshold — the
  exact shape Def-5's σ-instance peel derivations produce. Everything at `O(log k)`.
* The implicational glue (`compUnder`/`postUnder`/`swapAnte`) is derivable — ZERO new
  constructors. Family-B completion (2026-07-28) is what made this possible: without
  `implS` the B-combinator dance has no basis.
* The stage lemma's subscript discipline is the one real design constraint: the side
  antecedent must be PRE-LOWERED (here to `xa = k − Θ(k)`) so that `box4`'s output
  and the K-distribution land BELOW the premise's self-box at `k`. Lowering is free
  (contravariant position, `boxMono` pre-composition). Both stage fixpoints share one
  `fb₁ = k − xa − 4V`.
* **Budget cascade** (the honest cost of iterated-unary): each Löb stage's OUTPUT
  transcript (`4096·W`) feeds the next stage's unit — V → W₁ = 2¹⁶V → W₂ = 2²⁰V →
  U = 2³⁴V → master `2⁵²·V ≤ k` (vs `2¹⁷·V` for the pure-cycle
  `mutual_pblt_engine_id`). Still `O(log k)`, so the `∃k₂` theorems are unaffected,
  but the constant grows like `2^(O(n))` in the number of elimination stages. Fine
  for the milestone σ-zoo (3 entangled instances); an n-ary `Formula.diag` (ONE
  bloeb for the whole vector) is the poly(n) refinement if a large zoo ever needs it.
* The hardcoded `100·log₂ k + 1000` hypotheses of the `_id` consumer engines do NOT
  fit the cascade's intermediate transcripts — but `bloeb_engine`/`mutual_loeb` are
  fully budget-parametric, so no engine change was needed; Phase 4's
  `vector_pblt_engine` must simply stay parametric too.
-/

open PD

namespace PD.SysLobSpike

open PD.BaseTheorems

/-! ## §1 Implicational glue (K/S fragment only) -/

/-- Pre-composition under a fixed antecedent: from `⊢ D → (M → N)` and `⊢ X → M`,
    conclude `⊢ D → (X → N)`. (The B-combinator, via `implK`/`implS`/`impS2`.) -/
theorem compUnder {D X M N : Formula} {a b : Nat} (K : Nat)
    (h₁ : Pf a (.impl D (.impl M N)))
    (h₂ : Pf b (.impl X M))
    (H : a + b + 32 * (D.size + X.size + M.size + N.size) + 128 ≤ K) :
    Pf K (.impl D (.impl X N)) := by
  -- s : ⊢ (M→N) → (X→(M→N))
  have s : Pf (2 * M.size + 2 * N.size + X.size + 4)
      (.impl (.impl M N) (.impl X (.impl M N))) :=
    .implK _ _ (by simp only [Formula.size]; omega)
  -- t : ⊢ D → (X→(M→N))
  have t : Pf (a + (2 * M.size + 2 * N.size + X.size + 4)
        + (D.size + X.size + M.size + N.size + 3))
      (.impl D (.impl X (.impl M N))) :=
    .implTrans _ _ _ _ _ h₁ s (by simp only [Formula.size]; omega)
  -- u : ⊢ (X→(M→N)) → ((X→M)→(X→N))
  have u : Pf (3 * X.size + 2 * M.size + 2 * N.size + 6)
      (.impl (.impl X (.impl M N)) (.impl (.impl X M) (.impl X N))) :=
    .implS _ _ _ (by simp only [Formula.size]; omega)
  -- v : ⊢ D → ((X→M)→(X→N))
  have v : Pf (a + 8 * X.size + 8 * M.size + 8 * N.size + 2 * D.size + 24)
      (.impl D (.impl (.impl X M) (.impl X N))) :=
    .implTrans _ _ _ _ _ t u (by simp only [Formula.size]; omega)
  -- w : ⊢ D → (X→M)
  have w : Pf (b + D.size + X.size + M.size + 2) (.impl D (.impl X M)) :=
    .weakenImpl _ _ _ h₂ (by simp only [Formula.size]; omega)
  -- res : ⊢ D → (X→N)
  exact .impS2 _ _ _ _ _ K v w (by simp only [Formula.size]; omega)

/-- Post-composition under two antecedents: from `⊢ D → (X → M)` and `⊢ M → N`,
    conclude `⊢ D → (X → N)`. -/
theorem postUnder {D X M N : Formula} {a b : Nat} (K : Nat)
    (h₁ : Pf a (.impl D (.impl X M)))
    (h₂ : Pf b (.impl M N))
    (H : a + b + 32 * (D.size + X.size + M.size + N.size) + 128 ≤ K) :
    Pf K (.impl D (.impl X N)) := by
  -- wk : ⊢ X → (M→N)
  have wk : Pf (b + X.size + M.size + N.size + 2) (.impl X (.impl M N)) :=
    .weakenImpl _ _ _ h₂ (by simp only [Formula.size]; omega)
  -- u : ⊢ (X→(M→N)) → ((X→M)→(X→N))
  have u : Pf (3 * X.size + 2 * M.size + 2 * N.size + 6)
      (.impl (.impl X (.impl M N)) (.impl (.impl X M) (.impl X N))) :=
    .implS _ _ _ (by simp only [Formula.size]; omega)
  -- m3 : ⊢ (X→M) → (X→N)
  have m3 : Pf (b + 7 * X.size + 5 * M.size + 5 * N.size + 16)
      (.impl (.impl X M) (.impl X N)) :=
    .mp _ _ _ _ u wk (by simp only [Formula.size]; omega)
  -- res : ⊢ D → (X→N)
  exact .implTrans _ _ _ _ _ h₁ m3 (by simp only [Formula.size]; omega)

/-- Antecedent swap (the C-combinator): from `⊢ φ → (ψ → χ)`, conclude
    `⊢ ψ → (φ → χ)`. -/
theorem swapAnte {φ ψ χ : Formula} {a : Nat} (K : Nat)
    (h : Pf a (.impl φ (.impl ψ χ)))
    (H : a + 32 * (φ.size + ψ.size + χ.size) + 128 ≤ K) :
    Pf K (.impl ψ (.impl φ χ)) := by
  -- a₁ : ⊢ ψ → (φ→ψ)
  have a₁ : Pf (φ.size + 2 * ψ.size + 2) (.impl ψ (.impl φ ψ)) :=
    .implK _ _ (by simp only [Formula.size]; omega)
  -- b₁ : ⊢ (φ→(ψ→χ)) → ((φ→ψ)→(φ→χ))
  have b₁ : Pf (3 * φ.size + 2 * ψ.size + 2 * χ.size + 6)
      (.impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ))) :=
    .implS _ _ _ (by simp only [Formula.size]; omega)
  -- b₂ : ⊢ (φ→ψ) → (φ→χ)
  have b₂ : Pf (a + 5 * φ.size + 3 * ψ.size + 3 * χ.size + 9)
      (.impl (.impl φ ψ) (.impl φ χ)) :=
    .mp _ _ _ _ b₁ h (by simp only [Formula.size]; omega)
  -- res : ⊢ ψ → (φ→χ)
  exact .implTrans _ _ _ _ _ a₁ b₂ (by simp only [Formula.size]; omega)

/-! ## §2 The stage: a compound Löb premise from a full-dependency premise -/

/-- **Löb under a boxed side-antecedent** — the Def-5 stage step. From the
    full-dependency premise `⊢ □_u S → (□_w T → T)` (side box at the FREE subscript
    `u`, self-box at the source subscript `w`), build the compound Löb premise
    `□_fb C → C` for `C := □_u S → T`, ready for `bloeb_engine`.

    Derivation, thread `D := □_fb C`:
    `axKf`: `D → (□_m (□_u S) → □_c T)`; `box4` on the SIDE box: `□_u S → □_m (□_u S)`;
    `compUnder` → `D → (□_u S → □_c T)`; `boxMono c ≤ w` + `postUnder` →
    `D → (□_u S → □_w T)`; lift the premise (`weakenImpl`) and S-distribute
    (`implS` + `implTrans` + `impS2`) → `D → (□_u S → T) = D → C`. -/
theorem loeb_premise_under_box (S T : Formula) (u w fb m c p K : Nat)
    (P : Pf p (.impl (.box u S) (.impl (.box w T) T)))
    (Hm : u + (Formula.box u S).size ≤ m)
    (Hc : fb + m + T.size ≤ c)
    (Hcw : c ≤ w)
    (HK : 1024 * ((Formula.box u S).size + T.size
        + numCost fb + numCost m + numCost c + numCost w + p + 8) ≤ K) :
    Pf K (.impl (.box fb (.impl (.box u S) T)) (.impl (.box u S) T)) := by
  -- base unit for the budget ladder
  obtain ⟨base, hbase⟩ : ∃ base, base = (Formula.box u S).size + T.size
      + numCost fb + numCost m + numCost c + numCost w + p + 8 := ⟨_, rfl⟩
  -- s₁ : ⊢ □_fb C → (□_m (□_u S) → □_c T)   [axKf]
  have s₁ : Pf (4 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box m (.box u S)) (.box c T))) :=
    .axKf fb m c _ _ _ Hc (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₂ : ⊢ □_u S → □_m (□_u S)   [box4 on the SIDE box]
  have s₂ : Pf (4 * base) (.impl (.box u S) (.box m (.box u S))) :=
    .box4 u m _ _ Hm (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₃ : ⊢ □_fb C → (□_u S → □_c T)
  have s₃ : Pf (256 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) (.box c T))) :=
    compUnder _ s₁ s₂ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₄ : ⊢ □_c T → □_w T   [mono-UP into the premise's self-box]
  have s₄ : Pf (4 * base) (.impl (.box c T) (.box w T)) :=
    .boxMono c w _ _ Hcw (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₅ : ⊢ □_fb C → (□_u S → □_w T)
  have s₅ : Pf (512 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) (.box w T))) :=
    postUnder _ s₃ s₄ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₆ : ⊢ □_fb C → (□_u S → (□_w T → T))   [lift the premise]
  have s₆ : Pf (8 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) (.impl (.box w T) T))) :=
    .weakenImpl _ _ _ P (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₇ : ⊢ (□_u S → (□_w T → T)) → ((□_u S → □_w T) → (□_u S → T))
  have s₇ : Pf (4 * base) (.impl (.impl (.box u S) (.impl (.box w T) T))
      (.impl (.impl (.box u S) (.box w T)) (.impl (.box u S) T))) :=
    .implS _ _ _ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₈ : ⊢ □_fb C → ((□_u S → □_w T) → (□_u S → T))
  have s₈ : Pf (16 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.impl (.box u S) (.box w T)) (.impl (.box u S) T))) :=
    .implTrans _ _ _ _ _ s₆ s₇ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  -- s₉ : ⊢ □_fb C → (□_u S → T) = □_fb C → C
  have s₉ : Pf (1024 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) T)) :=
    .impS2 _ _ _ _ _ _ s₈ s₅ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  exact Pf_mono s₉ (by omega)

/-! ## §3 Assembly: n = 2 full-dependency vector PBLT (both self-loops) -/

/-- **Vector PBLT, n = 2, FULL dependencies** — the Def-5 shape: each sentence implied
    by boxes of BOTH sentences (its own included). Neither existing mutual engine
    consumes this (they need 2-cycles). Iterated-unary assembly: stage `hL2` at the
    side subscript `xa` and Löb the compound `C₁ = □_xa A → B`; swap + stage `hL1`
    for `C₂ = □_xa B → A`; the two compound theorems are a STAGGERED CYCLE closed by
    `mutual_loeb` + `bloeb_engine`; `boxIntro` + `mp` then recover `B`. -/
theorem vector2_full_pblt_engine (Af Bf : Nat → Formula) (p₁ p₂ : Nat → Nat) (k₁ : Nat)
    (hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000)
    (hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000)
    (hp1 : ∀ k, p₁ k ≤ 100 * Nat.log2 k + 1000)
    (hp2 : ∀ k, p₂ k ≤ 100 * Nat.log2 k + 1000)
    (hL1 : ∀ k, k > k₁ →
      Pf (p₁ k) (.impl (.box k (Af k)) (.impl (.box k (Bf k)) (Af k))))
    (hL2 : ∀ k, k > k₁ →
      Pf (p₂ k) (.impl (.box k (Af k)) (.impl (.box k (Bf k)) (Bf k)))) :
    ∃ k₂, ∀ k, k > k₂ → (∃ m, Pf m (Af k)) ∧ (∃ m, Pf m (Bf k)) := by
  -- master headroom: 2⁵²·V ≤ k with V ≤ 401·log2 k + 4016
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (4503599627370496 * 401) (4503599627370496 * 4016)
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hVk : 4503599627370496 * V ≤ k := by
    have h := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hVle : V ≤ 401 * Nat.log2 k + 4016 := by omega
    calc 4503599627370496 * V ≤ 4503599627370496 * (401 * Nat.log2 k + 4016) :=
          Nat.mul_le_mul_left _ hVle
      _ = 4503599627370496 * 401 * Nat.log2 k + 4503599627370496 * 4016 := by ring
      _ ≤ k := h
  have hkk₁ : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  -- units: W₁/W₂ for the two compound bloebs, U for the mutual closer, xa the side subscript
  obtain ⟨W₁, hW₁⟩ : ∃ W₁, W₁ = 65536 * V := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂, W₂ = 1048576 * V := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = 17179869184 * V := ⟨_, rfl⟩
  obtain ⟨xa, hxa⟩ : ∃ xa, xa = 131072 * U := ⟨_, rfl⟩
  -- the shared stage fixpoint subscript: fb₁ = k − xa − 4V
  obtain ⟨fb₁, hfb₁⟩ : ∃ fb₁, xa + 4 * V + fb₁ = k := Nat.le.dest (by omega)
  -- the mutual fixpoint subscript: fb₃ = xa − 64U
  obtain ⟨fb₃, hfb₃⟩ : ∃ fb₃, 64 * U + fb₃ = xa := Nat.le.dest (by omega)
  -- log2 atoms (each subscript ≤ k)
  have hlxa : Nat.log2 xa ≤ Nat.log2 k := log2_mono (by omega)
  have hlfb₁ : Nat.log2 fb₁ ≤ Nat.log2 k := log2_mono (by omega)
  have hlfb₃ : Nat.log2 fb₃ ≤ Nat.log2 k := log2_mono (by omega)
  have hlm₁ : Nat.log2 (xa + 2 * V) ≤ Nat.log2 k := log2_mono (by omega)
  have hlc₁ : Nat.log2 (fb₁ + xa + 3 * V) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₁a : Nat.log2 (32 * W₁) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₁b : Nat.log2 (1024 * W₁) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₁c : Nat.log2 (2048 * W₁) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₁d : Nat.log2 (8192 * W₁) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₂a : Nat.log2 (32 * W₂) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₂b : Nat.log2 (1024 * W₂) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₂c : Nat.log2 (2048 * W₂) ≤ Nat.log2 k := log2_mono (by omega)
  have hlW₂d : Nat.log2 (8192 * W₂) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUa : Nat.log2 (16 * U) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUb : Nat.log2 (512 * U) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUc : Nat.log2 (8192 * U) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUd : Nat.log2 (16384 * U) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUe : Nat.log2 (65536 * U) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUm : Nat.log2 (fb₃ + 8 * U) ≤ Nat.log2 k := log2_mono (by omega)
  have hlUc' : Nat.log2 (fb₃ + 32 * U) ≤ Nat.log2 k := log2_mono (by omega)
  -- ── Stage 1: C₁ := □_xa A → B ─────────────────────────────────────────────
  -- pre-lower hL2's side antecedent to xa
  have mono₁ : Pf (8 * V) (.impl (.box xa (Af k)) (.box k (Af k))) :=
    .boxMono xa k _ _ (by omega) (by simp only [Formula.size, numCost]; omega)
  have P₂' : Pf (p₂ k + 16 * V)
      (.impl (.box xa (Af k)) (.impl (.box k (Bf k)) (Bf k))) :=
    .implTrans _ _ _ _ _ mono₁ (hL2 k hkk₁)
      (by simp only [Formula.size, numCost]; omega)
  have stage₁ : Pf (32768 * V)
      (.impl (.box fb₁ (.impl (.box xa (Af k)) (Bf k)))
        (.impl (.box xa (Af k)) (Bf k))) :=
    loeb_premise_under_box (Af k) (Bf k) xa k fb₁ (xa + 2 * V) (fb₁ + xa + 3 * V)
      (p₂ k + 16 * V) _ P₂'
      (by simp only [Formula.size, numCost]; omega)
      (by omega) (by omega)
      (by simp only [Formula.size, numCost]; omega)
  have hC₁ : Pf (4096 * W₁) (.impl (.box xa (Af k)) (Bf k)) := by
    refine bloeb_engine _ (32768 * V) fb₁ (1024 * W₁) (32 * W₁) (2048 * W₁)
      (2048 * W₁) (8192 * W₁) (16 * W₁) (16 * W₁) (64 * W₁) (32 * W₁) (128 * W₁)
      (32 * W₁) (16 * W₁) (256 * W₁) (512 * W₁) (16 * W₁) (640 * W₁) (704 * W₁)
      (768 * W₁) (2048 * W₁) (4096 * W₁) stage₁
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  -- ── Stage 2: C₂ := □_xa B → A ─────────────────────────────────────────────
  have swap₁ : Pf (p₁ k + 192 * V)
      (.impl (.box k (Bf k)) (.impl (.box k (Af k)) (Af k))) :=
    swapAnte _ (hL1 k hkk₁) (by simp only [Formula.size, numCost]; omega)
  have mono₂ : Pf (8 * V) (.impl (.box xa (Bf k)) (.box k (Bf k))) :=
    .boxMono xa k _ _ (by omega) (by simp only [Formula.size, numCost]; omega)
  have P₁' : Pf (p₁ k + 224 * V)
      (.impl (.box xa (Bf k)) (.impl (.box k (Af k)) (Af k))) :=
    .implTrans _ _ _ _ _ mono₂ swap₁
      (by simp only [Formula.size, numCost]; omega)
  have stage₂ : Pf (524288 * V)
      (.impl (.box fb₁ (.impl (.box xa (Bf k)) (Af k)))
        (.impl (.box xa (Bf k)) (Af k))) :=
    loeb_premise_under_box (Bf k) (Af k) xa k fb₁ (xa + 2 * V) (fb₁ + xa + 3 * V)
      (p₁ k + 224 * V) _ P₁'
      (by simp only [Formula.size, numCost]; omega)
      (by omega) (by omega)
      (by simp only [Formula.size, numCost]; omega)
  have hC₂ : Pf (4096 * W₂) (.impl (.box xa (Bf k)) (Af k)) := by
    refine bloeb_engine _ (524288 * V) fb₁ (1024 * W₂) (32 * W₂) (2048 * W₂)
      (2048 * W₂) (8192 * W₂) (16 * W₂) (16 * W₂) (64 * W₂) (32 * W₂) (128 * W₂)
      (32 * W₂) (16 * W₂) (256 * W₂) (512 * W₂) (16 * W₂) (640 * W₂) (704 * W₂)
      (768 * W₂) (2048 * W₂) (4096 * W₂) stage₂
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  -- ── The mutual closer: C₁/C₂ are a staggered cycle at (xa, xa) ────────────
  have s10 : Pf (160 * U) (.impl (.box fb₃ (Af k)) (Af k)) := by
    refine mutual_loeb (Af k) (Bf k) xa xa fb₃ (16 * U) (fb₃ + 8 * U) (fb₃ + 32 * U)
      (4096 * W₁) (4096 * W₂) (8 * U) (16 * U) (32 * U) (16 * U) (64 * U) (16 * U)
      (96 * U) (8 * U) (128 * U) (160 * U) hC₁ hC₂
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  have hA : Pf (32768 * U) (Af k) := by
    refine bloeb_engine _ (160 * U) fb₃ (8192 * U) (512 * U) (16384 * U) (16384 * U)
      (65536 * U) (256 * U) (256 * U) (1024 * U) (512 * U) (2048 * U) (512 * U)
      (512 * U) (3072 * U) (4096 * U) (256 * U) (5120 * U) (6144 * U) (7168 * U)
      (16384 * U) (32768 * U) s10
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  -- ── recover B: box A up to xa, mp through C₁ ──────────────────────────────
  have hBoxA : Pf (xa + 4 * V) (.box xa (Af k)) :=
    .boxIntro xa _ _ (Pf_mono hA (by omega))
      (by simp only [Formula.size, numCost]; omega)
  exact ⟨⟨32768 * U, hA⟩,
    ⟨2 * xa, .mp _ _ _ _ hC₁ hBoxA (by omega)⟩⟩

-- Axiom footprint: must list only Lean's 3 standard axioms (propext, Classical.choice,
-- Quot.sound) — the engine has ZERO project axioms and this spike must add none.
#print axioms vector2_full_pblt_engine

end PD.SysLobSpike
