import PrisonersDilemma.Base.Soundness

/-!
# Base/Loeb — bounded Löb inside `Pf` (the internalized PBLT chain)

`mutual_loeb` (the cross-bot fixpoint closer), `bloeb_engine` (the 14-step internalized
GL derivation, transcript-cost), `pblt_engine`/`pblt_engine_id` (Critch's PBLT as a
theorem), and the mutual engines `mutual_pblt_engine_id`/`_staggered` consumed by the
cross-bot cooperation theorems.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-! ### The mutual-Löb corollary — closes the cross-bot cooperation fixpoints

`mutual_loeb` derives a closed Löb premise from the two object transparency legs
(`legPD : □_kP A → B`, `legDP : □_kD B → A`). TRANSCRIPT-COST SHAPE (T0 §6,
`Research/Spikes/transcript/T0Transcript.lean`): the conclusion lives at a LOWERED box
subscript `fb` (strictly below the legs' source literals) — `□_fb A → □_kP A` feeds leg 1
via upward `boxMono`, the K-distribution lands at `c ≤ kD` which mono-UPs onto leg 2's box,
yielding `□_fb A → A` with an O(log k) transcript. `bloeb_engine`/`pblt_engine` then consume
the premise at `fb`. (The former same-subscript factoring `□_k φP → φP` is UNDERIVABLE under
transcript cost: K-distribution pushes the intermediate subscript above `k`, and downward
box-mono is unsound.) -/

/-- **Mutual / simultaneous bounded Löb premise** (object form) — ALL CONSTRUCTORS, no axiom.
    From `legPD : □_kP A → B` and `legDP : □_kD B → A`, build `□_fb A → A` at the lowered
    subscript `fb`. Free choices: `fb n m c` and the step transcripts `d₁…d₉`; the H-side
    conditions are what the consumers' omega blocks discharge (all O(log k)-shaped when the
    legs are transparency leaves). -/
theorem mutual_loeb (A B : Formula) (kP kD fb n m c pA pB : Nat)
    (d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ K : Nat)
    (legPD : Pf pA (.impl (.box kP A) B))
    (legDP : Pf pB (.impl (.box kD B) A))
    (H1 : fb ≤ kP)
    (H2 : (Formula.impl (.box fb A) (.box kP A)).size ≤ d₁)
    (H3 : d₁ + pA + (Formula.impl (.box fb A) B).size ≤ d₂)
    (H4 : d₂ ≤ n)
    (H5 : n + (Formula.box n (.impl (.box fb A) B)).size ≤ d₃)
    (H6 : n + m + B.size ≤ c)
    (H7 : (Formula.impl (.box n (.impl (.box fb A) B))
            (.impl (.box m (.box fb A)) (.box c B))).size ≤ d₄)
    (H8 : d₄ + d₃ + (Formula.impl (.box m (.box fb A)) (.box c B)).size ≤ d₅)
    (H9 : fb + (Formula.box fb A).size ≤ m)
    (H10 : (Formula.impl (.box fb A) (.box m (.box fb A))).size ≤ d₆)
    (H11 : d₆ + d₅ + (Formula.impl (.box fb A) (.box c B)).size ≤ d₇)
    (H12 : c ≤ kD)
    (H13 : (Formula.impl (.box c B) (.box kD B)).size ≤ d₈)
    (H14 : d₇ + d₈ + (Formula.impl (.box fb A) (.box kD B)).size ≤ d₉)
    (H15 : d₉ + pB + (Formula.impl (.box fb A) A).size ≤ K) :
    Pf K (.impl (.box fb A) A) := by
  -- s1 : □_fb A → □_kP A   (mono-UP onto leg 1's antecedent)
  have s1 : Pf d₁ (.impl (.box fb A) (.box kP A)) := Pf.boxMono fb kP d₁ A H1 H2
  -- s2 : □_fb A → B
  have s2 : Pf d₂ (.impl (.box fb A) B) :=
    Pf.implTrans _ _ _ d₁ pA s1 legPD H3
  -- s3 : □_n (□_fb A → B)
  have s3 : Pf d₃ (.box n (.impl (.box fb A) B)) :=
    Pf.boxIntro n d₃ _ (Pf_mono s2 H4) H5
  -- s4 : K-distribution landing at c ≤ kD (THE fix)
  have s4 : Pf d₄ (.impl (.box n (.impl (.box fb A) B))
      (.impl (.box m (.box fb A)) (.box c B))) :=
    Pf.axKf n m c d₄ (.box fb A) B H6 H7
  have s5 : Pf d₅ (.impl (.box m (.box fb A)) (.box c B)) :=
    Pf.mp d₄ d₃ _ _ s4 s3 H8
  -- s6 : □_fb A → □_m □_fb A   (four)
  have s6 : Pf d₆ (.impl (.box fb A) (.box m (.box fb A))) :=
    Pf.box4 fb m d₆ A H9 H10
  have s7 : Pf d₇ (.impl (.box fb A) (.box c B)) :=
    Pf.implTrans _ _ _ d₆ d₅ s6 s5 H11
  -- s8 : □_c B → □_kD B   (mono-UP onto leg 2's antecedent)
  have s8 : Pf d₈ (.impl (.box c B) (.box kD B)) := Pf.boxMono c kD d₈ B H12 H13
  have s9 : Pf d₉ (.impl (.box fb A) (.box kD B)) :=
    Pf.implTrans _ _ _ d₇ d₈ s7 s8 H14
  -- s10 : □_fb A → A — the tight Löb premise at the LOWERED subscript
  exact Pf.implTrans _ _ _ d₉ pB s9 legDP H15


/-! ## Bounded Löb INSIDE `Pf` — the internalized chain, TRANSCRIPT-COST (T0).

`bloeb_engine` runs Löb's derivation entirely in `Pf` from the TIGHT premise
`Pf pm (□_fb φ → φ)` — `pm` is the premise's honest transcript (O(log k) for the
consumers' single-leaf `searchBranch` / `mutual_loeb` premises; do NOT weaken it up to `k`,
the chain needs `pm ≪ fb`). The fixpoint sentence `ψ := .diag g φ` lives at the FREE subscript
`g ≺ fb`: under transcript cost ψ's proof CONTAINS the premise's proof, so `□`-ing ψ needs
`g` to absorb ψ's whole transcript (`H19 : c₁₃ ≤ g`) — Critch's `g ≺ f` dance, validated in
`Research/Spikes/transcript/T0Transcript.lean` (`bloeb_transcript`, axiom-free). The step
transcripts `c₁…c₁₄` and the box stages `n₁ n₃ n₄ n₅` are explicit; `pblt_engine` instantiates
everything as multiples of ONE O(log k) unit and discharges the 21 side-conditions by omega. -/

theorem bloeb_engine (φ : Formula) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ K : Nat)
    (hLoeb : Pf pm (.impl (.box fb φ) φ))
    (H1 : pm + (Formula.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)).size ≤ c₁)
    (H2 : pm + (Formula.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)).size ≤ c₂)
    (H3 : c₁ ≤ n₁)
    (H4 : n₁ + (Formula.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))).size ≤ c₃)
    (H5 : n₁ + g + (Formula.impl (.box g (.diag g φ)) φ).size ≤ n₃)
    (H6 : (Formula.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
            (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))).size ≤ c₄)
    (H7 : c₄ + c₃ + (Formula.impl (.box g (.diag g φ))
            (.box n₃ (.impl (.box g (.diag g φ)) φ))).size ≤ c₅)
    (H8 : n₃ + n₄ + φ.size ≤ n₅)
    (H9 : (Formula.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₆)
    (H10 : g + (Formula.box g (.diag g φ)).size ≤ n₄)
    (H11 : (Formula.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))).size ≤ c₇)
    (H12 : c₅ + c₆ + (Formula.impl (.box g (.diag g φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₈)
    (H13 : c₈ + c₇ + (Formula.impl (.box g (.diag g φ)) (.box n₅ φ)).size ≤ c₉)
    (H14 : n₅ ≤ fb)
    (H15 : (Formula.impl (.box n₅ φ) (.box fb φ)).size ≤ c₁₀)
    (H16 : c₉ + c₁₀ + (Formula.impl (.box g (.diag g φ)) (.box fb φ)).size ≤ c₁₁)
    (H17 : c₁₁ + pm + (Formula.impl (.box g (.diag g φ)) φ).size ≤ c₁₂)
    (H18 : c₂ + c₁₂ + (Formula.diag g φ).size ≤ c₁₃)
    (H19 : c₁₃ ≤ g)
    (H20 : g + (Formula.box g (.diag g φ)).size ≤ c₁₄)
    (H21 : c₁₂ + c₁₄ + φ.size ≤ K) :
    Pf K φ := by
  -- the two fixpoint legs (gated on hLoeb, charging its transcript)
  have legF : Pf c₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)) :=
    Pf.diagF pm fb g c₁ φ hLoeb H1
  have legB : Pf c₂ (.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)) :=
    Pf.diagB pm fb g c₂ φ hLoeb H2
  -- hnec : □_{n₁}(ψ → (□_gψ→φ))
  have hnec : Pf c₃ (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))) :=
    Pf.boxIntro n₁ c₃ _ (Pf_mono legF H3) H4
  -- hK1 : □_{n₁}(ψ→ctx) → (□_g ψ → □_{n₃} ctx)   [axKf stage 1]
  have hK1 : Pf c₄ (.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
      (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))) :=
    Pf.axKf n₁ g n₃ c₄ (.diag g φ) (.impl (.box g (.diag g φ)) φ) H5 H6
  -- h2 : □_g ψ → □_{n₃} ctx
  have h2 : Pf c₅ (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ))) :=
    Pf.mp c₄ c₃ _ _ hK1 hnec H7
  -- hK2 : □_{n₃}(□_gψ→φ) → (□_{n₄}□_gψ → □_{n₅} φ)   [axKf stage 2]
  have hK2 : Pf c₆ (.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    Pf.axKf n₃ n₄ n₅ c₆ (.box g (.diag g φ)) φ H8 H9
  -- hfour : □_g ψ → □_{n₄} □_g ψ
  have hfour : Pf c₇ (.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))) :=
    Pf.box4 g n₄ c₇ (.diag g φ) H10 H11
  -- h4 : □_g ψ → (□_{n₄}□_gψ → □_{n₅} φ)
  have h4 : Pf c₈ (.impl (.box g (.diag g φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    Pf.implTrans _ _ _ c₅ c₆ h2 hK2 H12
  -- h6 : □_g ψ → □_{n₅} φ   [impS2 — S-composition]
  have h6 : Pf c₉ (.impl (.box g (.diag g φ)) (.box n₅ φ)) :=
    Pf.impS2 _ _ _ c₈ c₇ c₉ h4 hfour H13
  -- hmono : □_{n₅} φ → □_{fb} φ   [upward boxMono — new with the transcript model]
  have hmono : Pf c₁₀ (.impl (.box n₅ φ) (.box fb φ)) :=
    Pf.boxMono n₅ fb c₁₀ φ H14 H15
  -- h6' : □_g ψ → □_{fb} φ
  have h6' : Pf c₁₁ (.impl (.box g (.diag g φ)) (.box fb φ)) :=
    Pf.implTrans _ _ _ c₉ c₁₀ h6 hmono H16
  -- hE : □_g ψ → φ
  have hE : Pf c₁₂ (.impl (.box g (.diag g φ)) φ) :=
    Pf.implTrans _ _ _ c₁₁ pm h6' hLoeb H17
  -- hF : ψ  (contains legB + hE — hence the premise's transcript; H19 : c₁₃ ≤ g absorbs it)
  have hF : Pf c₁₃ (.diag g φ) := Pf.mp c₂ c₁₂ _ _ legB hE H18
  have hG : Pf c₁₄ (.box g (.diag g φ)) :=
    Pf.boxIntro g c₁₄ _ (Pf_mono hF H19) H20
  exact Pf.mp c₁₂ c₁₄ _ _ hE hG H21

/-- **Parametric bounded Löb, INTERNAL** — the `PBLT` conclusion as a THEOREM, transcript-cost.
    Premise at its HONEST transcript `pm k` (O(log k) for all consumers — do not weaken to `f k`);
    ONE master headroom bound `8192·(pm k + (φ k).size + log2 (f k) + 8) ≤ f k` instantiates the
    whole chain as multiples of the unit `W := pm + |φ| + log2 (f k) + 8` (T0's assignment:
    `g = 1024·W` absorbs the fixpoint's proof, the largest stage is `n₅ = 8192·W ≤ f k`). -/
theorem pblt_engine (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + (φ k).size + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  -- every chosen subscript is ≤ f k, so its numeral's log2 is ≤ log2 (f k)
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, bloeb_engine (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [numCost, Formula.size]); omega

/-- **Consumer-facing PBLT** (`f = id`, the shape every bot theorem uses): tight Löb premise at
    its honest transcript `pm k` (what the `*_loeb_premise` lemmas produce — a single
    transparency leaf, `O(log k)` characters) + generous uniform `10·log2 k + 100` bounds on
    both the play-atom family and the premise transcript (covers every bot in the zoo).
    Replaces the former `PBLT` axiom at all call sites. -/
theorem pblt_engine_id (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (φ k) := by
  -- master bound: 8192·((100L+1000) + (100L+1000) + L + 8) = 1646592·L + 16449536 ≤ k, eventually.
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le 1646592 16449536
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ id pm (max k₁ Ksz)
    (fun k hk => hLoeb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    (by
      intro k hk
      have h1 := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
      have h2 := hφ k
      have h3 := hpm k
      show 8192 * (pm k + (φ k).size + Nat.log2 (id k) + 8) ≤ id k
      simp only [id]
      omega)
  exact ⟨k₂, hk₂⟩

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
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (Af k) := by
  -- master headroom: 131072·V ≤ k with V ≤ 401·log2 k + 4016.
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (131072 * 401) (131072 * 4016)
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hVk : 131072 * V ≤ k := by
    have h := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hVle : V ≤ 401 * Nat.log2 k + 4016 := by omega
    calc 131072 * V ≤ 131072 * (401 * Nat.log2 k + 4016) := Nat.mul_le_mul_left _ hVle
      _ = 131072 * 401 * Nat.log2 k + 131072 * 4016 := by ring
      _ ≤ k := h
  have hkk₁ : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  -- the lowered premise subscript: fb + 64V = k
  obtain ⟨fb, hfb⟩ : ∃ fb, 64 * V + fb = k := Nat.le.dest (by omega)
  have hLfb : Nat.log2 fb ≤ Nat.log2 k := log2_mono (by omega)
  have hLm : Nat.log2 (fb + 8*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLc : Nat.log2 (fb + 32*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn : Nat.log2 (16*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₁ : Nat.log2 (512*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLg : Nat.log2 (8192*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₃ : Nat.log2 (16384*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₅ : Nat.log2 (65536*V) ≤ Nat.log2 k := log2_mono (by omega)
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
  · (try simp only [numCost, Formula.size]); omega

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
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Pf m (Af k) := by
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (131072 * 401) (131072 * 4016)
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hkPk := hkP k; have hkPlogk := hkPlog k
  have hVk : 131072 * V ≤ k := by
    have h := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hVle : V ≤ 401 * Nat.log2 k + 4016 := by omega
    calc 131072 * V ≤ 131072 * (401 * Nat.log2 k + 4016) := Nat.mul_le_mul_left _ hVle
      _ = 131072 * 401 * Nat.log2 k + 131072 * 4016 := by ring
      _ ≤ k := h
  have hkk₁ : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  obtain ⟨fb, hfb⟩ : ∃ fb, 64 * V + fb = k := Nat.le.dest (by omega)
  have hLfb : Nat.log2 fb ≤ Nat.log2 k := log2_mono (by omega)
  have hLm : Nat.log2 (fb + 8*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLc : Nat.log2 (fb + 32*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn : Nat.log2 (16*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₁ : Nat.log2 (512*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLg : Nat.log2 (8192*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₃ : Nat.log2 (16384*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₅ : Nat.log2 (65536*V) ≤ Nat.log2 k := log2_mono (by omega)
  -- the lowered Löb premise (mutual_loeb, staggered legs): Pf (160V) (□_fb Af → Af)
  have s10 : Pf (160*V) (.impl (.box fb (Af k)) (Af k)) := by
    refine mutual_loeb (Af k) (Bf k) (kP k) k fb (16*V) (fb + 8*V) (fb + 32*V) (p₁ k) (p₂ k)
      (8*V) (16*V) (32*V) (16*V) (64*V) (16*V) (96*V) (8*V) (128*V) (160*V)
      (hL1 k hkk₁) (hL2 k hkk₁)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  refine ⟨32768*V, bloeb_engine (Af k) (160*V) fb
    (8192*V) (512*V) (16384*V) (16384*V) (65536*V)
    (256*V) (256*V) (1024*V) (512*V) (2048*V) (512*V) (512*V)
    (3072*V) (4096*V) (256*V) (5120*V) (6144*V) (7168*V) (16384*V) (32768*V)
    s10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [numCost, Formula.size]); omega

end PD.BaseTheorems
