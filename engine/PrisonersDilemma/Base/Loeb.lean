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

/-- **PBLT, budget-carrying**: identical to `pblt_engine`, but it also reports that
    the fixpoint's transcript fits in HALF the budget. The engine picks
    `m = 4096·W` while its own size hypothesis forces `8192·W ≤ f k`, so this costs
    nothing extra — it just stops throwing the bound away.

    Needed whenever a Löb bit has to be RE-CERTIFIED at budget `k` (a `proofSearch k`
    gate), rather than merely consumed as an `∃ m` play witness. -/
theorem pblt_engine_bounded (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ f k ∧ Pf m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + (φ k).size + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, by omega, bloeb_engine (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [numCost, Formula.size]); omega

/-- `pblt_engine_bounded` at `f = id`: the fixpoint holds at a budget ≤ k/2. -/
theorem pblt_engine_id_bounded (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Pf (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, 2 * m ≤ k ∧ Pf m (φ k) := by
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le 1646592 16449536
  obtain ⟨k₂, hk₂⟩ := pblt_engine_bounded φ id pm (max k₁ Ksz)
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

/-! ## The VECTOR engines — full-dependency mutual Löb (Def-5, Phase 4, 2026-08-13)

Promoted from `Research/Spikes/sysLob/VectorPblt.lean` (Spike A, the Route-A
go/no-go — Def 5 is shelved, see `Research/Notes/TAUBOTS.md`; tag `taubot-def5-research`). Def-5 σ-instances produce
FULL-DEPENDENCY premises — each sentence implied by boxes of ALL entangled
sentences, its own included (`□_k A → (□_k B → A)`), a shape the cycle engines
above cannot consume. The iterated-unary reduction closes them with ZERO new
constructors: the Family-B completion (`implK`/`implS`, 2026-07-28) makes the
B-combinator glue derivable, and the stage lemma turns a full-dependency premise
into a compound Löb premise for `bloeb_engine`.

SIZE-PARAMETRIC on purpose: the budget cascade (each stage's `4096·W` output
transcript feeds the next stage's unit) puts intermediate transcripts far above
the `100·log₂ k + 1000` envelope of the `_id` wrappers, so the vector engine's
envelope `C·log₂ k + D` is a parameter — Phase-5 consumers instantiate `C`/`D`
with their zoo's concrete constants. Threshold constants are `2^(O(n))` in the
number of elimination stages (master `2⁵²·V ≤ k` here, vs `2¹⁷·V` for the cycle
engines): fine for a fixed zoo; an n-ary `Formula.diag` is the poly(n)
refinement if ever needed. -/

/-- Pre-composition under a fixed antecedent: from `⊢ D → (M → N)` and `⊢ X → M`,
    conclude `⊢ D → (X → N)`. (The B-combinator, via `implK`/`implS`/`impS2`.) -/
theorem compUnder {D X M N : Formula} {a b : Nat} (K : Nat)
    (h₁ : Pf a (.impl D (.impl M N)))
    (h₂ : Pf b (.impl X M))
    (H : a + b + 32 * (D.size + X.size + M.size + N.size) + 128 ≤ K) :
    Pf K (.impl D (.impl X N)) := by
  have s : Pf (2 * M.size + 2 * N.size + X.size + 4)
      (.impl (.impl M N) (.impl X (.impl M N))) :=
    .implK _ _ (by simp only [Formula.size]; omega)
  have t : Pf (a + (2 * M.size + 2 * N.size + X.size + 4)
        + (D.size + X.size + M.size + N.size + 3))
      (.impl D (.impl X (.impl M N))) :=
    .implTrans _ _ _ _ _ h₁ s (by simp only [Formula.size]; omega)
  have u : Pf (3 * X.size + 2 * M.size + 2 * N.size + 6)
      (.impl (.impl X (.impl M N)) (.impl (.impl X M) (.impl X N))) :=
    .implS _ _ _ (by simp only [Formula.size]; omega)
  have v : Pf (a + 8 * X.size + 8 * M.size + 8 * N.size + 2 * D.size + 24)
      (.impl D (.impl (.impl X M) (.impl X N))) :=
    .implTrans _ _ _ _ _ t u (by simp only [Formula.size]; omega)
  have w : Pf (b + D.size + X.size + M.size + 2) (.impl D (.impl X M)) :=
    .weakenImpl _ _ _ h₂ (by simp only [Formula.size]; omega)
  exact .impS2 _ _ _ _ _ K v w (by simp only [Formula.size]; omega)

/-- Post-composition under two antecedents: from `⊢ D → (X → M)` and `⊢ M → N`,
    conclude `⊢ D → (X → N)`. -/
theorem postUnder {D X M N : Formula} {a b : Nat} (K : Nat)
    (h₁ : Pf a (.impl D (.impl X M)))
    (h₂ : Pf b (.impl M N))
    (H : a + b + 32 * (D.size + X.size + M.size + N.size) + 128 ≤ K) :
    Pf K (.impl D (.impl X N)) := by
  have wk : Pf (b + X.size + M.size + N.size + 2) (.impl X (.impl M N)) :=
    .weakenImpl _ _ _ h₂ (by simp only [Formula.size]; omega)
  have u : Pf (3 * X.size + 2 * M.size + 2 * N.size + 6)
      (.impl (.impl X (.impl M N)) (.impl (.impl X M) (.impl X N))) :=
    .implS _ _ _ (by simp only [Formula.size]; omega)
  have m3 : Pf (b + 7 * X.size + 5 * M.size + 5 * N.size + 16)
      (.impl (.impl X M) (.impl X N)) :=
    .mp _ _ _ _ u wk (by simp only [Formula.size]; omega)
  exact .implTrans _ _ _ _ _ h₁ m3 (by simp only [Formula.size]; omega)

/-- Antecedent swap (the C-combinator): from `⊢ φ → (ψ → χ)`, conclude
    `⊢ ψ → (φ → χ)`. -/
theorem swapAnte {φ ψ χ : Formula} {a : Nat} (K : Nat)
    (h : Pf a (.impl φ (.impl ψ χ)))
    (H : a + 32 * (φ.size + ψ.size + χ.size) + 128 ≤ K) :
    Pf K (.impl ψ (.impl φ χ)) := by
  have a₁ : Pf (φ.size + 2 * ψ.size + 2) (.impl ψ (.impl φ ψ)) :=
    .implK _ _ (by simp only [Formula.size]; omega)
  have b₁ : Pf (3 * φ.size + 2 * ψ.size + 2 * χ.size + 6)
      (.impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ))) :=
    .implS _ _ _ (by simp only [Formula.size]; omega)
  have b₂ : Pf (a + 5 * φ.size + 3 * ψ.size + 3 * χ.size + 9)
      (.impl (.impl φ ψ) (.impl φ χ)) :=
    .mp _ _ _ _ b₁ h (by simp only [Formula.size]; omega)
  exact .implTrans _ _ _ _ _ a₁ b₂ (by simp only [Formula.size]; omega)

/-- **Löb under a boxed side-antecedent** — the Def-5 stage step. From the
    full-dependency premise `⊢ □_u S → (□_w T → T)` (side box at the FREE
    subscript `u`, self-box at the source subscript `w`), build the compound Löb
    premise `□_fb C → C` for `C := □_u S → T`, ready for `bloeb_engine`.
    Subscript discipline (the `mutual_loeb` lesson, one level up): `box4` applies
    to the PRE-LOWERED side box, so the K-distribution lands at
    `c = fb + m + |T| ≤ w`, mono-UP into the premise's self-box. Lowering the
    side antecedent is free — contravariant position, `boxMono` pre-composes. -/
theorem loeb_premise_under_box (S T : Formula) (u w fb m c p K : Nat)
    (P : Pf p (.impl (.box u S) (.impl (.box w T) T)))
    (Hm : u + (Formula.box u S).size ≤ m)
    (Hc : fb + m + T.size ≤ c)
    (Hcw : c ≤ w)
    (HK : 1024 * ((Formula.box u S).size + T.size
        + numCost fb + numCost m + numCost c + numCost w + p + 8) ≤ K) :
    Pf K (.impl (.box fb (.impl (.box u S) T)) (.impl (.box u S) T)) := by
  obtain ⟨base, hbase⟩ : ∃ base, base = (Formula.box u S).size + T.size
      + numCost fb + numCost m + numCost c + numCost w + p + 8 := ⟨_, rfl⟩
  have s₁ : Pf (4 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box m (.box u S)) (.box c T))) :=
    .axKf fb m c _ _ _ Hc (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₂ : Pf (4 * base) (.impl (.box u S) (.box m (.box u S))) :=
    .box4 u m _ _ Hm (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₃ : Pf (256 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) (.box c T))) :=
    compUnder _ s₁ s₂ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₄ : Pf (4 * base) (.impl (.box c T) (.box w T)) :=
    .boxMono c w _ _ Hcw (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₅ : Pf (512 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) (.box w T))) :=
    postUnder _ s₃ s₄ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₆ : Pf (8 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) (.impl (.box w T) T))) :=
    .weakenImpl _ _ _ P (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₇ : Pf (4 * base) (.impl (.impl (.box u S) (.impl (.box w T) T))
      (.impl (.impl (.box u S) (.box w T)) (.impl (.box u S) T))) :=
    .implS _ _ _ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₈ : Pf (16 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.impl (.box u S) (.box w T)) (.impl (.box u S) T))) :=
    .implTrans _ _ _ _ _ s₆ s₇ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  have s₉ : Pf (1024 * base) (.impl (.box fb (.impl (.box u S) T))
      (.impl (.box u S) T)) :=
    .impS2 _ _ _ _ _ _ s₈ s₅ (by simp only [Formula.size, numCost] at hbase ⊢; omega)
  exact Pf_mono s₉ (by omega)

/-- **Vector PBLT, n = 2, FULL dependencies, SIZE-PARAMETRIC** — the Def-5
    consumer shape: each sentence implied by boxes of BOTH sentences (self-loops
    included), sizes and premise transcripts within an ARBITRARY envelope
    `C·log₂ k + D` (do NOT specialize to the `_id` wrappers' `100/1000` — Def-5
    probe atoms carry whole systems). Assembly: stage `hL2` at side subscript
    `xa` and Löb the compound `C₁ = □_xa A → B`; swap + stage `hL1` for
    `C₂ = □_xa B → A`; the compounds are a staggered CYCLE closed by
    `mutual_loeb` + `bloeb_engine`; `boxIntro` + `mp` recover `B`. -/
theorem vector2_full_pblt_engine (Af Bf : Nat → Formula) (p₁ p₂ : Nat → Nat)
    (k₁ C D : Nat)
    (hsA : ∀ k, (Af k).size ≤ C * Nat.log2 k + D)
    (hsB : ∀ k, (Bf k).size ≤ C * Nat.log2 k + D)
    (hp1 : ∀ k, p₁ k ≤ C * Nat.log2 k + D)
    (hp2 : ∀ k, p₂ k ≤ C * Nat.log2 k + D)
    (hL1 : ∀ k, k > k₁ →
      Pf (p₁ k) (.impl (.box k (Af k)) (.impl (.box k (Bf k)) (Af k))))
    (hL2 : ∀ k, k > k₁ →
      Pf (p₂ k) (.impl (.box k (Af k)) (.impl (.box k (Bf k)) (Bf k)))) :
    ∃ k₂, ∀ k, k > k₂ → (∃ m, Pf m (Af k)) ∧ (∃ m, Pf m (Bf k)) := by
  -- master headroom: 2⁵²·V ≤ k with V ≤ (4C+1)·log2 k + (4D+16)
  obtain ⟨Ksz, hKsz⟩ :=
    linear_log2_add_le (4503599627370496 * (4 * C + 1)) (4503599627370496 * (4 * D + 16))
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hVk : 4503599627370496 * V ≤ k := by
    have h := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hVle : V ≤ (4 * C + 1) * Nat.log2 k + (4 * D + 16) := by
      -- expose the nonlinear atom `C * log2 k` to omega by expanding the coefficient
      have hexp : (4 * C + 1) * Nat.log2 k
          = C * Nat.log2 k + C * Nat.log2 k + C * Nat.log2 k + C * Nat.log2 k
            + Nat.log2 k := by ring
      omega
    calc 4503599627370496 * V
        ≤ 4503599627370496 * ((4 * C + 1) * Nat.log2 k + (4 * D + 16)) :=
          Nat.mul_le_mul_left _ hVle
      _ = 4503599627370496 * (4 * C + 1) * Nat.log2 k
          + 4503599627370496 * (4 * D + 16) := by ring
      _ ≤ k := h
  have hkk₁ : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  obtain ⟨W₁, hW₁⟩ : ∃ W₁, W₁ = 65536 * V := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂, W₂ = 1048576 * V := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = 17179869184 * V := ⟨_, rfl⟩
  obtain ⟨xa, hxa⟩ : ∃ xa, xa = 131072 * U := ⟨_, rfl⟩
  obtain ⟨fb₁, hfb₁⟩ : ∃ fb₁, xa + 4 * V + fb₁ = k := Nat.le.dest (by omega)
  obtain ⟨fb₃, hfb₃⟩ : ∃ fb₃, 64 * U + fb₃ = xa := Nat.le.dest (by omega)
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
  have hBoxA : Pf (xa + 4 * V) (.box xa (Af k)) :=
    .boxIntro xa _ _ (Pf_mono hA (by omega))
      (by simp only [Formula.size, numCost]; omega)
  exact ⟨⟨32768 * U, hA⟩,
    ⟨2 * xa, .mp _ _ _ _ hC₁ hBoxA (by omega)⟩⟩

end PD.BaseTheorems
