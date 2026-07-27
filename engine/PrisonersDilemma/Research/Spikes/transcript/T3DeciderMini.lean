import Mathlib.Data.Nat.Log

/-!
# T3.0 spike — `Prov` is DECIDABLE under transcript accounting (mini-engine, all 9 rules).

`DECIDABILITY_ROADMAP.md` T3, kill-criterion. The transcript cost model makes bounded proof
search genuinely finite: EVERY rule's final gate is `(premise transcripts) + |conclusion| ≤ k`,
so (a) premise budgets are STRICTLY below the conclusion's, and (b) premise formulas have size
bounded by their budgets (`prov_size`) — hence range over the FINITE set `enumF k` (formulas of
size ≤ k are finitely many because every numeral pays `log2`). Backward search therefore
terminates by recursion on the budget, with fuel = budget.

THE RESULT: `decP` (a computable Bool search) with `decP_sound` + `decP_complete`, giving
`instance : Decidable (Prov k φ)` — for the FULL additive rule set of `T0Transcript.lean`,
INCLUDING the Löb-fixpoint rules `diagF`/`diagB` (whose gate premise is found by searching the
finitely many possible `fb` subscripts — `log2 fb` is paid by the gate formula, so `fb < 2^(k+2)`).
This is the mini analogue of "GL is decidable despite Löb", now for the bounded engine shape.

What this does NOT cover (engine deltas, next steps): `struct` (Derivation search — same method,
structural sizes now paid) and `atom` (PlaysProof/eval entanglement — the fuel-stratified
`decGuard` side, T3.1+). The mp-cut wall (`MN1_decidable.lean`) is dissolved HERE by construction:
`app`'s cut formula is paid by its premise transcripts, so cuts range over `enumF k`.

NOTE the one deliberate difference from T0's mini: atoms pay their code (`log2 n + 2`), as every
engine `Formula` leaf pays its content — with unit-cost coded atoms, formulas of bounded size
would be infinite and enumeration impossible (that IS the old wall, localized).

Efficiency is a NON-goal: `enumF`/the `fb` range are exponential; decidability is the theorem.
-/

namespace T3
open Classical in

/-! ## 1. Formulas; size pays every numeral (incl. atom codes). -/

inductive F where
  | atom (n : Nat)
  | impl (a b : F)
  | box  (g : Nat) (a : F)
  | diag (g : Nat) (t : F)
deriving DecidableEq, Repr

def F.size : F → Nat
  | .atom n   => Nat.log2 n + 2
  | .impl a b => a.size + b.size + 1
  | .box g a  => (Nat.log2 g + 1) + a.size + 1
  | .diag g t => (Nat.log2 g + 1) + t.size + 1

theorem F.size_pos : ∀ φ : F, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp [F.size]

/-! ## 2. `Prov` — the T0 additive (transcript) rule set, verbatim shapes. -/

inductive Prov : Nat → F → Prop where
  | app {m₁ m₂ k : Nat} (φ α : F) :
      Prov m₁ (.impl φ α) → Prov m₂ φ → m₁ + m₂ + α.size ≤ k → Prov k α
  | boxIntro {m g k : Nat} (φ : F) :
      Prov m φ → m ≤ g → m + (F.box g φ).size ≤ k → Prov k (.box g φ)
  | boxMono {a b k : Nat} (φ : F) :
      a ≤ b → (F.impl (.box a φ) (.box b φ)).size ≤ k →
      Prov k (.impl (.box a φ) (.box b φ))
  | axKf {a b c k : Nat} (φ α : F) :
      a + b + α.size ≤ c →
      (F.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ k →
      Prov k (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
  | four {a b k : Nat} (φ : F) :
      a + (F.box a φ).size ≤ b →
      (F.impl (.box a φ) (.box b (.box a φ))).size ≤ k →
      Prov k (.impl (.box a φ) (.box b (.box a φ)))
  | diagF {pm fb g k : Nat} (t : F) :
      Prov pm (.impl (.box fb t) t) →
      pm + (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k →
      Prov k (.impl (.diag g t) (.impl (.box g (.diag g t)) t))
  | diagB {pm fb g k : Nat} (t : F) :
      Prov pm (.impl (.box fb t) t) →
      pm + (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k →
      Prov k (.impl (.impl (.box g (.diag g t)) t) (.diag g t))
  | implTrans {m₁ m₂ k : Nat} (φ ψ χ : F) :
      Prov m₁ (.impl φ ψ) → Prov m₂ (.impl ψ χ) →
      m₁ + m₂ + (F.impl φ χ).size ≤ k → Prov k (.impl φ χ)
  | impS2 {m₁ m₂ k : Nat} (φ ψ χ : F) :
      Prov m₁ (.impl φ (.impl ψ χ)) → Prov m₂ (.impl φ ψ) →
      m₁ + m₂ + (F.impl φ χ).size ≤ k → Prov k (.impl φ χ)

/-- Budget monotonicity (each rule's final gate relaxes). -/
theorem Prov_mono : ∀ {j φ}, Prov j φ → ∀ {k}, j ≤ k → Prov k φ := by
  intro j φ h
  induction h with
  | app φ α h1 h2 hle _ _ => intro k hjk; exact Prov.app φ α h1 h2 (Nat.le_trans hle hjk)
  | boxIntro φ hp hmg hle _ => intro k hjk; exact Prov.boxIntro φ hp hmg (Nat.le_trans hle hjk)
  | boxMono φ hab hle => intro k hjk; exact Prov.boxMono φ hab (Nat.le_trans hle hjk)
  | axKf φ α hg hle => intro k hjk; exact Prov.axKf φ α hg (Nat.le_trans hle hjk)
  | four φ hg hle => intro k hjk; exact Prov.four φ hg (Nat.le_trans hle hjk)
  | diagF t hgate hle _ => intro k hjk; exact Prov.diagF t hgate (Nat.le_trans hle hjk)
  | diagB t hgate hle _ => intro k hjk; exact Prov.diagB t hgate (Nat.le_trans hle hjk)
  | implTrans φ ψ χ h1 h2 hle _ _ =>
      intro k hjk; exact Prov.implTrans φ ψ χ h1 h2 (Nat.le_trans hle hjk)
  | impS2 φ ψ χ h1 h2 hle _ _ =>
      intro k hjk; exact Prov.impS2 φ ψ χ h1 h2 (Nat.le_trans hle hjk)

/-- **Conclusions are paid**: a ≤k-transcript proof concludes a ≤k-size formula. This is the
    property (absent from the conclusion-cost model) that bounds the search space. -/
theorem prov_size : ∀ {k φ}, Prov k φ → φ.size ≤ k := by
  intro k φ h
  cases h with
  | app φ α h1 h2 hle => omega
  | boxIntro φ hp hmg hle => omega
  | boxMono φ hab hle => omega
  | axKf φ α hg hle => omega
  | four φ hg hle => omega
  | diagF t hgate hle => omega
  | diagB t hgate hle => omega
  | implTrans φ ψ χ h1 h2 hle => omega
  | impS2 φ ψ χ h1 h2 hle => omega

/-! ## 3. Enumeration — formulas of size ≤ n form a (computably) finite set. -/

/-- A numeral whose written length fits in `s` characters is below `2^s`. -/
theorem lt_two_pow_of_log2_lt {g s : Nat} (h : Nat.log2 g + 1 ≤ s) : g < 2 ^ s := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact Nat.two_pow_pos s
  · have h1 : g < 2 ^ (Nat.log2 g + 1) := by
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two g
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h)

/-- All formulas of size ≤ n appear in this list (a SUPERSET is fine — the search checks
    every candidate against decidable side-conditions). -/
def enumF : Nat → List F
  | 0 => []
  | n+1 =>
      ((List.range (2 ^ (n+1))).map F.atom)
      ++ ((enumF n).flatMap fun a => (enumF n).map fun b => F.impl a b)
      ++ ((List.range (2 ^ (n+1))).flatMap fun g => (enumF n).map fun a => F.box g a)
      ++ ((List.range (2 ^ (n+1))).flatMap fun g => (enumF n).map fun t => F.diag g t)

theorem enumF_complete : ∀ (n : Nat) (φ : F), φ.size ≤ n → φ ∈ enumF n := by
  intro n
  induction n with
  | zero => intro φ h; have := F.size_pos φ; omega
  | succ n ih =>
    intro φ h
    cases φ with
    | atom m =>
        simp only [F.size] at h
        have hmem : F.atom m ∈ (List.range (2 ^ (n+1))).map F.atom :=
          List.mem_map.2 ⟨m, List.mem_range.2 (lt_two_pow_of_log2_lt (by omega)), rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))
    | impl a b =>
        simp only [F.size] at h
        have ha := F.size_pos a; have hb := F.size_pos b
        have hmem : F.impl a b ∈ (enumF n).flatMap fun x => (enumF n).map fun y => F.impl x y :=
          List.mem_flatMap.2 ⟨a, ih a (by omega), List.mem_map.2 ⟨b, ih b (by omega), rfl⟩⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem))
    | box g a =>
        simp only [F.size] at h
        have ha := F.size_pos a
        have hmem : F.box g a ∈
            (List.range (2 ^ (n+1))).flatMap fun g' => (enumF n).map fun x => F.box g' x :=
          List.mem_flatMap.2 ⟨g, List.mem_range.2 (lt_two_pow_of_log2_lt (by omega)),
            List.mem_map.2 ⟨a, ih a (by omega), rfl⟩⟩
        exact List.mem_append_left _ (List.mem_append_right _ hmem)
    | diag g t =>
        simp only [F.size] at h
        have ht := F.size_pos t
        have hmem : F.diag g t ∈
            (List.range (2 ^ (n+1))).flatMap fun g' => (enumF n).map fun x => F.diag g' x :=
          List.mem_flatMap.2 ⟨g, List.mem_range.2 (lt_two_pow_of_log2_lt (by omega)),
            List.mem_map.2 ⟨t, ih t (by omega), rfl⟩⟩
        exact List.mem_append_right _ hmem

/-! ## 4. The decider — backward search, fuel-structural (fuel = budget suffices, since every
premise budget is strictly below the conclusion's). One named checker per rule (so their match
equations stay small); recursive checkers take the smaller-fuel search as a callback. Per-rule
instantiation is at the MAXIMAL admissible premise budget, justified by `Prov_mono`. -/

def chkBoxMono (k : Nat) : F → Bool
  | .impl (.box a ψ) (.box b ψ') =>
      ψ == ψ' && decide (a ≤ b) && decide ((F.impl (.box a ψ) (.box b ψ)).size ≤ k)
  | _ => false

def chkAxKf (k : Nat) : F → Bool
  | .impl (.box a (.impl ψ α)) (.impl (.box b ψ') (.box c α')) =>
      ψ == ψ' && α == α' && decide (a + b + α.size ≤ c) &&
      decide ((F.impl (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α))).size ≤ k)
  | _ => false

def chkFour (k : Nat) : F → Bool
  | .impl (.box a ψ) (.box b (.box a' ψ')) =>
      ψ == ψ' && a == a' && decide (a + (F.box a ψ).size ≤ b) &&
      decide ((F.impl (.box a ψ) (.box b (.box a ψ))).size ≤ k)
  | _ => false

def chkBoxIntro (rec : Nat → F → Bool) (k : Nat) : F → Bool
  | .box g ψ => decide ((F.box g ψ).size ≤ k) && rec (min g (k - (F.box g ψ).size)) ψ
  | _ => false

def chkDiagF (rec : Nat → F → Bool) (k : Nat) : F → Bool
  | .impl (.diag g t) (.impl (.box g' (.diag g'' t')) t'') =>
      g == g' && g == g'' && t == t' && t == t'' &&
      decide ((F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        rec (k - (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkDiagB (rec : Nat → F → Bool) (k : Nat) : F → Bool
  | .impl (.impl (.box g (.diag g' t)) t') (.diag g'' t'') =>
      g == g' && g == g'' && t == t' && t == t'' &&
      decide ((F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        rec (k - (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkApp (rec : Nat → F → Bool) (k : Nat) (φ : F) : Bool :=
  (List.range k).any fun m₁ => (enumF k).any fun φ' =>
    decide (m₁ + φ.size ≤ k) && rec m₁ (.impl φ' φ) && rec (k - φ.size - m₁) φ'

def chkImplTrans (rec : Nat → F → Bool) (k : Nat) : F → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumF k).any fun ψ' =>
        decide (m₁ + (F.impl A C).size ≤ k) && rec m₁ (.impl A ψ') &&
        rec (k - (F.impl A C).size - m₁) (.impl ψ' C)
  | _ => false

def chkImpS2 (rec : Nat → F → Bool) (k : Nat) : F → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumF k).any fun ψ' =>
        decide (m₁ + (F.impl A C).size ≤ k) && rec m₁ (.impl A (.impl ψ' C)) &&
        rec (k - (F.impl A C).size - m₁) (.impl A ψ')
  | _ => false

def decP : Nat → Nat → F → Bool
  | 0, _, _ => false
  | fuel+1, k, φ =>
      chkBoxMono k φ || chkAxKf k φ || chkFour k φ ||
      chkBoxIntro (fun m ψ => decP fuel m ψ) k φ ||
      chkDiagF (fun m ψ => decP fuel m ψ) k φ ||
      chkDiagB (fun m ψ => decP fuel m ψ) k φ ||
      chkApp (fun m ψ => decP fuel m ψ) k φ ||
      chkImplTrans (fun m ψ => decP fuel m ψ) k φ ||
      chkImpS2 (fun m ψ => decP fuel m ψ) k φ

/-! ## 5. Soundness — every search hit is a real rule application. -/

theorem chkBoxMono_sound {k : Nat} {φ : F} (h : chkBoxMono k φ = true) : Prov k φ := by
  unfold chkBoxMono at h
  split at h
  · rename_i a ψ b ψ'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hab⟩, hsz⟩ := h
    exact Prov.boxMono ψ hab hsz
  · simp at h

theorem chkAxKf_sound {k : Nat} {φ : F} (h : chkAxKf k φ = true) : Prov k φ := by
  unfold chkAxKf at h
  split at h
  · rename_i a ψ α b ψ' c α'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hg⟩, hsz⟩ := h
    exact Prov.axKf ψ α hg hsz
  · simp at h

theorem chkFour_sound {k : Nat} {φ : F} (h : chkFour k φ = true) : Prov k φ := by
  unfold chkFour at h
  split at h
  · rename_i a ψ b a' ψ'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hg⟩, hsz⟩ := h
    exact Prov.four ψ hg hsz
  · simp at h

theorem chkBoxIntro_sound {rec : Nat → F → Bool}
    (hrec : ∀ m ψ, rec m ψ = true → Prov m ψ) {k : Nat} {φ : F}
    (h : chkBoxIntro rec k φ = true) : Prov k φ := by
  unfold chkBoxIntro at h
  split at h
  · rename_i g ψ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hsz, hr⟩ := h
    refine Prov.boxIntro ψ (hrec _ _ hr) (Nat.min_le_left _ _) ?_
    have := Nat.min_le_right g (k - (F.box g ψ).size)
    omega
  · simp at h

theorem chkDiagF_sound {rec : Nat → F → Bool}
    (hrec : ∀ m ψ, rec m ψ = true → Prov m ψ) {k : Nat} {φ : F}
    (h : chkDiagF rec k φ = true) : Prov k φ := by
  unfold chkDiagF at h
  split at h
  · rename_i g t g' g'' t' t''
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, hr⟩ := h
    exact Prov.diagF t (hrec _ _ hr) (by omega)
  · simp at h

theorem chkDiagB_sound {rec : Nat → F → Bool}
    (hrec : ∀ m ψ, rec m ψ = true → Prov m ψ) {k : Nat} {φ : F}
    (h : chkDiagB rec k φ = true) : Prov k φ := by
  unfold chkDiagB at h
  split at h
  · rename_i g g' t t' g'' t''
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, hr⟩ := h
    exact Prov.diagB t (hrec _ _ hr) (by omega)
  · simp at h

theorem chkApp_sound {rec : Nat → F → Bool}
    (hrec : ∀ m ψ, rec m ψ = true → Prov m ψ) {k : Nat} {φ : F}
    (h : chkApp rec k φ = true) : Prov k φ := by
  unfold chkApp at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨m₁, hm₁, φ', _, ⟨hguard, h1⟩, h2⟩ := h
  exact Prov.app φ' φ (hrec _ _ h1) (hrec _ _ h2) (by omega)

theorem chkImplTrans_sound {rec : Nat → F → Bool}
    (hrec : ∀ m ψ, rec m ψ = true → Prov m ψ) {k : Nat} {φ : F}
    (h : chkImplTrans rec k φ = true) : Prov k φ := by
  unfold chkImplTrans at h
  split at h
  · rename_i A C
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨m₁, hm₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
    exact Prov.implTrans A ψ' C (hrec _ _ h1) (hrec _ _ h2) (by omega)
  · simp at h

theorem chkImpS2_sound {rec : Nat → F → Bool}
    (hrec : ∀ m ψ, rec m ψ = true → Prov m ψ) {k : Nat} {φ : F}
    (h : chkImpS2 rec k φ = true) : Prov k φ := by
  unfold chkImpS2 at h
  split at h
  · rename_i A C
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨m₁, hm₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
    exact Prov.impS2 A ψ' C (hrec _ _ h1) (hrec _ _ h2) (by omega)
  · simp at h

theorem decP_sound : ∀ fuel k φ, decP fuel k φ = true → Prov k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decP] at h
  | succ f ih =>
    intro k φ h
    rw [decP] at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
    · exact chkBoxMono_sound h
    · exact chkAxKf_sound h
    · exact chkFour_sound h
    · exact chkBoxIntro_sound (fun m ψ => ih m ψ) h
    · exact chkDiagF_sound (fun m ψ => ih m ψ) h
    · exact chkDiagB_sound (fun m ψ => ih m ψ) h
    · exact chkApp_sound (fun m ψ => ih m ψ) h
    · exact chkImplTrans_sound (fun m ψ => ih m ψ) h
    · exact chkImpS2_sound (fun m ψ => ih m ψ) h

/-! ## 6. Completeness — every ≤k-transcript proof is FOUND (the mp-cut wall, dissolved). -/

/-- Collapse a `||`-chain once one disjunct is `true`. -/
private theorem or_fire {a b : Bool} (h : a = true) : (a || b) = true := by simp [h]
private theorem or_fire' {a b : Bool} (h : b = true) : (a || b) = true := by simp [h]

set_option linter.unusedSimpArgs false in
theorem decP_complete : ∀ {m φ}, Prov m φ →
    ∀ fuel K, m ≤ K → K ≤ fuel → decP fuel K φ = true := by
  intro m φ h
  induction h with
  | app φ' α h1 h2 hle ih1 ih2 =>
      rename_i m₁ m₂ k
      intro fuel K hmK hKf
      have hα := F.size_pos α
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkApp (fun m ψ => decP f m ψ) K α = true := by
        unfold chkApp
        simp only [List.any_eq_true, List.mem_range]
        refine ⟨m₁, by omega, φ', enumF_complete K φ'
          (Nat.le_trans (prov_size h2) (by omega)), ?_⟩
        have e1 : decP f m₁ (.impl φ' α) = true := ih1 f m₁ le_rfl (by omega)
        have e2 : decP f (K - α.size - m₁) φ' = true := ih2 f _ (by omega) (by omega)
        have hg : m₁ + α.size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | boxIntro ψ hp hmg hle ih =>
      rename_i m g k
      intro fuel K hmK hKf
      have hs := F.size_pos ψ
      have hbs := F.size_pos (F.box g ψ)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hszK : (F.box g ψ).size ≤ K := by
        have : (F.box g ψ).size ≤ k := by omega
        omega
      have hfire : chkBoxIntro (fun m ψ => decP f m ψ) K (F.box g ψ) = true := by
        unfold chkBoxIntro
        have hmin : m ≤ min g (K - (F.box g ψ).size) := by
          have : m ≤ K - (F.box g ψ).size := by omega
          omega
        have hrec : decP f (min g (K - (F.box g ψ).size)) ψ = true := by
          refine ih f _ hmin ?_
          have h1 : min g (K - (F.box g ψ).size) ≤ K - (F.box g ψ).size :=
            Nat.min_le_right _ _
          have h2 : 1 ≤ (F.box g ψ).size := F.size_pos _
          omega
        simp [hszK, hrec]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | boxMono ψ hab hle =>
      rename_i a b k
      intro fuel K hmK hKf
      have hcs := F.size_pos (F.impl (.box a ψ) (.box b ψ))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkBoxMono K (F.impl (.box a ψ) (.box b ψ)) = true := by
        unfold chkBoxMono
        have hg : (F.impl (.box a ψ) (.box b ψ)).size ≤ K := by omega
        simp [hab, hg]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | axKf ψ α hg hle =>
      rename_i a b c k
      intro fuel K hmK hKf
      have hcs := F.size_pos (F.impl (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α)))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkAxKf K
          (F.impl (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α))) = true := by
        unfold chkAxKf
        have hszg : (F.impl (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α))).size ≤ K := by
          omega
        simp [hg, hszg]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | four ψ hg hle =>
      rename_i a b k
      intro fuel K hmK hKf
      have hcs := F.size_pos (F.impl (.box a ψ) (.box b (.box a ψ)))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkFour K (F.impl (.box a ψ) (.box b (.box a ψ))) = true := by
        unfold chkFour
        have hszg : (F.impl (.box a ψ) (.box b (.box a ψ))).size ≤ K := by omega
        simp [hg, hszg]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | diagF t hgate hle ih =>
      rename_i pm fb g k
      intro fuel K hmK hKf
      have hcs := F.size_pos (F.impl (.diag g t) (.impl (.box g (.diag g t)) t))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hgsz := prov_size hgate
      have hfire : chkDiagF (fun m ψ => decP f m ψ) K
          (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)) = true := by
        unfold chkDiagF
        simp only [List.any_eq_true, List.mem_range, beq_self_eq_true, Bool.true_and,
          Bool.and_eq_true, decide_eq_true_eq]
        have hcsz : (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ K := by omega
        refine ⟨hcsz, fb, ?_, ?_⟩
        · refine lt_two_pow_of_log2_lt ?_
          simp only [F.size] at hgsz
          omega
        · refine ih f _ (by omega) ?_
          have h1 : 1 ≤ (F.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size :=
            F.size_pos _
          omega
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | diagB t hgate hle ih =>
      rename_i pm fb g k
      intro fuel K hmK hKf
      have hcs := F.size_pos (F.impl (.impl (.box g (.diag g t)) t) (.diag g t))
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hgsz := prov_size hgate
      have hfire : chkDiagB (fun m ψ => decP f m ψ) K
          (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)) = true := by
        unfold chkDiagB
        simp only [List.any_eq_true, List.mem_range, beq_self_eq_true, Bool.true_and,
          Bool.and_eq_true, decide_eq_true_eq]
        have hcsz : (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ K := by omega
        refine ⟨hcsz, fb, ?_, ?_⟩
        · refine lt_two_pow_of_log2_lt ?_
          simp only [F.size] at hgsz
          omega
        · refine ih f _ (by omega) ?_
          have h1 : 1 ≤ (F.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size :=
            F.size_pos _
          omega
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | implTrans A ψ' C h1 h2 hle ih1 ih2 =>
      rename_i m₁ m₂ k
      intro fuel K hmK hKf
      have hs : 1 ≤ (F.impl A C).size := F.size_pos _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkImplTrans (fun m ψ => decP f m ψ) K (F.impl A C) = true := by
        unfold chkImplTrans
        simp only [List.any_eq_true, List.mem_range]
        have hψ'sz : ψ'.size ≤ K := by
          have := prov_size h1
          simp only [F.size] at this
          omega
        refine ⟨m₁, by omega, ψ', enumF_complete K ψ' hψ'sz, ?_⟩
        have e1 : decP f m₁ (.impl A ψ') = true := ih1 f m₁ le_rfl (by omega)
        have e2 : decP f (K - (F.impl A C).size - m₁) (.impl ψ' C) = true :=
          ih2 f _ (by omega) (by omega)
        have hg : m₁ + (F.impl A C).size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]
  | impS2 A ψ' C h1 h2 hle ih1 ih2 =>
      rename_i m₁ m₂ k
      intro fuel K hmK hKf
      have hs : 1 ≤ (F.impl A C).size := F.size_pos _
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfire : chkImpS2 (fun m ψ => decP f m ψ) K (F.impl A C) = true := by
        unfold chkImpS2
        simp only [List.any_eq_true, List.mem_range]
        have hψ'sz : ψ'.size ≤ K := by
          have := prov_size h2
          simp only [F.size] at this
          omega
        refine ⟨m₁, by omega, ψ', enumF_complete K ψ' hψ'sz, ?_⟩
        have e1 : decP f m₁ (.impl A (.impl ψ' C)) = true := ih1 f m₁ le_rfl (by omega)
        have e2 : decP f (K - (F.impl A C).size - m₁) (.impl A ψ') = true :=
          ih2 f _ (by omega) (by omega)
        have hg : m₁ + (F.impl A C).size ≤ K := by omega
        simp [e1, e2, hg]
      rw [decP]
      simp only [hfire, Bool.or_true, Bool.true_or]

/-! ## 7. THE PAYOFF — `Prov` is decidable; `proofSearch := D` is a computable function. -/

/-- The decider: fuel = budget suffices (every premise budget is strictly smaller). -/
def D (k : Nat) (φ : F) : Bool := decP k k φ

theorem D_iff (k : Nat) (φ : F) : D k φ = true ↔ Prov k φ :=
  ⟨decP_sound k k φ, fun h => decP_complete h k k le_rfl le_rfl⟩

/-- **Bounded provability is DECIDABLE** — with the Löb rules on board. The engine analogue
    (T3.1+) replaces `proofSearch := Classical.decide` with this, making `eval` computable. -/
instance provDecidable (k : Nat) (φ : F) : Decidable (Prov k φ) :=
  decidable_of_iff (D k φ = true) (D_iff k φ)

-- Consistency, now COMPUTED: nothing proves a bare atom at budget 3 — the search
-- returns `false`, and by completeness that is a genuine refutation.
#eval D 3 (.atom 0)   -- false

end T3
