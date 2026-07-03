/-!
# T4.1a spike — DECIDABILITY WITH BUDGET JUMPS, by least-fixpoint stabilization.

`DECIDABILITY_ROADMAP.md` T4.1. The engine's residual to full decidability is the budget
TOWER: the two CITE-model hops (`search_t`'s guard, `searchThenSearch_t`'s inner premise)
jump the search to a SOURCE-LITERAL budget while paying only its `log2`, and enumerated CUT
formulas can smuggle in fresh literals up to `2^K` — iterate and the budgets tower. The T4.1
analysis splits the problem in two:

  (a) **the bounded-literal world is decidable** — if every literal reachable by the search
      lives in a fixed finite set, the query space is finite and a positive rule system over
      it is decidable by LEAST-FIXPOINT STABILIZATION, with a computable fuel bound
      (`|query space|` iterations — monotone chains on a finite Bool-lattice stabilize);
  (b) **cut relevance** (OPEN) — minimal engine derivations only need cut formulas whose
      literals are source-bounded, collapsing the engine into world (a).

This spike proves (a) END TO END in the minimal system exhibiting the phenomenon: programs
with `search`-style nodes whose guards are CITED at their own literal budget `kg` — which can
EXCEED the conclusion's budget (`kg ≫ k` is legal: only `log2 kg + 2 ≤ k` is paid). So the
T3.0 method (fuel = budget, premises strictly decrease) is UNAVAILABLE — this is precisely
what breaks in the engine — yet decidability holds:

  `Good k p  ↔  decN (Qs p k).length k p true = true`      (`Good_iff_decN`)

with everything computable, hence `Decidable (Good k p)` (`decideGood`). The proof pattern —
step operator + soundness + chain monotonicity + ∃-fuel completeness + countP pigeonhole
stabilization + agreement propagation — is the exact skeleton for the engine's future
`ProvableB N` (literal-bounded `Provable`) decidability theorem.

Mini ↔ engine dictionary: `Good k p` ~ `Provable k (guard p)`; `Bad` ~ the Σ₁ refutation
layer (`Provable (.neg ·)`, supplier of `search_f`); `hop_t` ~ `search_t` (cite at the
literal, `log2`-paid); `hop_f` ~ `search_f` (refutation at swept budget `m` + the full floor
`kg` paid LINEARLY — no jump on the false side, exactly the engine's repair); subprogram
closure ~ the source-generated query universe (no cuts here: bounded vocabulary is (b)'s
job).

Self-contained: no engine imports, 3 standard axioms.
-/

namespace PD.T4Mini

/-! ## 1. Programs, subterm closure, literals -/

/-- `sr kg g p q`: "if the guard `g` is `Good` at budget `kg` — a SOURCE LITERAL, cited at
    `log2` cost — run `p`, else (on a derivable refutation) run `q`." -/
inductive P where
  | tt
  | ff
  | sr (kg : Nat) (g p q : P)
deriving DecidableEq

/-- Subterm closure (with the program itself). -/
def P.subs : P → List P
  | .tt => [.tt]
  | .ff => [.ff]
  | .sr kg g p q => .sr kg g p q :: (g.subs ++ p.subs ++ q.subs)

/-- All guard literals in the program text. -/
def P.lits : P → List Nat
  | .tt => []
  | .ff => []
  | .sr kg g p q => kg :: (g.lits ++ p.lits ++ q.lits)

/-! ## 2. The judgments — note `hop_t`'s premise budget `kg` is UNRELATED to `k`. -/

mutual
  /-- `Good k p`: provable-within-budget-`k` that `p` evaluates true. -/
  inductive Good : Nat → P → Prop where
    | tt_ {k : Nat} (h : 1 ≤ k) : Good k .tt
    | hop_t {k kg : Nat} {g p q : P} (hg : Good kg g)
        (hp : Good (k - (Nat.log2 kg + 2)) p) (hk : Nat.log2 kg + 2 ≤ k) :
        Good k (.sr kg g p q)
    | hop_f {k kg m : Nat} {g p q : P} (hg : Bad m g)
        (hq : Good (k - (m + kg + 1)) q) (hk : m + kg + 1 ≤ k) :
        Good k (.sr kg g p q)

  /-- `Bad k p`: a derivable REFUTATION within budget `k` (the Σ₁ else-side supplier). -/
  inductive Bad : Nat → P → Prop where
    | ff_ {k : Nat} (h : 1 ≤ k) : Bad k .ff
    | bhop_t {k kg : Nat} {g p q : P} (hg : Good kg g)
        (hp : Bad (k - (Nat.log2 kg + 2)) p) (hk : Nat.log2 kg + 2 ≤ k) :
        Bad k (.sr kg g p q)
    | bhop_f {k kg m : Nat} {g p q : P} (hg : Bad m g)
        (hq : Bad (k - (m + kg + 1)) q) (hk : m + kg + 1 ≤ k) :
        Bad k (.sr kg g p q)
end

/-! ## 3. The step operator and its iteration.

`S : Nat → P → Bool → Bool` is the current approximation (last argument = polarity:
`true` = `Good`-side, `false` = `Bad`-side). One step fires every rule whose premises the
approximation already holds. `decN n` = `n`-fold iteration from `⊥`. -/

def stepF (S : Nat → P → Bool → Bool) : Nat → P → Bool → Bool := fun k p pol =>
  match p, pol with
  | .tt, true => decide (1 ≤ k)
  | .ff, false => decide (1 ≤ k)
  | .sr kg g a b, pol =>
      (S kg g true && decide (Nat.log2 kg + 2 ≤ k) && S (k - (Nat.log2 kg + 2)) a pol)
      ||
      ((List.range (k + 1)).any fun m =>
        S m g false && decide (m + kg + 1 ≤ k) && S (k - (m + kg + 1)) b pol)
  | _, _ => false

def decN : Nat → Nat → P → Bool → Bool
  | 0 => fun _ _ _ => false
  | n + 1 => stepF (decN n)

/-! ## 4. Soundness — every hit at every fuel is a real derivation. -/

theorem decN_sound : ∀ n k p,
    (decN n k p true = true → Good k p) ∧ (decN n k p false = true → Bad k p) := by
  intro n
  induction n with
  | zero => intro k p; constructor <;> intro h <;> simp [decN] at h
  | succ n ih =>
    intro k p
    constructor <;> intro h
    · show Good k p
      cases p with
      | tt => exact Good.tt_ (by simpa [decN, stepF] using h)
      | ff => simp [decN, stepF] at h
      | sr kg g a b =>
          have h' : stepF (decN n) k (.sr kg g a b) true = true := h
          simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            List.any_eq_true, List.mem_range] at h'
          rcases h' with ⟨⟨hg, hk⟩, ha⟩ | ⟨m, _, ⟨hg, hk⟩, hb⟩
          · exact Good.hop_t ((ih kg g).1 hg) ((ih _ a).1 ha) hk
          · exact Good.hop_f ((ih m g).2 hg) ((ih _ b).1 hb) hk
    · show Bad k p
      cases p with
      | tt => simp [decN, stepF] at h
      | ff => exact Bad.ff_ (by simpa [decN, stepF] using h)
      | sr kg g a b =>
          have h' : stepF (decN n) k (.sr kg g a b) false = true := h
          simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            List.any_eq_true, List.mem_range] at h'
          rcases h' with ⟨⟨hg, hk⟩, ha⟩ | ⟨m, _, ⟨hg, hk⟩, hb⟩
          · exact Bad.bhop_t ((ih kg g).1 hg) ((ih _ a).2 ha) hk
          · exact Bad.bhop_f ((ih m g).2 hg) ((ih _ b).2 hb) hk

/-! ## 5. Chain monotonicity -/

theorem stepF_mono {S₁ S₂ : Nat → P → Bool → Bool}
    (hS : ∀ k p pol, S₁ k p pol = true → S₂ k p pol = true) :
    ∀ k p pol, stepF S₁ k p pol = true → stepF S₂ k p pol = true := by
  intro k p pol h
  cases p with
  | tt => cases pol <;> simpa [stepF] using h
  | ff => cases pol <;> simpa [stepF] using h
  | sr kg g a b =>
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range] at h ⊢
      rcases h with ⟨⟨hg, hk⟩, ha⟩ | ⟨m, hm, ⟨hg, hk⟩, hb⟩
      · exact Or.inl ⟨⟨hS _ _ _ hg, hk⟩, hS _ _ _ ha⟩
      · exact Or.inr ⟨m, hm, ⟨hS _ _ _ hg, hk⟩, hS _ _ _ hb⟩

theorem decN_le : ∀ n k p pol, decN n k p pol = true → decN (n + 1) k p pol = true := by
  intro n
  induction n with
  | zero => intro k p pol h; simp [decN] at h
  | succ n ih => exact fun k p pol h => stepF_mono ih k p pol h

theorem decN_mono {n n' : Nat} (h : n ≤ n') :
    ∀ k p pol, decN n k p pol = true → decN n' k p pol = true := by
  induction n' with
  | zero =>
      intro k p pol hh
      have : n = 0 := by omega
      subst this; exact hh
  | succ n' ih =>
      intro k p pol hh
      rcases Nat.lt_or_ge n (n' + 1) with hlt | hge
      · exact decN_le n' k p pol (ih (by omega) k p pol hh)
      · have : n = n' + 1 := by omega
        subst this; exact hh

/-! ## 6. ∃-fuel completeness (semidecidability — the §7-of-T31 analogue). -/

theorem Good_exists_decN : ∀ {k p}, Good k p → ∃ n, decN n k p true = true := by
  intro k p h
  refine Good.rec (motive_1 := fun k p _ => ∃ n, decN n k p true = true)
    (motive_2 := fun k p _ => ∃ n, decN n k p false = true)
    ?tt_ ?hop_t ?hop_f ?ff_ ?bhop_t ?bhop_f h
  case tt_ => intro k hk; exact ⟨1, by simp [decN, stepF, hk]⟩
  case hop_t =>
      intro k kg g a b hg ha hk ihg iha
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := iha
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) true = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨⟨e₁', hk⟩, e₂'⟩
  case hop_f =>
      intro k kg m g a b hg hb hk ihg ihb
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := ihb
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) true = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range]
      exact Or.inr ⟨m, by omega, ⟨e₁', hk⟩, e₂'⟩
  case ff_ => intro k hk; exact ⟨1, by simp [decN, stepF, hk]⟩
  case bhop_t =>
      intro k kg g a b hg ha hk ihg iha
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := iha
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) false = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨⟨e₁', hk⟩, e₂'⟩
  case bhop_f =>
      intro k kg m g a b hg hb hk ihg ihb
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := ihb
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) false = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range]
      exact Or.inr ⟨m, by omega, ⟨e₁', hk⟩, e₂'⟩

theorem Bad_exists_decN : ∀ {k p}, Bad k p → ∃ n, decN n k p false = true := by
  intro k p h
  refine Bad.rec (motive_1 := fun k p _ => ∃ n, decN n k p true = true)
    (motive_2 := fun k p _ => ∃ n, decN n k p false = true)
    ?tt_ ?hop_t ?hop_f ?ff_ ?bhop_t ?bhop_f h
  case tt_ => intro k hk; exact ⟨1, by simp [decN, stepF, hk]⟩
  case hop_t =>
      intro k kg g a b hg ha hk ihg iha
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := iha
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) true = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨⟨e₁', hk⟩, e₂'⟩
  case hop_f =>
      intro k kg m g a b hg hb hk ihg ihb
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := ihb
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) true = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range]
      exact Or.inr ⟨m, by omega, ⟨e₁', hk⟩, e₂'⟩
  case ff_ => intro k hk; exact ⟨1, by simp [decN, stepF, hk]⟩
  case bhop_t =>
      intro k kg g a b hg ha hk ihg iha
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := iha
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) false = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨⟨e₁', hk⟩, e₂'⟩
  case bhop_f =>
      intro k kg m g a b hg hb hk ihg ihb
      obtain ⟨n₁, e₁⟩ := ihg
      obtain ⟨n₂, e₂⟩ := ihb
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show stepF (decN (max n₁ n₂)) k (.sr kg g a b) false = true
      have e₁' := decN_mono (Nat.le_max_left n₁ n₂) _ _ _ e₁
      have e₂' := decN_mono (Nat.le_max_right n₁ n₂) _ _ _ e₂
      simp only [stepF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range]
      exact Or.inr ⟨m, by omega, ⟨e₁', hk⟩, e₂'⟩

/-! ## 7. The finite query space and its closure lemmas. -/

theorem P.mem_subs_self : ∀ p : P, p ∈ p.subs := by
  intro p; cases p <;> simp [P.subs]

theorem P.subs_closed : ∀ {p q : P}, q ∈ p.subs → ∀ {r : P}, r ∈ q.subs → r ∈ p.subs := by
  intro p
  induction p with
  | tt =>
      intro q hq r hr
      simp [P.subs] at hq; subst hq
      simpa [P.subs] using hr
  | ff =>
      intro q hq r hr
      simp [P.subs] at hq; subst hq
      simpa [P.subs] using hr
  | sr kg g a b ihg iha ihb =>
      intro q hq r hr
      simp only [P.subs, List.mem_cons, List.mem_append] at hq
      rcases hq with rfl | (hq | hq) | hq
      · exact hr
      · simp only [P.subs, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (Or.inl (ihg hq hr)))
      · simp only [P.subs, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (Or.inr (iha hq hr)))
      · simp only [P.subs, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (ihb hq hr))

/-- The head literal of any `sr` in the closure is a source literal. -/
theorem P.lit_of_mem_subs : ∀ {root p : P}, p ∈ root.subs →
    ∀ {kg : Nat} {g a b : P}, p = .sr kg g a b → kg ∈ root.lits := by
  intro root
  induction root with
  | tt =>
      intro p hp kg g a b hpe
      simp [P.subs] at hp; subst hp; cases hpe
  | ff =>
      intro p hp kg g a b hpe
      simp [P.subs] at hp; subst hp; cases hpe
  | sr kg' g' a' b' ihg iha ihb =>
      intro p hp kg g a b hpe
      simp only [P.subs, List.mem_cons, List.mem_append] at hp
      rcases hp with rfl | (hp | hp) | hp
      · cases hpe; simp [P.lits]
      · simp only [P.lits, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (Or.inl (ihg hp hpe)))
      · simp only [P.lits, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (Or.inr (iha hp hpe)))
      · simp only [P.lits, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (ihb hp hpe))

def maxL (l : List Nat) : Nat := l.foldr max 0

theorem le_maxL : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ maxL l := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hxt) (Nat.le_max_right _ _)

section Space

variable (root : P) (k₀ : Nat)

/-- The budget ceiling: the root budget and every source literal. -/
def MB : Nat := max k₀ (maxL root.lits)

/-- The finite query space: (budget ≤ ceiling) × (subterm closure) × polarity. -/
def Qs : List (Nat × P × Bool) :=
  (List.range (MB root k₀ + 1)).flatMap fun b =>
    root.subs.flatMap fun p => [(b, p, true), (b, p, false)]

theorem mem_Qs {b : Nat} {p : P} {pol : Bool} :
    (b, p, pol) ∈ Qs root k₀ ↔ b ≤ MB root k₀ ∧ p ∈ root.subs := by
  simp only [Qs, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨b', hb', p', hp', hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> · cases h; exact ⟨by omega, hp'⟩
  · rintro ⟨hb, hp⟩
    refine ⟨b, by omega, p, hp, ?_⟩
    cases pol <;> simp

end Space

/-! ## 8. Local agreement: `stepF` at an in-space query reads only in-space queries. -/

theorem anyCongr {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.any_cons]
      rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem stepF_congr {root : P} {k₀ : Nat} {S₁ S₂ : Nat → P → Bool → Bool}
    (hS : ∀ b ≤ MB root k₀, ∀ p ∈ root.subs, ∀ pol, S₁ b p pol = S₂ b p pol)
    {b : Nat} (hb : b ≤ MB root k₀) {p : P} (hp : p ∈ root.subs) (pol : Bool) :
    stepF S₁ b p pol = stepF S₂ b p pol := by
  cases p with
  | tt => cases pol <;> rfl
  | ff => cases pol <;> rfl
  | sr kg g a bb =>
      have hkg : kg ≤ MB root k₀ :=
        Nat.le_trans (le_maxL (P.lit_of_mem_subs hp rfl)) (Nat.le_max_right _ _)
      have hg : g ∈ root.subs :=
        P.subs_closed hp (by simp [P.subs, P.mem_subs_self g])
      have ha : a ∈ root.subs :=
        P.subs_closed hp (by simp [P.subs, P.mem_subs_self a])
      have hbb : bb ∈ root.subs :=
        P.subs_closed hp (by simp [P.subs, P.mem_subs_self bb])
      have e₁ : S₁ kg g true = S₂ kg g true := hS kg hkg g hg true
      have e₂ : S₁ (b - (Nat.log2 kg + 2)) a pol = S₂ (b - (Nat.log2 kg + 2)) a pol :=
        hS _ (by omega) a ha pol
      have e₃ : ((List.range (b + 1)).any fun m =>
          S₁ m g false && decide (m + kg + 1 ≤ b) && S₁ (b - (m + kg + 1)) bb pol) =
          ((List.range (b + 1)).any fun m =>
          S₂ m g false && decide (m + kg + 1 ≤ b) && S₂ (b - (m + kg + 1)) bb pol) := by
        apply anyCongr
        intro m hm
        have hmb : m ≤ MB root k₀ := by
          have := List.mem_range.mp hm; omega
        rw [hS m hmb g hg false, hS _ (by omega) bb hbb pol]
      simp only [stepF]
      rw [e₁, e₂, e₃]

/-! ## 9. Stabilization: the countP pigeonhole on the finite space. -/

theorem countP_le {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = true → g x = true) → l.countP f ≤ l.countP g := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      rw [List.countP_cons, List.countP_cons]
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      by_cases hfa : f a = true
      · have := h a (List.mem_cons_self ..) hfa
        simp [hfa, this]; omega
      · simp only [Bool.not_eq_true] at hfa
        simp [hfa]; omega

theorem countP_lt {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = true → g x = true) →
      ∀ x ∈ l, f x = false → g x = true → l.countP f < l.countP g := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a t ih =>
      intro h x hx hfx hgx
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp hx with rfl | hxt
      · have ht := countP_le (fun y hy => h y (List.mem_cons_of_mem _ hy))
        simp [hfx, hgx]; omega
      · have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hxt hfx hgx
        by_cases hfa : f a = true
        · have := h a (List.mem_cons_self ..) hfa
          simp [hfa, this]; omega
        · simp only [Bool.not_eq_true] at hfa
          by_cases hga : g a = true <;> simp [hfa, hga] <;> omega

theorem countP_le_len {α : Type} (f : α → Bool) : ∀ l : List α, l.countP f ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.length_cons]
      by_cases hfa : f a = true
      · simp [hfa]; omega
      · simp only [Bool.not_eq_true] at hfa
        simp [hfa]; omega

section Stab

variable (root : P) (k₀ : Nat)

/-- The two consecutive iterates agree on the whole space. -/
def Agree (n : Nat) : Prop :=
  ∀ q ∈ Qs root k₀, decN n q.1 q.2.1 q.2.2 = decN (n + 1) q.1 q.2.1 q.2.2

theorem agree_succ {n : Nat} (h : Agree root k₀ n) : Agree root k₀ (n + 1) := by
  intro q hq
  obtain ⟨b, p, pol⟩ := q
  have ⟨hb, hp⟩ := (mem_Qs root k₀).mp hq
  show decN (n + 1) b p pol = decN (n + 2) b p pol
  show stepF (decN n) b p pol = stepF (decN (n + 1)) b p pol
  exact stepF_congr
    (fun b' hb' p' hp' pol' => h (b', p', pol') ((mem_Qs root k₀).mpr ⟨hb', hp'⟩))
    hb hp pol

theorem agree_ge {n : Nat} (h : Agree root k₀ n) :
    ∀ m, n ≤ m → ∀ q ∈ Qs root k₀, decN m q.1 q.2.1 q.2.2 = decN n q.1 q.2.1 q.2.2 := by
  intro m
  induction m with
  | zero =>
      intro hm q _
      have : n = 0 := by omega
      subst this; rfl
  | succ m ih =>
      intro hm q hq
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · -- n ≤ m: agreement has propagated up to m
        have hAm : Agree root k₀ m := by
          clear hq q
          have : ∀ j, Agree root k₀ n → n + j ≤ m + 1 → n + j ≤ m → Agree root k₀ (n + j) := by
            intro j
            induction j with
            | zero => intro h _ _; simpa using h
            | succ j ihj =>
                intro h h1 h2
                have := ihj h (by omega) (by omega)
                exact agree_succ root k₀ this
          have hnm : n ≤ m := by omega
          have h4 := this (m - n) h (by omega) (by omega)
          have heq : n + (m - n) = m := by omega
          rw [heq] at h4
          exact h4
        have e1 : decN (m + 1) q.1 q.2.1 q.2.2 = decN m q.1 q.2.1 q.2.2 :=
          (hAm q hq).symm
        rw [e1, ih (by omega) q hq]
      · have : n = m + 1 := by omega
        subst this; rfl

/-- The pigeonhole: within `|Qs|` steps the iteration must stabilize. -/
theorem exists_agree : ∃ n, n ≤ (Qs root k₀).length ∧ Agree root k₀ n := by
  apply Classical.byContradiction
  intro hcon
  have hall : ∀ j, j ≤ (Qs root k₀).length → ¬ Agree root k₀ j := by
    intro j hj hag
    exact hcon ⟨j, hj, hag⟩
  have hstrict : ∀ j, j ≤ (Qs root k₀).length →
      (Qs root k₀).countP (fun q => decN j q.1 q.2.1 q.2.2) <
      (Qs root k₀).countP (fun q => decN (j + 1) q.1 q.2.1 q.2.2) := by
    intro j hj
    have hnag := hall j hj
    have hex : ∃ q, q ∈ Qs root k₀ ∧
        decN j q.1 q.2.1 q.2.2 ≠ decN (j + 1) q.1 q.2.1 q.2.2 := by
      apply Classical.byContradiction
      intro hno
      exact hnag (fun q hq => Classical.byContradiction (fun hne => hno ⟨q, hq, hne⟩))
    obtain ⟨q, hq, hne⟩ := hex
    have hmono : ∀ x ∈ Qs root k₀,
        decN j x.1 x.2.1 x.2.2 = true → decN (j + 1) x.1 x.2.1 x.2.2 = true :=
      fun x _ hx => decN_le j _ _ _ hx
    have hfj : decN j q.1 q.2.1 q.2.2 = false := by
      cases hj' : decN j q.1 q.2.1 q.2.2 with
      | false => rfl
      | true =>
          have h2 := decN_le j _ _ _ hj'
          rw [hj', h2] at hne
          exact absurd rfl hne
    have hgj : decN (j + 1) q.1 q.2.1 q.2.2 = true := by
      cases hj'' : decN (j + 1) q.1 q.2.1 q.2.2 with
      | true => rfl
      | false =>
          rw [hfj, hj''] at hne
          exact absurd rfl hne
    exact countP_lt hmono q hq hfj hgj
  have hge : ∀ j, j ≤ (Qs root k₀).length + 1 →
      j ≤ (Qs root k₀).countP (fun q => decN j q.1 q.2.1 q.2.2) := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        have h2 := hstrict j (by omega)
        omega
  have h1 := hge ((Qs root k₀).length + 1) (Nat.le_refl _)
  have h2 := countP_le_len (fun q => decN ((Qs root k₀).length + 1) q.1 q.2.1 q.2.2)
    (Qs root k₀)
  omega

/-! ## 10. THE PAYOFF — decidability with budget jumps, computable fuel bound. -/

/-- Any ∃-fuel hit at an in-space query is already a hit at fuel `|Qs|`. -/
theorem decN_bound {n b : Nat} {p : P} {pol : Bool}
    (hb : b ≤ MB root k₀) (hp : p ∈ root.subs)
    (h : decN n b p pol = true) : decN (Qs root k₀).length b p pol = true := by
  obtain ⟨j, hjle, hag⟩ := exists_agree root k₀
  have hqmem : (b, p, pol) ∈ Qs root k₀ := (mem_Qs root k₀).mpr ⟨hb, hp⟩
  rcases Nat.le_total n (Qs root k₀).length with hle | hge
  · exact decN_mono hle _ _ _ h
  · have e1 := agree_ge root k₀ hag n (by omega) (b, p, pol) hqmem
    have e2 := agree_ge root k₀ hag (Qs root k₀).length (by omega) (b, p, pol) hqmem
    simp only at e1 e2
    rw [e2, ← e1]
    exact h

/-- **DECIDABILITY WITH BUDGET JUMPS.** The T3.0 fuel=budget method is unavailable
    (`hop_t` cites a premise at `kg`, unrelated to `k`), yet `|Qs|` iterations of the step
    operator decide `Good` — the least fixpoint over the finite query space stabilizes. -/
theorem Good_iff_decN (root : P) (k₀ : Nat) :
    Good k₀ root ↔ decN (Qs root k₀).length k₀ root true = true := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Good_exists_decN h
    exact decN_bound root k₀ (Nat.le_max_left _ _) (P.mem_subs_self root) hn
  · intro h
    exact (decN_sound _ _ _).1 h

theorem Bad_iff_decN (root : P) (k₀ : Nat) :
    Bad k₀ root ↔ decN (Qs root k₀).length k₀ root false = true := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Bad_exists_decN h
    exact decN_bound root k₀ (Nat.le_max_left _ _) (P.mem_subs_self root) hn
  · intro h
    exact (decN_sound _ _ _).2 h

/-- `Good` is DECIDABLE — the mini's headline, with jumps and all. -/
def decideGood (k : Nat) (root : P) : Decidable (Good k root) :=
  if h : decN (Qs root k).length k root true = true then
    .isTrue ((Good_iff_decN root k).mpr h)
  else
    .isFalse (fun hg => h ((Good_iff_decN root k).mp hg))

def decideBad (k : Nat) (root : P) : Decidable (Bad k root) :=
  if h : decN (Qs root k).length k root false = true then
    .isTrue ((Bad_iff_decN root k).mpr h)
  else
    .isFalse (fun hb => h ((Bad_iff_decN root k).mp hb))

end Stab

/-!
## What this buys the engine, and what remains

PROVED here: a positive rule system whose only budget-raising rule cites SOURCE literals is
decidable, uniformly, with the computable fuel bound `|Qs| = O(maxBudget · |subterms| · 2)`.
The proof skeleton (step operator / chain / ∃-fuel / countP pigeonhole / agreement
propagation) ports to the engine's `ProvableB N` — `Provable` with every enumerated cut
restricted to literals `≤ N` — whose query space is `budgets ≤ max(k, N, source-lits)` ×
`formulas of size ≤ budget over the bounded vocabulary` × the cert layer (finite per query:
`decCertG`'s recursion is structurally fuel-bounded). Two engine-specific additions will be
needed: the enumerated-cut branching (finite per node — `enumFormula` restricted to the
vocabulary) and the subst-closure of programs (finite for bots whose guards mention `.self`/
`.opp` atomically — all zoo bots; infinite in general, where the SLICE argument caps it).

OPEN (T4.1b, the conjecture): CUT RELEVANCE — every engine-derivable `(k, φ)` has a
derivation whose cut formulas use only source-bounded literals, i.e. `Provable = ProvableB N`
at `N = N₀(k, φ)` computable. The Löb machinery respects it (`bloeb_engine`'s diag/box diet
is `O(k)`); the question is whether an exotic-literal detour can ever be NECESSARY. If the
conjecture fails, `Provable` is a natural candidate for an UNDECIDABLE bounded-provability
predicate — either resolution is a thesis-grade result.
-/

end PD.T4Mini
