import PrisonersDilemma.Base.Exclusion

/-!
# Base/TowerCensus — the provability-tracking floor census (2026-08-25)

**What it is for.** `no_provable_tailToS_floor` claims "no proof tails at the
target atom T" and kills every reading rule by SHAPE. That claim is FALSE when
T's player is a then-`D` searcher: `botSearchStep` proves `□(its guard) → T`
outright — a genuine theorem that tails at T. The census must therefore admit
that theorem and show it is HARMLESS: its box antecedent is unprovable, because
the guard itself is a formula of the same kind one level down. So the class
tracks boxes explicitly.

**The tower.** Fix a chain of targets `Z₁, Z₂, …` — each the atom the previous
one's reading rule is guarded by (`T`, then the partner's guard `Y`, then the
guard of `Y`'s own player, … until a player no rule reads). At one level, the
tower class `TowerAt Z dead n φ` says: `φ` is an implication chain ending at

* index `0`: the target `Z` itself;
* index `n+1`: a box whose content is an index-`n` formula;

whose antecedents are neither in any LOWER index of this level (`Low`) nor in
any DEEPER level (`dead` — the deeper levels' towers, one index higher per level
down). The two exclusions are exactly what makes every premise-free axiom
self-annihilate (`implK`, `implS`, `box4`, `axKf`, `boxMono`, …) and what lets a
`mp`/`implTrans` with a BOX in the middle be discharged by the deeper level's
theorem — a theorem already in hand, not an induction hypothesis.

**The claim.** For each level, `∀ K n φ, Pf K φ → TowerAt Z (DeadAll rest) n φ → False`,
proved by strong induction on the budget with the deeper levels' claims as
hypotheses. Instantiated bottom-up: the deepest target has no reading rule, the
one above it is guarded by a box of a deepest-level formula, and so on.
-/

open PD PD.BaseTheorems

namespace PD

/-- One level's tower (see the module header). `dead n a` is "a lies in a deeper
    level at an index compatible with n" — supplied by `DeadAll`. -/
def TowerAt (Z : Formula) (dead : Nat → Formula → Prop) : Nat → Formula → Prop
  | n, .impl a ψ =>
      TowerAt Z dead n ψ ∧ (∀ m, m ≤ n → ¬ TowerAt Z dead m a) ∧ ¬ dead n a
  | n + 1, .box _ W => TowerAt Z dead n W
  | 0, φ => φ = Z
  | _ + 1, _ => False

/-- The DEEPER levels, as seen from index `n` of the level above: the first
    deeper level at indices `≤ n+1`, the next at `≤ n+2`, and so on. -/
def DeadAll : List Formula → Nat → Formula → Prop
  | [], _, _ => False
  | Z :: rest, n, a =>
      (∃ m, m ≤ n + 1 ∧ TowerAt Z (DeadAll rest) m a) ∨ DeadAll rest (n + 1) a

/-- The tower of the level whose target heads the list. -/
def Tower : List Formula → Nat → Formula → Prop
  | [], _, _ => False
  | Z :: rest, n, φ => TowerAt Z (DeadAll rest) n φ

/-! ## Unfolding lemmas -/

theorem TowerAt_impl (Z : Formula) (dead : Nat → Formula → Prop) (n : Nat) (a ψ : Formula) :
    TowerAt Z dead n (.impl a ψ)
      ↔ TowerAt Z dead n ψ ∧ (∀ m, m ≤ n → ¬ TowerAt Z dead m a) ∧ ¬ dead n a := by
  cases n <;> simp [TowerAt]

theorem TowerAt_succ_box (Z : Formula) (dead : Nat → Formula → Prop) (n k : Nat) (W : Formula) :
    TowerAt Z dead (n + 1) (.box k W) ↔ TowerAt Z dead n W := by simp [TowerAt]

theorem TowerAt_zero_box (Z : Formula) (dead : Nat → Formula → Prop) (k : Nat) (W : Formula) :
    TowerAt Z dead 0 (.box k W) ↔ Formula.box k W = Z := by simp [TowerAt]

theorem TowerAt_zero_plays (Z : Formula) (dead : Nat → Formula → Prop) (p q : Prog) (a : Action) :
    TowerAt Z dead 0 (.plays p q a) ↔ Formula.plays p q a = Z := by simp [TowerAt]
theorem TowerAt_succ_plays (Z : Formula) (dead : Nat → Formula → Prop) (n : Nat) (p q : Prog) (a : Action) :
    ¬ TowerAt Z dead (n + 1) (.plays p q a) := by simp [TowerAt]
theorem TowerAt_zero_neg (Z : Formula) (dead : Nat → Formula → Prop) (φ : Formula) :
    TowerAt Z dead 0 (.neg φ) ↔ Formula.neg φ = Z := by simp [TowerAt]
theorem TowerAt_succ_neg (Z : Formula) (dead : Nat → Formula → Prop) (n : Nat) (φ : Formula) :
    ¬ TowerAt Z dead (n + 1) (.neg φ) := by simp [TowerAt]
theorem TowerAt_zero_eq (Z : Formula) (dead : Nat → Formula → Prop) (p q : Prog) :
    TowerAt Z dead 0 (.eq p q) ↔ Formula.eq p q = Z := by simp [TowerAt]
theorem TowerAt_succ_eq (Z : Formula) (dead : Nat → Formula → Prop) (n : Nat) (p q : Prog) :
    ¬ TowerAt Z dead (n + 1) (.eq p q) := by simp [TowerAt]
theorem TowerAt_zero_diag (Z : Formula) (dead : Nat → Formula → Prop) (g : Nat) (φ : Formula) :
    TowerAt Z dead 0 (.diag g φ) ↔ Formula.diag g φ = Z := by simp [TowerAt]
theorem TowerAt_succ_diag (Z : Formula) (dead : Nat → Formula → Prop) (n g : Nat) (φ : Formula) :
    ¬ TowerAt Z dead (n + 1) (.diag g φ) := by simp [TowerAt]

/-- The admissible target shapes: a plays-atom, or an identity between two
    DISTINCT programs (CupodTroll's index-decided guard). Neither is a box, an
    implication, a negation, a diag, or a reflexive identity. -/
def GoodTarget (Z : Formula) : Prop :=
  (∃ p q c, Z = .plays p q c) ∨ (∃ p q, p ≠ q ∧ Z = .eq p q)

theorem GoodTarget.not_box {Z : Formula} (h : GoodTarget Z) (k : Nat) (W : Formula) :
    Formula.box k W ≠ Z := by
  rintro rfl; rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> simp at h
theorem GoodTarget.not_impl {Z : Formula} (h : GoodTarget Z) (a ψ : Formula) :
    Formula.impl a ψ ≠ Z := by
  rintro rfl; rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> simp at h
theorem GoodTarget.not_neg {Z : Formula} (h : GoodTarget Z) (φ : Formula) :
    Formula.neg φ ≠ Z := by
  rintro rfl; rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> simp at h
theorem GoodTarget.not_diag {Z : Formula} (h : GoodTarget Z) (g : Nat) (φ : Formula) :
    Formula.diag g φ ≠ Z := by
  rintro rfl; rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> simp at h
theorem GoodTarget.not_eqRefl {Z : Formula} (h : GoodTarget Z) (p : Prog) :
    Formula.eq p p ≠ Z := by
  rintro rfl
  rcases h with ⟨_, _, _, h⟩ | ⟨p', q', hne, h⟩
  · simp at h
  · simp only [Formula.eq.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hne rfl

/-! ## Structural lemmas -/

/-- A formula sits at ONE index of a level: the box depth of its tail is fixed. -/
theorem TowerAt_unique {Z : Formula} (hZ : GoodTarget Z) (dead : Nat → Formula → Prop) :
    ∀ (φ : Formula) (n m : Nat), TowerAt Z dead n φ → TowerAt Z dead m φ → n = m
  | .impl a ψ, n, m, hn, hm => by
      rw [TowerAt_impl] at hn hm
      exact TowerAt_unique hZ dead ψ n m hn.1 hm.1
  | .box k W, n, m, hn, hm => by
      cases n with
      | zero => exact absurd ((TowerAt_zero_box _ _ _ _).1 hn) (hZ.not_box k W)
      | succ n' =>
        cases m with
        | zero => exact absurd ((TowerAt_zero_box _ _ _ _).1 hm) (hZ.not_box k W)
        | succ m' =>
          rw [TowerAt_succ_box] at hn hm
          exact congrArg Nat.succ (TowerAt_unique hZ dead W n' m' hn hm)
  | .plays p q c, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rfl
        | succ _ => exact absurd hm (TowerAt_succ_plays _ _ _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_plays _ _ _ _ _ _)
  | .neg φ, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rfl
        | succ _ => exact absurd hm (TowerAt_succ_neg _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_neg _ _ _ _)
  | .eq p q, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rfl
        | succ _ => exact absurd hm (TowerAt_succ_eq _ _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_eq _ _ _ _ _)
  | .diag g φ, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rfl
        | succ _ => exact absurd hm (TowerAt_succ_diag _ _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_diag _ _ _ _ _)

/-- Two levels with DISTINCT targets share no formula: a chain's tail atom is unique. -/
theorem TowerAt_disjoint {Z Z' : Formula} (hZ : GoodTarget Z) (hZ' : GoodTarget Z')
    (hne : Z ≠ Z') (dead dead' : Nat → Formula → Prop) :
    ∀ (φ : Formula) (n m : Nat), TowerAt Z dead n φ → TowerAt Z' dead' m φ → False
  | .impl a ψ, n, m, hn, hm => by
      rw [TowerAt_impl] at hn hm
      exact TowerAt_disjoint hZ hZ' hne dead dead' ψ n m hn.1 hm.1
  | .box k W, n, m, hn, hm => by
      cases n with
      | zero => exact absurd ((TowerAt_zero_box _ _ _ _).1 hn) (hZ.not_box k W)
      | succ n' =>
        cases m with
        | zero => exact absurd ((TowerAt_zero_box _ _ _ _).1 hm) (hZ'.not_box k W)
        | succ m' =>
          rw [TowerAt_succ_box] at hn hm
          exact TowerAt_disjoint hZ hZ' hne dead dead' W n' m' hn hm
  | .plays p q c, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero =>
          rw [TowerAt_zero_plays] at hn hm
          exact hne (hn.symm.trans hm)
        | succ _ => exact absurd hm (TowerAt_succ_plays _ _ _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_plays _ _ _ _ _ _)
  | .neg φ, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rw [TowerAt_zero_neg] at hn hm; exact hne (hn.symm.trans hm)
        | succ _ => exact absurd hm (TowerAt_succ_neg _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_neg _ _ _ _)
  | .eq p q, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rw [TowerAt_zero_eq] at hn hm; exact hne (hn.symm.trans hm)
        | succ _ => exact absurd hm (TowerAt_succ_eq _ _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_eq _ _ _ _ _)
  | .diag g φ, n, m, hn, hm => by
      cases n with
      | zero => cases m with
        | zero => rw [TowerAt_zero_diag] at hn hm; exact hne (hn.symm.trans hm)
        | succ _ => exact absurd hm (TowerAt_succ_diag _ _ _ _ _)
      | succ _ => exact absurd hn (TowerAt_succ_diag _ _ _ _ _)

/-- A well-formed target chain: every target admissible, all distinct. -/
def GoodChain : List Formula → Prop
  | [] => True
  | Z :: rest => GoodTarget Z ∧ (∀ Z' ∈ rest, Z ≠ Z') ∧ GoodChain rest

theorem GoodChain.head {Z : Formula} {rest : List Formula} (h : GoodChain (Z :: rest)) :
    GoodTarget Z := h.1
theorem GoodChain.tail {Z : Formula} {rest : List Formula} (h : GoodChain (Z :: rest)) :
    GoodChain rest := h.2.2
theorem GoodChain.mem {ts : List Formula} (h : GoodChain ts) : ∀ Z ∈ ts, GoodTarget Z := by
  induction ts with
  | nil => intro Z hZ; simp at hZ
  | cons Z rest ih =>
    intro Z' hZ'
    simp only [List.mem_cons] at hZ'
    rcases hZ' with rfl | hZ'
    · exact h.1
    · exact ih h.2.2 Z' hZ'

/-- Deeper-level membership names a tower of some member of `rest`. -/
theorem DeadAll_elim {rest : List Formula} {n : Nat} {a : Formula} (h : DeadAll rest n a) :
    ∃ Z' ∈ rest, ∃ rest' m, TowerAt Z' (DeadAll rest') m a := by
  induction rest generalizing n with
  | nil => exact h.elim
  | cons Z' rest' ih =>
    rcases h with ⟨m, -, hm⟩ | hdeep
    · exact ⟨Z', List.mem_cons_self .., rest', m, hm⟩
    · obtain ⟨Z'', hmem, r, m, hm⟩ := ih hdeep
      exact ⟨Z'', List.mem_cons_of_mem _ hmem, r, m, hm⟩

/-- A level's tower and its deeper levels are disjoint. -/
theorem TowerAt_not_DeadAll {Z : Formula} {rest : List Formula} (hc : GoodChain (Z :: rest))
    {n m : Nat} {φ : Formula} (h : TowerAt Z (DeadAll rest) n φ) (hd : DeadAll rest m φ) :
    False := by
  obtain ⟨Z', hmem, rest', m', hm'⟩ := DeadAll_elim hd
  exact TowerAt_disjoint hc.head (hc.tail.mem Z' hmem) (hc.2.1 Z' hmem) _ _ φ n m' h hm'

/-- Deeper membership is monotone in the index. -/
theorem DeadAll_mono {rest : List Formula} :
    ∀ {n m : Nat} {a : Formula}, n ≤ m → DeadAll rest n a → DeadAll rest m a := by
  induction rest with
  | nil => intro _ _ _ _ h; exact h.elim
  | cons Z rest' ih =>
    intro n m a hnm h
    rcases h with ⟨i, hi, hT⟩ | hdeep
    · exact Or.inl ⟨i, by omega, hT⟩
    · exact Or.inr (ih (by omega) hdeep)

/-- Boxing shifts the deeper index by one — the bridge every box arm uses. -/
theorem DeadAll_box {rest : List Formula} (hc : GoodChain rest) :
    ∀ {n : Nat} {k : Nat} {φ : Formula}, DeadAll rest (n + 1) (.box k φ) ↔ DeadAll rest n φ := by
  induction rest with
  | nil => intro _ _ _; simp [DeadAll]
  | cons Z rest' ih =>
    intro n k φ
    constructor
    · rintro (⟨i, hi, hT⟩ | hdeep)
      · cases i with
        | zero => exact absurd ((TowerAt_zero_box _ _ _ _).1 hT) (hc.head.not_box k φ)
        | succ i' =>
          rw [TowerAt_succ_box] at hT
          exact Or.inl ⟨i', by omega, hT⟩
      · exact Or.inr ((ih hc.tail).1 hdeep)
    · rintro (⟨i, hi, hT⟩ | hdeep)
      · exact Or.inl ⟨i + 1, by omega, (TowerAt_succ_box _ _ _ _ _).2 hT⟩
      · exact Or.inr ((ih hc.tail).2 hdeep)

/-- Same-level lower membership of a box, shifted. -/
theorem Low_box {Z : Formula} (hZ : GoodTarget Z) (dead : Nat → Formula → Prop) {n k : Nat}
    {φ : Formula} :
    (∀ m, m ≤ n + 1 → ¬ TowerAt Z dead m (.box k φ)) ↔ (∀ m, m ≤ n → ¬ TowerAt Z dead m φ) := by
  constructor
  · intro h m hm hT
    exact h (m + 1) (by omega) ((TowerAt_succ_box _ _ _ _ _).2 hT)
  · intro h m hm hT
    cases m with
    | zero => exact hZ.not_box k φ ((TowerAt_zero_box _ _ _ _).1 hT)
    | succ m' => exact h m' (by omega) ((TowerAt_succ_box _ _ _ _ _).1 hT)

theorem Low_mono {Z : Formula} (dead : Nat → Formula → Prop) {n m : Nat} {a : Formula}
    (hnm : m ≤ n) (h : ∀ i, i ≤ n → ¬ TowerAt Z dead i a) : ∀ i, i ≤ m → ¬ TowerAt Z dead i a :=
  fun i hi => h i (by omega)

/-! ## Two bridges the arms need -/

/-- The tail atom of an implication spine. -/
def tailOf : Formula → Formula
  | .impl _ ψ => tailOf ψ
  | φ => φ

theorem TowerAt_tailOf {Z : Formula} {dead : Nat → Formula → Prop} :
    ∀ (φ : Formula) {n : Nat}, TowerAt Z dead n φ → TowerAt Z dead n (tailOf φ)
  | .impl a ψ, n, h => by
      show TowerAt Z dead n (tailOf ψ)
      exact TowerAt_tailOf ψ ((TowerAt_impl _ _ _ _ _).1 h).1
  | .plays _ _ _, _, h => h
  | .box _ _, _, h => h
  | .neg _, _, h => h
  | .eq _ _, _, h => h
  | .diag _ _, _, h => h

theorem tailOf_implChain (gs : List Formula) (tgt : Formula) :
    tailOf (implChain gs tgt) = tailOf tgt := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [implChain, List.foldr_cons, tailOf]; exact ih

/-- A tower atom at index 0 IS the target; at any other index there is none. -/
theorem TowerAt_plays_eq {Z : Formula} {dead : Nat → Formula → Prop} {n : Nat} {p q : Prog}
    {a : Action} (h : TowerAt Z dead n (.plays p q a)) : n = 0 ∧ Formula.plays p q a = Z := by
  cases n with
  | zero => exact ⟨rfl, (TowerAt_zero_plays _ _ _ _ _).1 h⟩
  | succ _ => exact absurd h (TowerAt_succ_plays _ _ _ _ _ _)

/-- Deeper membership passes through an implication whose antecedent is not deeper. -/
theorem DeadAll_impl {rest : List Formula} :
    ∀ {n : Nat} {a ψ : Formula}, DeadAll rest n ψ → ¬ DeadAll rest n a →
      DeadAll rest n (.impl a ψ) := by
  induction rest with
  | nil => intro _ _ _ h; exact h.elim
  | cons Z' rest' ih =>
    intro n a ψ h hna
    rcases h with ⟨i, hi, hT⟩ | hdeep
    · refine Or.inl ⟨i, hi, (TowerAt_impl _ _ _ _ _).2 ⟨hT, ?_, ?_⟩⟩
      · intro j hj hTj; exact hna (Or.inl ⟨j, by omega, hTj⟩)
      · intro hd; exact hna (Or.inr (DeadAll_mono (by omega) hd))
    · exact Or.inr (ih hdeep (fun hd => hna (Or.inr hd)))

/-- A box cannot be deeper when its content sits in this level. -/
theorem TowerAt_not_DeadAll_box {Z : Formula} {rest : List Formula} (hc : GoodChain (Z :: rest))
    {n m k : Nat} {φ : Formula} (h : TowerAt Z (DeadAll rest) n φ)
    (hd : DeadAll rest m (.box k φ)) : False := by
  obtain ⟨Z', hmem, rest', i, hi⟩ := DeadAll_elim hd
  cases i with
  | zero => exact (hc.tail.mem Z' hmem).not_box k φ ((TowerAt_zero_box _ _ _ _).1 hi)
  | succ i' =>
    rw [TowerAt_succ_box] at hi
    exact TowerAt_disjoint hc.head (hc.tail.mem Z' hmem) (hc.2.1 Z' hmem) _ _ φ n i' h hi

/-! ## THE KERNEL -/

set_option maxHeartbeats 1000000 in
/-- **The tower census.** No proof, at ANY budget, concludes a formula in the
    tower of target `Z`, given: the deeper levels' towers are already unprovable
    (`hdead`); `Z` has no certificate; every reading rule that could conclude `Z`
    is either shape-impossible or — for the one that is not, the `.bot`-wrapped
    searcher — guarded by a box that is DEEPER. -/
theorem tower_census (Z : Formula) (rest : List Formula) (hc : GoodChain (Z :: rest))
    (hdead : ∀ K n φ, Pf K φ → DeadAll rest n φ → False)
    (hatom : ∀ K, ¬ AtomProvable K Z)
    (hsearch : ∀ g ψ b c opp, Z = .plays (.search g ψ (.const c) (.const b)) opp c → False)
    (hsim : ∀ p q opp a, Z = .plays (.sim p q) opp a → False)
    (hbotsim : ∀ p q opp a, Z = .plays (.bot (.sim p q)) opp a → False)
    (hbotsearch : ∀ g ψ b c opp, Z = .plays (.bot (.search g ψ (.const c) (.const b))) opp c →
      DeadAll rest 0 (.box g (ψ.subst (.bot (.search g ψ (.const c) (.const b))) opp)))
    (hbotsys : ∀ defs i opp a, Z = .plays (.bot (.sys defs i)) opp a → False)
    (hite : ∀ z a' g ψ c0 c1 q opp,
      Z = .plays (.ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q) opp c0 →
      False)
    (hsts : ∀ k₁ ψ₁ k₂ ψ₂ c0 c1 q opp,
      Z = .plays (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opp c0 → False)
    (hplug : ∀ g₁ ψ₁ e₁ L a opp,
      Z = .plays (.search g₁ ψ₁ (searchPlug L (.const a)) e₁) opp a → False)
    (hctx : ∀ hd L a opp, Z = .plays (ctxPlug (hd :: L) (.const a)) opp a → False)
    (hplug2 : ∀ hd L a opp, Z = .plays (plug2 (hd :: L) (.const a)) opp a → False) :
    ∀ K n φ, Pf K φ → TowerAt Z (DeadAll rest) n φ → False := by
  have hZ : GoodTarget Z := hc.head
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro n φ hp ht
    cases hp with
    -- ── the reading rules: the tail atom is `plays me oppo a`; if it is Z, kill by shape,
    --    or (the bot-searcher) by the DEAD box antecedent ──
    | searchBranch gg psi aa bb me oppo hme hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hsearch _ _ _ _ _ hZ'.symm
    | simStep me pp qq oppo aa hme hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hsim _ _ _ _ hZ'.symm
    | botSimStep me pp qq oppo aa hme hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hbotsim _ _ _ _ hZ'.symm
    | botSearchStep gg psi aa bb me oppo hme hsz =>
        obtain ⟨hT, -, hD⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨rfl, hZ'⟩ := TowerAt_plays_eq hT
        subst hme
        exact hD (hbotsearch _ _ _ _ _ hZ'.symm)
    | botSysSearchStep dfs ii gg psi aa bb me oppo hme hget hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hbotsys _ _ _ _ hZ'.symm
    | botSysSimStep dfs ii jj aa me oppo hme hget hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hbotsys _ _ _ _ hZ'.symm
    | iteBranchSearch_t gg zz aa' cc0 cc1 psi qq me oppo hme hsz =>
        have hT := TowerAt_tailOf _ ht
        simp only [tailOf] at hT
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hite _ _ _ _ _ _ _ _ hZ'.symm
    | botSysSearchThenSearch dfs ii k₁ k₂ m ψ₁ ψ₂ c0 c1 q' me oppo hme hget hpre hm hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hbotsys _ _ _ _ hZ'.symm
    | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q' me oppo hme hpre hm hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hsts _ _ _ _ _ _ _ _ hZ'.symm
    | searchChain g₁ ψ₁ e₁ L a me oppo hme hsz =>
        have hT := TowerAt_tailOf _ ht
        simp only [tailOf, tailOf_implChain] at hT
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hplug _ _ _ _ _ _ hZ'.symm
    | ctxChain hd L a me oppo hme hsz =>
        have hT := TowerAt_tailOf _ ht
        simp only [tailOf, tailOf_implChain] at hT
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hctx _ _ _ _ hZ'.symm
    | searchElseChain hd L a me oppo hme hsz =>
        have hT := TowerAt_tailOf _ ht
        simp only [tailOf, tailOf_implChain] at hT
        obtain ⟨-, hZ'⟩ := TowerAt_plays_eq hT
        subst hme; exact hplug2 _ _ _ _ hZ'.symm
    -- ── the atom entry ──
    | atom h =>
        cases h with
        | mk hpp hn =>
          obtain ⟨-, hZ'⟩ := TowerAt_plays_eq ht
          exact hatom K (hZ' ▸ AtomProvable.mk hpp hn)
    -- ── the logical core: strictly smaller premise budgets ──
    | weakenImpl φ' ψ m hψ hsz =>
        obtain ⟨hψt, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        have := Formula.size_pos (Formula.impl φ' ψ)
        exact ih m (by omega) n ψ hψ hψt
    | implTrans φ' ψ χ a b h1 h2 hsz =>
        obtain ⟨hχ, hLφ, hDφ⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        have hsz' := Formula.size_pos (Formula.impl φ' χ)
        by_cases hψL : ∃ m, m ≤ n ∧ TowerAt Z (DeadAll rest) m ψ
        · obtain ⟨m, hm, hψ⟩ := hψL
          exact ih a (by omega) m _ h1 ((TowerAt_impl _ _ _ _ _).2
            ⟨hψ, Low_mono _ hm hLφ, fun hd => hDφ (DeadAll_mono hm hd)⟩)
        by_cases hψD : DeadAll rest n ψ
        · exact hdead a n _ h1 (DeadAll_impl hψD hDφ)
        · exact ih b (by omega) n _ h2 ((TowerAt_impl _ _ _ _ _).2
            ⟨hχ, fun m hm hT => hψL ⟨m, hm, hT⟩, hψD⟩)
    | mp m₁ m₂ φ' α h1 h2 hsz =>
        -- `cases` has substituted the conclusion: it is the outer `φ`; `φ'` is the antecedent
        have hsz' := Formula.size_pos φ
        by_cases hαL : ∃ m, m ≤ n ∧ TowerAt Z (DeadAll rest) m φ'
        · obtain ⟨m, -, hα⟩ := hαL
          exact ih m₂ (by omega) m _ h2 hα
        by_cases hαD : DeadAll rest n φ'
        · exact hdead m₂ n _ h2 hαD
        · exact ih m₁ (by omega) n _ h1 ((TowerAt_impl _ _ _ _ _).2
            ⟨ht, fun m hm hT => hαL ⟨m, hm, hT⟩, hαD⟩)
    | impS2 φ' ψ χ m₁ m₂ K' h1 h2 hsz =>
        obtain ⟨hχ, hLφ, hDφ⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        have hsz' := Formula.size_pos (Formula.impl φ' χ)
        by_cases hψL : ∃ m, m ≤ n ∧ TowerAt Z (DeadAll rest) m ψ
        · obtain ⟨m, hm, hψ⟩ := hψL
          exact ih m₂ (by omega) m _ h2 ((TowerAt_impl _ _ _ _ _).2
            ⟨hψ, Low_mono _ hm hLφ, fun hd => hDφ (DeadAll_mono hm hd)⟩)
        by_cases hψD : DeadAll rest n ψ
        · exact hdead m₂ n _ h2 (DeadAll_impl hψD hDφ)
        · exact ih m₁ (by omega) n _ h1 ((TowerAt_impl _ _ _ _ _).2
            ⟨(TowerAt_impl _ _ _ _ _).2 ⟨hχ, fun m hm hT => hψL ⟨m, hm, hT⟩, hψD⟩, hLφ, hDφ⟩)
    | diagF pm fb g' K' tgt hpre hsz =>
        obtain ⟨⟨hT, -, -⟩, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        have hsz' := Formula.size_pos
          (Formula.impl (.diag g' tgt) (.impl (.box g' (.diag g' tgt)) tgt))
        refine ih pm (by omega) n _ hpre ((TowerAt_impl _ _ _ _ _).2 ⟨hT, ?_, ?_⟩)
        · intro m hm hbox
          cases m with
          | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hbox)
          | succ m' =>
            rw [TowerAt_succ_box] at hbox
            have := TowerAt_unique hZ _ tgt n m' hT hbox
            omega
        · exact fun hd => TowerAt_not_DeadAll_box hc hT hd
    -- ── the premise-free axioms: self-annihilating ──
    | implRefl φ' hsz =>
        obtain ⟨hT, hL, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        exact hL n le_rfl hT
    | implK φ' ψ hsz =>
        obtain ⟨⟨hT, -, -⟩, hL, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        exact hL n le_rfl hT
    | implS φ' ψ χ hsz =>
        obtain ⟨h2, hL1, hD1⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨h3, hL2, hD2⟩ := (TowerAt_impl _ _ _ _ _).1 h2
        obtain ⟨hχ, hLφ, hDφ⟩ := (TowerAt_impl _ _ _ _ _).1 h3
        by_cases hψL : ∃ m, m ≤ n ∧ TowerAt Z (DeadAll rest) m ψ
        · obtain ⟨m, hm, hψ⟩ := hψL
          exact hL2 m hm ((TowerAt_impl _ _ _ _ _).2
            ⟨hψ, Low_mono _ hm hLφ, fun hd => hDφ (DeadAll_mono hm hd)⟩)
        by_cases hψD : DeadAll rest n ψ
        · exact hD2 (DeadAll_impl hψD hDφ)
        · exact hL1 n le_rfl ((TowerAt_impl _ _ _ _ _).2
            ⟨(TowerAt_impl _ _ _ _ _).2 ⟨hχ, fun m hm hT => hψL ⟨m, hm, hT⟩, hψD⟩, hLφ, hDφ⟩)
    | contrapose φ' ψ m' h hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        cases n with
        | zero => exact hZ.not_neg _ ((TowerAt_zero_neg _ _ _).1 hT)
        | succ _ => exact TowerAt_succ_neg _ _ _ _ hT
    | negElim =>
        rename_i φ' m₁ m₂ h1 h2 hsz
        exact absurd (Pf_sound _ _ h2) (Pf_sound _ _ h1)
    -- ── non-target tails ──
    | eqRefl pp hsz =>
        cases n with
        | zero => exact hZ.not_eqRefl _ ((TowerAt_zero_eq _ _ _ _).1 ht)
        | succ _ => exact TowerAt_succ_eq _ _ _ _ _ ht
    | eqNeg pp qq hne hsz =>
        cases n with
        | zero => exact hZ.not_neg _ ((TowerAt_zero_neg _ _ _).1 ht)
        | succ _ => exact TowerAt_succ_neg _ _ _ _ ht
    | atomNeg p' q' b aN m hcert hne hsz =>
        cases n with
        | zero => exact hZ.not_neg _ ((TowerAt_zero_neg _ _ _).1 ht)
        | succ _ => exact TowerAt_succ_neg _ _ _ _ ht
    | diagB pm fb g' K' tgt hpre hsz =>
        obtain ⟨hT, -, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        cases n with
        | zero => exact hZ.not_diag _ _ ((TowerAt_zero_diag _ _ _ _).1 hT)
        | succ _ => exact TowerAt_succ_diag _ _ _ _ _ hT
    -- ── the box rules: index bookkeeping ──
    | atomBoxImpl kBox p' q' a hcert hsz =>
        obtain ⟨hT, hL, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        cases n with
        | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hT)
        | succ m =>
          rw [TowerAt_succ_box] at hT
          obtain ⟨rfl, -⟩ := TowerAt_plays_eq hT
          exact hL 0 (by omega) hT
    | boxIntro kIn K' φ' hpre hsz =>
        cases n with
        | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 ht)
        | succ m =>
          rw [TowerAt_succ_box] at ht
          have := Formula.size_pos (Formula.box kIn φ')
          exact ih kIn (by omega) m _ hpre ht
    | axK a b c m K' φ' α hpre hab hsz =>
        obtain ⟨hT, hL, hD⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        cases n with
        | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hT)
        | succ i =>
          rw [TowerAt_succ_box] at hT
          have hsz' := Formula.size_pos (Formula.impl (.box b φ') (.box c α))
          refine ih m (by omega) (i + 1) _ hpre ((TowerAt_succ_box _ _ _ _ _).2
            ((TowerAt_impl _ _ _ _ _).2 ⟨hT, (Low_box hZ _).1 hL, ?_⟩))
          intro hd; exact hD ((DeadAll_box hc.tail).2 hd)
    | box4 a b K' φ' h1 h2 =>
        obtain ⟨hT, hL, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        cases n with
        | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hT)
        | succ i =>
          rw [TowerAt_succ_box] at hT
          cases i with
          | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hT)
          | succ i' =>
            rw [TowerAt_succ_box] at hT
            exact hL (i' + 1) (by omega) ((TowerAt_succ_box _ _ _ _ _).2 hT)
    | axKf a b c K' φ' α h1 h2 =>
        obtain ⟨h2', hL1, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        obtain ⟨hT, hL2, hD2⟩ := (TowerAt_impl _ _ _ _ _).1 h2'
        cases n with
        | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hT)
        | succ i =>
          rw [TowerAt_succ_box] at hT
          refine hL1 (i + 1) le_rfl ((TowerAt_succ_box _ _ _ _ _).2
            ((TowerAt_impl _ _ _ _ _).2 ⟨hT, (Low_box hZ _).1 hL2, ?_⟩))
          intro hd; exact hD2 ((DeadAll_box hc.tail).2 hd)
    | boxMono a b K' φ' hab hsz =>
        obtain ⟨hT, hL, -⟩ := (TowerAt_impl _ _ _ _ _).1 ht
        cases n with
        | zero => exact hZ.not_box _ _ ((TowerAt_zero_box _ _ _ _).1 hT)
        | succ i =>
          rw [TowerAt_succ_box] at hT
          exact hL (i + 1) le_rfl ((TowerAt_succ_box _ _ _ _ _).2 hT)

/-- Package a proven level as the `hdead` of the level above. -/
theorem DeadAll_cons_kill {Z : Formula} {rest : List Formula}
    (hZ : ∀ K n φ, Pf K φ → TowerAt Z (DeadAll rest) n φ → False)
    (hrest : ∀ K n φ, Pf K φ → DeadAll rest n φ → False) :
    ∀ K n φ, Pf K φ → DeadAll (Z :: rest) n φ → False := by
  rintro K n φ hp (⟨m, -, hT⟩ | hdeep)
  · exact hZ K m φ hp hT
  · exact hrest K (n + 1) φ hp hdeep

theorem DeadAll_nil_kill : ∀ K n φ, Pf K φ → DeadAll [] n φ → False :=
  fun _ _ _ _ h => h.elim

end PD
