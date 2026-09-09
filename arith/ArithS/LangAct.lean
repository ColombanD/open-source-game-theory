import ArithS.MetaLength

/-!
# ArithS.LangAct — the language `ℒₒᵣ + {c_C, c_D}` and the transposition τ

Roadmap §2.4: the two actions are FRESH CONSTANT SYMBOLS of the language, never numerals.
`LAct := ℒₒᵣ + Language.constant Act`. Its Gödel encoding is written by hand so that every
`ℒₒᵣ` symbol keeps its `ℒₒᵣ` code (`encode (Sum.inl f) = encode f`): an `ℒₒᵣ`-formula has the
SAME code in both languages, which is what lets PA's Δ₁ axiom class be reused for the
theory `TAct` (`ArithS.TheoryAct`). `swap : LAct →ᵥ LAct` exchanges the two constants and is
an involution; every symbol counts `1`, so `tlen`/`flen` are invariant under ANY language hom,
in particular under `swap`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping

/-- The two actions of the prisoner's dilemma. -/
inductive Act
  | C
  | D
  deriving DecidableEq, Inhabited, Repr

/-- `ℒₒᵣ` extended by two constant symbols `c_C`, `c_D`. -/
abbrev LAct : Language := ℒₒᵣ + Language.constant Act

namespace LAct

/-- The constant symbol of an action. -/
abbrev const (a : Act) : LAct.Func 0 := Sum.inr (Language.Constant.Func.const a)

instance decEqConst (k : ℕ) : DecidableEq (Language.Constant.Func Act k)
  | .const a, .const b => decidable_of_iff (a = b) (by simp)

instance decEqFunc (k : ℕ) : DecidableEq (LAct.Func k) :=
  inferInstanceAs (DecidableEq (Language.Func ℒₒᵣ k ⊕ Language.Constant.Func Act k))

instance decEqRel (k : ℕ) : DecidableEq (LAct.Rel k) :=
  inferInstanceAs (DecidableEq (Language.Rel ℒₒᵣ k ⊕ PEmpty))

instance : LAct.DecidableEq := ⟨decEqFunc, decEqRel⟩

/-! ### The encoding: `ℒₒᵣ` codes unchanged, `c_C ↦ 2`, `c_D ↦ 3` -/

/-- Codes of `ℒₒᵣ` function symbols are `0` or `1`. -/
lemma ORing.encode_func_lt_two {k : ℕ} (f : Language.Func ℒₒᵣ k) : Encodable.encode f < 2 := by
  rcases Language.ORing.of_mem_range_encode_func.mp ⟨f, rfl⟩ with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
    omega

def encodeFunc {k : ℕ} : LAct.Func k → ℕ
  | Sum.inl f => Encodable.encode f
  | Sum.inr (Language.Constant.Func.const Act.C) => 2
  | Sum.inr (Language.Constant.Func.const Act.D) => 3

def decodeFunc : (k : ℕ) → ℕ → Option (LAct.Func k)
  | k, n =>
    if n < 2 then (Encodable.decode n : Option (Language.Func ℒₒᵣ k)).map Sum.inl
    else match k with
      | 0 => if n = 2 then some (const Act.C) else if n = 3 then some (const Act.D) else none
      | _ + 1 => none

@[instance_reducible] def encFunc (k : ℕ) : Encodable (LAct.Func k) where
  encode := encodeFunc
  decode := decodeFunc k
  encodek := by
    rintro (f | ⟨(_ | _)⟩)
    · simp [encodeFunc, decodeFunc, ORing.encode_func_lt_two f]; rfl
    · decide
    · decide

@[instance_reducible] def encRel (k : ℕ) : Encodable (LAct.Rel k) where
  encode
    | Sum.inl r => Encodable.encode r
    | Sum.inr e => PEmpty.elim e
  decode n := (Encodable.decode n : Option (Language.Rel ℒₒᵣ k)).map Sum.inl
  encodek := by
    rintro (r | e)
    · simp; rfl
    · exact e.elim

instance instEncFunc (k : ℕ) :
    Encodable (Language.Func ℒₒᵣ k ⊕ Language.Func (Language.constant Act) k) := encFunc k
instance instEncRel (k : ℕ) :
    Encodable (Language.Rel ℒₒᵣ k ⊕ Language.Rel (Language.constant Act) k) := encRel k

instance : LAct.Encodable := Language.Encodable.mk instEncFunc instEncRel

@[simp] lemma encode_inl_func {k : ℕ} (f : Language.Func ℒₒᵣ k) :
    Encodable.encode (α := LAct.Func k) (Sum.inl f) = Encodable.encode f := rfl
@[simp] lemma encode_inl_rel {k : ℕ} (r : Language.Rel ℒₒᵣ k) :
    Encodable.encode (α := LAct.Rel k) (Sum.inl r) = Encodable.encode r := rfl
@[simp] lemma encode_const_C : Encodable.encode (α := LAct.Func 0) (const Act.C) = 2 := rfl
@[simp] lemma encode_const_D : Encodable.encode (α := LAct.Func 0) (const Act.D) = 3 := rfl

/-! ### Δ₀-definability of the symbol sets -/

lemma mem_range_encode_func {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : LAct.Func k → ℕ) ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨
    (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  constructor
  · rintro ⟨g, rfl⟩
    rcases g with g | ⟨(_ | _)⟩
    · rcases Language.ORing.of_mem_range_encode_func.mp ⟨g, rfl⟩ with
        ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Sum.inl Language.ORing.Func.zero, rfl⟩
    · exact ⟨Sum.inl Language.ORing.Func.one, rfl⟩
    · exact ⟨const Act.C, rfl⟩
    · exact ⟨const Act.D, rfl⟩
    · exact ⟨Sum.inl Language.ORing.Func.add, rfl⟩
    · exact ⟨Sum.inl Language.ORing.Func.mul, rfl⟩

lemma mem_range_encode_rel {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : LAct.Rel k → ℕ) ↔ (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  constructor
  · rintro ⟨g, rfl⟩
    rcases g with g | e
    · rcases Language.ORing.of_mem_range_encode_rel.mp ⟨g, rfl⟩ with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, h⟩
    · exact (e : PEmpty).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Sum.inl Language.ORing.Rel.eq, rfl⟩
    · exact ⟨Sum.inl Language.ORing.Rel.lt, rfl⟩

instance : LAct.LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨
    (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)”
  rel  := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”
  func_iff {k c} := by simpa [models_iff] using! mem_range_encode_func
  rel_iff {k c} := by simpa [models_iff] using! mem_range_encode_rel

/-! ### Arithmetic symbols, the embedding, and the swap -/

instance : Language.Eq LAct := ⟨Sum.inl Language.Eq.eq⟩
instance : Language.LT LAct := ⟨Sum.inl Language.LT.lt⟩
instance : Language.Zero LAct := ⟨Sum.inl Language.Zero.zero⟩
instance : Language.One LAct := ⟨Sum.inl Language.One.one⟩
instance : Language.Add LAct := ⟨Sum.inl Language.Add.add⟩
instance : Language.Mul LAct := ⟨Sum.inl Language.Mul.mul⟩
instance : Language.ORing LAct := Language.ORing.mk

/-- The inclusion `ℒₒᵣ →ᵥ LAct`. -/
abbrev emb : ℒₒᵣ →ᵥ LAct := Language.Hom.add₁ _ _

/-- The transposition of the two action constants. -/
def swap : LAct →ᵥ LAct where
  func {k} f := match k, f with
    | _, Sum.inl f => Sum.inl f
    | 0, Sum.inr (Language.Constant.Func.const Act.C) => const Act.D
    | 0, Sum.inr (Language.Constant.Func.const Act.D) => const Act.C
  rel r := r

@[simp] lemma swap_inl {k : ℕ} (f : Language.Func ℒₒᵣ k) : swap.func (Sum.inl f : LAct.Func k) = Sum.inl f := rfl
@[simp] lemma swap_C : swap.func (const Act.C) = const Act.D := rfl
@[simp] lemma swap_D : swap.func (const Act.D) = const Act.C := rfl
@[simp] lemma swap_rel {k : ℕ} (r : LAct.Rel k) : swap.rel r = r := rfl

lemma swap_swap_func {k : ℕ} (f : LAct.Func k) : swap.func (swap.func f) = f := by
  rcases f with f | ⟨(_ | _)⟩ <;> rfl

lemma swap_emb {k : ℕ} (f : Language.Func ℒₒᵣ k) : swap.func (emb.func f) = emb.func f := rfl

end LAct

/-! ### Symbol counts are invariant under language homs -/

section lengthInvariance

variable {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂)

lemma tlen_lMap {n : ℕ} (t : SyntacticSemiterm L₁ n) : tlen (Semiterm.lMap Φ t) = tlen t := by
  induction t with
  | bvar x => simp [tlen]
  | fvar x => simp [tlen]
  | func f v ih => simp [tlen, Semiterm.lMap_func, ih]

lemma flen_lMap {n : ℕ} (φ : Semiproposition L₁ n) : flen (Semiformula.lMap Φ φ) = flen φ := by
  induction φ with
  | rel R v => simp [Semiformula.lMap_rel, flen, tlen_lMap]
  | nrel R v => simp [Semiformula.lMap_nrel, flen, tlen_lMap]
  | verum =>
    change flen (Semiformula.lMap Φ ⊤) = 1
    rw [LogicalConnective.HomClass.map_top]; rfl
  | falsum =>
    change flen (Semiformula.lMap Φ ⊥) = 1
    rw [LogicalConnective.HomClass.map_bot]; rfl
  | and φ ψ ihφ ihψ =>
    change flen (Semiformula.lMap Φ (φ ⋏ ψ)) = flen φ + flen ψ + 1
    rw [LogicalConnective.HomClass.map_and]
    change flen (Semiformula.lMap Φ φ) + flen (Semiformula.lMap Φ ψ) + 1 = _
    rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change flen (Semiformula.lMap Φ (φ ⋎ ψ)) = flen φ + flen ψ + 1
    rw [LogicalConnective.HomClass.map_or]
    change flen (Semiformula.lMap Φ φ) + flen (Semiformula.lMap Φ ψ) + 1 = _
    rw [ihφ, ihψ]
  | all φ ih =>
    change flen (Semiformula.lMap Φ (∀¹ φ)) = flen φ + 1
    rw [Semiformula.lMap_all]
    change flen (Semiformula.lMap Φ φ) + 1 = _
    rw [ih]
  | exs φ ih =>
    change flen (Semiformula.lMap Φ (∃¹ φ)) = flen φ + 1
    rw [Semiformula.lMap_exs]
    change flen (Semiformula.lMap Φ φ) + 1 = _
    rw [ih]

end lengthInvariance

end ArithS
