import ArithS.Theory.Symmetry
import ArithS.Agents.RevalueTemplate

/-!
# ArithS.Prog — program codes and the action swap on codes

Programs are tagged codes built with the POLYNOMIAL pairing `ppair x y = (x + y)² + y`
(since 2026-09-11; before that Foundation's Cantor pair `⟪x, y⟫`, an `if` no ℒₒᵣ-term
denotes — the parametric bounded Löb milestone needs a program to be describable by a TERM
built from the binary numeral of its budget). They mirror the engine's `Prog`
(`Program.lean`); since roadmap M3 step (a) a search node carries a budget `k`
and a SIX-VARIABLE guard template `g` (a formula code over `LAct` in the description triples
`x₁ u₁ w₁` of `me` and `x₂ u₂ w₂` of `opp`, see `ArithS.Guard`/`ArithS.Template`); there is
no action slot.

* `pConst a = ppair 0 a + 1`, `pSelf = ppair 1 0 + 1`, `pOpp = ppair 2 0 + 1`,
  `pBot p = ppair 3 p + 1`, `pSim p q = ppair 4 (ppair p q) + 1`,
  `pIte b a p q = ppair 5 (ppair b (ppair a (ppair p q))) + 1`,
  `pSearch k g p q = ppair 6 (ppair k (ppair g (ppair p q))) + 1` (right-nested, exactly the
  nesting of the former `⟪6, k, g, p, q⟫`); action values: `0 = C`, `1 = D`. Sub-programs are
  STRICTLY below their parent (`le_ppair_left/right` + the outer `+ 1`), constructors are
  injective and pairwise disjoint (`ppair_ext_iff` + the tag).
* `swapAction` exchanges the two action values; `transposeCode` applies it to every action
  occurrence of a program code — the action VALUES of `pConst`/`pIte` and, through
  `revalueTemplate` (`ArithS.RevalueTemplate`), the action CONSTANTS of every stored
  template (a Δ₁ function defined by a fixpoint on Foundation pairs `⟪x, y⟫` of
  input/output — the fixpoint machinery keeps the Cantor pair — with a catch-all clause
  `y = x` on non-program codes so that it is total). It is the code-level τ of
  `Base/Transpose`: `transposeCode (transposeCode x) = x`.

**Reading guide.** Definition: §Constructors (the seven tagged codes) and, for τ, `swapAction` and the clauses `Revalue.Phi` (one per constructor) with the equations after `revalue`. Foundation plumbing: the Σ₀ graphs `p…Graph`, the `Revalue` blueprint and construction — skip on first reading. §The polynomial pairing is the arithmetic of `ppair` (injectivity, monotonicity). At ℕ: the `progCode_*` equations (`ArithS.Readings`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The polynomial pairing `ppair x y = (x + y)² + y` -/

section ppair

/-- The polynomial pairing `(x + y) * (x + y) + y`: injective, monotone in each argument,
above both arguments, and — unlike Foundation's Cantor pair, defined by an `if` — denoted by
an ℒₒᵣ-TERM. -/
noncomputable def ppair (x y : V) : V := (x + y) * (x + y) + y

/-- The Δ₀ graph of `ppair`: a plain polynomial equation, no quantifier. -/
def ppairDef : 𝚺₀.Semisentence 3 := .mkSigma “z x y. z = (x + y) * (x + y) + y”

instance ppair.defined : 𝚺₀-Function₂[V] ppair via ppairDef := .mk fun v ↦ by
  simp [ppairDef, ppair]

@[simp] lemma le_ppair_left (x y : V) : x ≤ ppair x y :=
  le_trans le_self_add (le_trans (le_mul_self _) le_self_add)

@[simp] lemma le_ppair_right (x y : V) : y ≤ ppair x y := le_add_self

/-- `s² + y < s'² + y'` whenever `s < s'` and `y ≤ s`: `s² + y ≤ s² + s < (s + 1)² ≤ s'²`. -/
lemma sq_add_lt_sq_add {s y s' : V} (hy : y ≤ s) (h : s < s') (y' : V) :
    s * s + y < s' * s' + y' := by
  have h1 : s * s + y < (s + 1) * (s + 1) := by
    have e : (s + 1) * (s + 1) = s * s + s + (s + 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (_root_.add_le_add_right hy _)
      (lt_add_of_pos_right _ (lt_of_le_of_lt (by simp) (lt_add_one s)))
  have h2 : (s + 1) * (s + 1) ≤ s' * s' :=
    mul_le_mul (lt_iff_succ_le.mp h) (lt_iff_succ_le.mp h) (by simp) (by simp)
  exact lt_of_lt_of_le h1 (le_trans h2 le_self_add)

/-- `s² + y` with `y ≤ s` determines `s`. -/
lemma sq_add_inj {s y s' y' : V} (hy : y ≤ s) (hy' : y' ≤ s')
    (h : s * s + y = s' * s' + y') : s = s' := by
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (sq_add_lt_sq_add hy hlt y'))
  · exact heq
  · exact absurd h.symm (ne_of_lt (sq_add_lt_sq_add hy' hgt y))

/-- `ppair` is injective. -/
lemma ppair_inj {x y x' y' : V} (h : ppair x y = ppair x' y') : x = x' ∧ y = y' := by
  have hs : x + y = x' + y' := sq_add_inj le_add_self le_add_self h
  have hy : y = y' := by
    unfold ppair at h
    rw [hs] at h
    exact add_left_cancel h
  refine ⟨?_, hy⟩
  rw [hy] at hs
  exact add_right_cancel hs

@[simp] lemma ppair_ext_iff {x y x' y' : V} : ppair x y = ppair x' y' ↔ x = x' ∧ y = y' :=
  ⟨ppair_inj, by rintro ⟨rfl, rfl⟩; rfl⟩

lemma ppair_lt_ppair_left {x₁ x₂ : V} (h : x₁ < x₂) (y : V) : ppair x₁ y < ppair x₂ y := by
  unfold ppair
  have h' : x₁ + y < x₂ + y := _root_.add_lt_add_left h y
  exact _root_.add_lt_add_left (mul_lt_mul'' h' h' (by simp) (by simp)) y

lemma ppair_lt_ppair_right (x : V) {y₁ y₂ : V} (h : y₁ < y₂) : ppair x y₁ < ppair x y₂ := by
  unfold ppair
  have h' : x + y₁ ≤ x + y₂ := _root_.add_le_add_right (le_of_lt h) x
  exact add_lt_add_of_le_of_lt (mul_le_mul h' h' (by simp) (by simp)) h

lemma ppair_le_ppair_left {x₁ x₂ : V} (h : x₁ ≤ x₂) (y : V) : ppair x₁ y ≤ ppair x₂ y := by
  rcases h with (rfl | lt)
  · exact le_refl _
  · exact le_of_lt (ppair_lt_ppair_left lt y)

lemma ppair_le_ppair_right (x : V) {y₁ y₂ : V} (h : y₁ ≤ y₂) : ppair x y₁ ≤ ppair x y₂ := by
  rcases h with (rfl | lt)
  · exact le_refl _
  · exact le_of_lt (ppair_lt_ppair_right x lt)

lemma ppair_le_ppair {x₁ x₂ y₁ y₂ : V} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    ppair x₁ y₁ ≤ ppair x₂ y₂ :=
  le_trans (ppair_le_ppair_left hx y₁) (ppair_le_ppair_right x₂ hy)

lemma ppair_lt_ppair {x₁ x₂ y₁ y₂ : V} (hx : x₁ < x₂) (hy : y₁ < y₂) :
    ppair x₁ y₁ < ppair x₂ y₂ :=
  lt_trans (ppair_lt_ppair_left hx y₁) (ppair_lt_ppair_right x₂ hy)

/-- The polynomial bound `ppair x y ≤ (x + y + 1)²` (bit length at most doubles). -/
lemma ppair_le_sq_succ (x y : V) : ppair x y ≤ (x + y + 1) * (x + y + 1) := by
  have e : (x + y + 1) * (x + y + 1) = ppair x y + (x + (x + y) + 1) := by
    unfold ppair; ring
  rw [e]
  exact le_self_add

end ppair


/-! ### Constructors

Seven program shapes (tags `0`–`6`) and, since 2026-09-30 (Phase 2 of `SPRIME_SOURCE_OF_TRUTH.md`), the
three tau constructors of the engine (`.tvote`/`.sys`/`.selfIdx`, tags `7`–`9`) and the list cons
(tag `10`):

* `pTvote v θ p q = ppair 7 (ppair v (ppair θ (ppair p q))) + 1` — the weighted action vote (`v` a
  vote list, `θ` the threshold);
* `pSys d i = ppair 8 (ppair d i) + 1` — component `i` of the mutually-recursive system `d` (a member list);
* `pSelfIdx j = ppair 9 j + 1` — the system-level pronoun "member `j`";
* `pNil = 0`, `pCons x rest = ppair 10 (ppair x rest) + 1` — the list codes shared by member lists
  (`ProgList`) and vote lists (`VoteList`, whose entry is `ppair w I`).

**Why the cons is TAGGED** (a deviation from the phase-2 note, which wrote `ppair x rest + 1`): an
untagged cons collides with the program shapes — `pCons 3 p = pBot p`, the member list `[const D]` would
be `pBot 0` — and every fixpoint that must descend into a member list (`revalue`, `codeTerm`) would then
have two clauses for one code. With tag `10` the cons is an ordinary disjoint shape and every fixpoint
treats it structurally, in the same domain, with no mode bit. -/

noncomputable def pConst (a : V) : V := ppair 0 a + 1
noncomputable def pSelf : V := ppair 1 0 + 1
noncomputable def pOpp : V := ppair 2 0 + 1
noncomputable def pBot (p : V) : V := ppair 3 p + 1
noncomputable def pSim (p q : V) : V := ppair 4 (ppair p q) + 1
noncomputable def pIte (b a p q : V) : V := ppair 5 (ppair b (ppair a (ppair p q))) + 1
noncomputable def pSearch (k g p q : V) : V := ppair 6 (ppair k (ppair g (ppair p q))) + 1
noncomputable def pTvote (v θ p q : V) : V := ppair 7 (ppair v (ppair θ (ppair p q))) + 1
noncomputable def pSys (d i : V) : V := ppair 8 (ppair d i) + 1
noncomputable def pSelfIdx (j : V) : V := ppair 9 j + 1
/-- The empty list. -/
abbrev pNil : V := 0
noncomputable def pCons (x rest : V) : V := ppair 10 (ppair x rest) + 1

section graphs

def pConstGraph : 𝚺₀.Semisentence 2 := .mkSigma “y a. ∃ y' < y, !ppairDef y' 0 a ∧ y = y' + 1”
instance pConst.defined : 𝚺₀-Function₁[V] pConst via pConstGraph := .mk fun v ↦ by
  simp_all [pConstGraph, pConst]

def pSelfGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !ppairDef y' 1 0 ∧ y = y' + 1”
def pOppGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !ppairDef y' 2 0 ∧ y = y' + 1”

def pBotGraph : 𝚺₀.Semisentence 2 := .mkSigma “y p. ∃ y' < y, !ppairDef y' 3 p ∧ y = y' + 1”
instance pBot.defined : 𝚺₀-Function₁[V] pBot via pBotGraph := .mk fun v ↦ by
  simp_all [pBotGraph, pBot]

def pSimGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y p q. ∃ y' < y, ∃ pq <⁺ y', !ppairDef pq p q ∧ !ppairDef y' 4 pq ∧ y = y' + 1”
instance pSim.defined : 𝚺₀-Function₂[V] pSim via pSimGraph := .mk fun v ↦ by
  simp_all [pSimGraph, pSim]

def pIteGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y b a p q. ∃ y' < y, ∃ bapq <⁺ y', ∃ apq <⁺ bapq, ∃ pq <⁺ apq,
    !ppairDef pq p q ∧ !ppairDef apq a pq ∧ !ppairDef bapq b apq ∧ !ppairDef y' 5 bapq ∧ y = y' + 1”
instance pIte.defined : 𝚺₀-Function₄ (pIte : V → V → V → V → V) via pIteGraph := .mk fun v ↦ by
  simp_all [pIteGraph, numeral_eq_natCast, pIte]

def pSearchGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y k g p q. ∃ y' < y, ∃ kgpq <⁺ y', ∃ gpq <⁺ kgpq, ∃ pq <⁺ gpq,
    !ppairDef pq p q ∧ !ppairDef gpq g pq ∧ !ppairDef kgpq k gpq ∧ !ppairDef y' 6 kgpq ∧ y = y' + 1”
instance pSearch.defined : 𝚺₀-Function₄ (pSearch : V → V → V → V → V) via pSearchGraph :=
  .mk fun v ↦ by simp_all [pSearchGraph, numeral_eq_natCast, pSearch]

def pTvoteGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y v th p q. ∃ y' < y, ∃ vtpq <⁺ y', ∃ tpq <⁺ vtpq, ∃ pq <⁺ tpq,
    !ppairDef pq p q ∧ !ppairDef tpq th pq ∧ !ppairDef vtpq v tpq ∧ !ppairDef y' 7 vtpq ∧ y = y' + 1”
instance pTvote.defined : 𝚺₀-Function₄ (pTvote : V → V → V → V → V) via pTvoteGraph :=
  .mk fun v ↦ by simp_all [pTvoteGraph, numeral_eq_natCast, pTvote]

def pSysGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y d i. ∃ y' < y, ∃ di <⁺ y', !ppairDef di d i ∧ !ppairDef y' 8 di ∧ y = y' + 1”
instance pSys.defined : 𝚺₀-Function₂[V] pSys via pSysGraph := .mk fun v ↦ by
  simp_all [pSysGraph, numeral_eq_natCast, pSys]

def pSelfIdxGraph : 𝚺₀.Semisentence 2 := .mkSigma “y j. ∃ y' < y, !ppairDef y' 9 j ∧ y = y' + 1”
instance pSelfIdx.defined : 𝚺₀-Function₁[V] pSelfIdx via pSelfIdxGraph := .mk fun v ↦ by
  simp_all [pSelfIdxGraph, numeral_eq_natCast, pSelfIdx]

def pConsGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y x r. ∃ y' < y, ∃ xr <⁺ y', !ppairDef xr x r ∧ !ppairDef y' 10 xr ∧ y = y' + 1”
instance pCons.defined : 𝚺₀-Function₂[V] pCons via pConsGraph := .mk fun v ↦ by
  simp_all [pConsGraph, numeral_eq_natCast, pCons]

end graphs

/-! ### Size facts (sub-programs are smaller than their parent) -/

@[simp] lemma p_lt_pBot (p : V) : p < pBot p :=
  le_iff_lt_succ.mp (le_ppair_right _ _)
@[simp] lemma p_lt_pSim (p q : V) : p < pSim p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma q_lt_pSim (p q : V) : q < pSim p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_right _ _) (le_ppair_right _ _)
@[simp] lemma b_lt_pIte (b a p q : V) : b < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma p_lt_pIte (b a p q : V) : p < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma q_lt_pIte (b a p q : V) : q < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_right _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma p_lt_pSearch (k g p q : V) : p < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma q_lt_pSearch (k g p q : V) : q < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_right _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma v_lt_pTvote (v θ p q : V) : v < pTvote v θ p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma θ_lt_pTvote (v θ p q : V) : θ < pTvote v θ p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma p_lt_pTvote (v θ p q : V) : p < pTvote v θ p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma q_lt_pTvote (v θ p q : V) : q < pTvote v θ p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_right _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma d_lt_pSys (d i : V) : d < pSys d i :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma i_lt_pSys (d i : V) : i < pSys d i :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_right _ _) (le_ppair_right _ _)
@[simp] lemma j_lt_pSelfIdx (j : V) : j < pSelfIdx j :=
  le_iff_lt_succ.mp (le_ppair_right _ _)
@[simp] lemma x_lt_pCons (x rest : V) : x < pCons x rest :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma rest_lt_pCons (x rest : V) : rest < pCons x rest :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_right _ _) (le_ppair_right _ _)

/-- A list code is `0` or strictly above every entry (`pCons` is above both components). -/
@[simp] lemma pCons_ne_zero (x rest : V) : pCons x rest ≠ 0 := fun h ↦ zero_ne_add_one _ h.symm
@[simp] lemma zero_ne_pCons (x rest : V) : (0 : V) ≠ pCons x rest := fun h ↦ zero_ne_add_one _ h

/-! ### Injectivity and disjointness of the constructors (the tag decides the shape) -/

section inj

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons

lemma pConst_inj {a a' : V} (h : pConst a = pConst a') : a = a' := by simpa using h
lemma pBot_inj {p p' : V} (h : pBot p = pBot p') : p = p' := by simpa using h
lemma pSim_inj {p q p' q' : V} (h : pSim p q = pSim p' q') : p = p' ∧ q = q' := by simpa using h
lemma pIte_inj {b a p q b' a' p' q' : V} (h : pIte b a p q = pIte b' a' p' q') :
    b = b' ∧ a = a' ∧ p = p' ∧ q = q' := by simpa [and_assoc] using h
lemma pSearch_inj {k g p q k' g' p' q' : V} (h : pSearch k g p q = pSearch k' g' p' q') :
    k = k' ∧ g = g' ∧ p = p' ∧ q = q' := by simpa [and_assoc] using h
lemma pTvote_inj {v θ p q v' θ' p' q' : V} (h : pTvote v θ p q = pTvote v' θ' p' q') :
    v = v' ∧ θ = θ' ∧ p = p' ∧ q = q' := by simpa [and_assoc] using h
lemma pSys_inj {d i d' i' : V} (h : pSys d i = pSys d' i') : d = d' ∧ i = i' := by simpa using h
lemma pSelfIdx_inj {j j' : V} (h : pSelfIdx j = pSelfIdx j') : j = j' := by simpa using h
lemma pCons_inj {x r x' r' : V} (h : pCons x r = pCons x' r') : x = x' ∧ r = r' := by simpa using h

end inj

/-! ### Re-valuing actions -/

/-- `0 ↦ u`, `1 ↦ w`, other values fixed. -/
noncomputable def revalueAction (a u w : V) : V := if a = 0 then u else if a = 1 then w else a

def revalueActionGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y a u w. (a = 0 → y = u) ∧ (a = 1 → y = w) ∧ (a ≠ 0 → a ≠ 1 → y = a)”

instance revalueAction.defined : 𝚺₀-Function₃ (revalueAction : V → V → V → V) via revalueActionGraph :=
  .mk fun v ↦ by
    suffices (v 1 = 0 → v 0 = v 2) ∧ (v 1 = 1 → v 0 = v 3) ∧ (v 1 ≠ 0 → v 1 ≠ 1 → v 0 = v 1) ↔
        v 0 = revalueAction (v 1) (v 2) (v 3) by simpa [revalueActionGraph]
    unfold revalueAction
    by_cases h0 : v 1 = 0
    · simp [h0]
    · by_cases h1 : v 1 = 1
      · simp [h0, h1]
      · simp [h0, h1]

/-- The action swap. -/
noncomputable abbrev swapAction (a : V) : V := revalueAction a 1 0

lemma revalueAction_le (a u w : V) : revalueAction a u w ≤ a + u + w := by
  unfold revalueAction
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h1]
    · simp [h0, h1]

@[simp] lemma revalueAction_zero_one (a : V) : revalueAction a 0 1 = a := by
  unfold revalueAction
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h0, h1]
    · simp [h0, h1]

@[simp] lemma swapAction_swapAction (a : V) : swapAction (swapAction a) = a := by
  unfold swapAction revalueAction
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h0, h1]
    · simp [h0, h1]

/-! ### Program shapes -/

/-- `x` is a constructor application (its immediate components are all `< x`). Eleven shapes: the seven
program constructors, the three tau constructors and the list cons; `pNil = 0` is not a shape. -/
def IsShape (x : V) : Prop :=
  (∃ a, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p, x = pBot p) ∨ (∃ p q, x = pSim p q) ∨
  (∃ b a p q, x = pIte b a p q) ∨ (∃ k g p q, x = pSearch k g p q) ∨
  (∃ v θ p q, x = pTvote v θ p q) ∨ (∃ d i, x = pSys d i) ∨ (∃ j, x = pSelfIdx j) ∨ (∃ e r, x = pCons e r)

def isShape : 𝚺₀.Semisentence 1 := .mkSigma
  “x. (∃ a < x, !pConstGraph x a) ∨ !pSelfGraph x ∨ !pOppGraph x ∨ (∃ p < x, !pBotGraph x p) ∨
    (∃ p < x, ∃ q < x, !pSimGraph x p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q) ∨
    (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q) ∨
    (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q) ∨
    (∃ d < x, ∃ i < x, !pSysGraph x d i) ∨ (∃ j < x, !pSelfIdxGraph x j) ∨
    (∃ e < x, ∃ r < x, !pConsGraph x e r)”

@[simp] lemma a_lt_pConst (a : V) : a < pConst a := le_iff_lt_succ.mp (le_ppair_right _ _)
@[simp] lemma a_lt_pIte (b a p q : V) : a < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma k_lt_pSearch (k g p q : V) : k < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma g_lt_pSearch (k g p q : V) : g < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _)) (le_ppair_right _ _)

/-- The eleven shape introductions. -/
lemma IsShape.const (a : V) : IsShape (pConst a) := Or.inl ⟨a, rfl⟩
lemma IsShape.self : IsShape (pSelf : V) := Or.inr (Or.inl rfl)
lemma IsShape.opp : IsShape (pOpp : V) := Or.inr (Or.inr (Or.inl rfl))
lemma IsShape.bot (p : V) : IsShape (pBot p) := Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
lemma IsShape.sim (p q : V) : IsShape (pSim p q) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))
lemma IsShape.ite (b a p q : V) : IsShape (pIte b a p q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))
lemma IsShape.search (k g p q : V) : IsShape (pSearch k g p q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, rfl⟩))))))
lemma IsShape.tvote (v θ p q : V) : IsShape (pTvote v θ p q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, rfl⟩)))))))
lemma IsShape.sys (d i : V) : IsShape (pSys d i) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, i, rfl⟩))))))))
lemma IsShape.selfIdx (j : V) : IsShape (pSelfIdx j) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
lemma IsShape.cons (e r : V) : IsShape (pCons e r) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, r, rfl⟩)))))))))

lemma isShape_iff (x : V) :
    IsShape x ↔
    (∃ a < x, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p < x, x = pBot p) ∨
    (∃ p < x, ∃ q < x, x = pSim p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q) ∨
    (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q) ∨
    (∃ v < x, ∃ θ < x, ∃ p < x, ∃ q < x, x = pTvote v θ p q) ∨
    (∃ d < x, ∃ i < x, x = pSys d i) ∨ (∃ j < x, x = pSelfIdx j) ∨ (∃ e < x, ∃ r < x, x = pCons e r) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
      ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩)
    · exact Or.inl ⟨a, by simp, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, by simp, θ, by simp, p, by simp, q, by simp, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, by simp, i, by simp, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, by simp, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e, by simp, r, by simp, rfl⟩)))))))))
  · rintro (⟨a, _, rfl⟩ | rfl | rfl | ⟨p, _, rfl⟩ | ⟨p, _, q, _, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl⟩ | ⟨k, _, g, _, p, _, q, _, rfl⟩ | ⟨v, _, θ, _, p, _, q, _, rfl⟩ |
      ⟨d, _, i, _, rfl⟩ | ⟨j, _, rfl⟩ | ⟨e, _, r, _, rfl⟩)
    · exact IsShape.const a
    · exact IsShape.self
    · exact IsShape.opp
    · exact IsShape.bot p
    · exact IsShape.sim p q
    · exact IsShape.ite b a p q
    · exact IsShape.search k g p q
    · exact IsShape.tvote v θ p q
    · exact IsShape.sys d i
    · exact IsShape.selfIdx j
    · exact IsShape.cons e r

lemma lt_and_eq_succ_iff {a y : V} : (a < y ∧ y = a + 1) ↔ y = a + 1 :=
  ⟨And.right, fun h ↦ ⟨by rw [h]; exact lt_add_one a, h⟩⟩

instance IsShape.defined : 𝚺₀-Predicate[V] IsShape via isShape := .mk fun v ↦ by
  simp [isShape, isShape_iff, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]

/-- `0` is not a shape (every shape is a successor). -/
lemma not_isShape_zero : ¬IsShape (0 : V) := by
  rintro (⟨a, h⟩ | h | h | ⟨p, h⟩ | ⟨p, q, h⟩ | ⟨b, a, p, q, h⟩ | ⟨k, g, p, q, h⟩ |
    ⟨v, θ, p, q, h⟩ | ⟨d, i, h⟩ | ⟨j, h⟩ | ⟨e, r, h⟩) <;>
    exact zero_ne_add_one _ h

/-! ### Re-valuing every action of a program: a fixpoint on pairs `⟪x, y⟫` with parameters `u w`

The search clause re-values the stored template through `revalueTemplate u w` (a Σ₁
function), so the core is Δ₁ (both polarities cite `revalueTemplateGraph`, exactly like the
guard code in `ArithS.Eval`) rather than Δ₀; the fixpoint is still StrongFinite, since the
sub-results referenced are `⟪p, p'⟫` with `p < x` and `p' < y`.

The tau clauses (2026-09-30): `pTvote v θ p q ↦ pTvote v θ p' q'` — the ENTRIES are frozen, exactly as
the engine's `τ̂` freezes a `VoteList` (`Base/Transpose`); `pSys d i ↦ pSys d' i` re-values the whole
member list (structurally, through the `pCons` clause `pCons x r ↦ pCons x' r'`, which is why the cons is
a tagged shape); `pSelfIdx j` is fixed (a reference carries no action). -/

namespace Revalue

/-- `Phi ![u, w] C ⟪x, y⟫`: `y` is `x` with actions re-valued `0 ↦ u, 1 ↦ w`, given the
sub-results in `C`. -/
def Phi (param : Fin 2 → V) (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪pConst a, pConst (revalueAction a (param 0) (param 1))⟫) ∨
  pr = ⟪pSelf, pSelf⟫ ∨ pr = ⟪pOpp, pOpp⟫ ∨
  (∃ p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪pBot p, pBot p'⟫) ∨
  (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨
  (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pIte b a p q, pIte b' (revalueAction a (param 0) (param 1)) p' q'⟫) ∨
  (∃ k g p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, pSearch k (revalueTemplate (param 0) (param 1) g) p' q'⟫) ∨
  (∃ v θ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pTvote v θ p q, pTvote v θ p' q'⟫) ∨
  (∃ d i d', ⟪d, d'⟫ ∈ C ∧ pr = ⟪pSys d i, pSys d' i⟫) ∨
  (∃ j, pr = ⟪pSelfIdx j, pSelfIdx j⟫) ∨
  (∃ e r e' r', ⟪e, e'⟫ ∈ C ∧ ⟪r, r'⟫ ∈ C ∧ pr = ⟪pCons e r, pCons e' r'⟫) ∨
  (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C u w. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ ∃ a' <⁺ a + u + w, !revalueActionGraph a' a u w ∧ !pConstGraph y a') ∨
      (!pSelfGraph x ∧ !pSelfGraph y) ∨
      (!pOppGraph x ∧ !pOppGraph y) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ a' <⁺ a + u + w, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !revalueActionGraph a' a u w ∧ !pIteGraph y b' a' p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ g', !revalueTemplateGraph g' u w g ∧ ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pTvoteGraph y v th p' q') ∨
      (∃ d < x, ∃ i < x, !pSysGraph x d i ∧ ∃ d' < y, :⟪d, d'⟫:∈ C ∧ !pSysGraph y d' i) ∨
      (∃ j < x, !pSelfIdxGraph x j ∧ !pSelfIdxGraph y j) ∨
      (∃ e < x, ∃ r < x, !pConsGraph x e r ∧
        ∃ e' < y, ∃ r' < y, :⟪e, e'⟫:∈ C ∧ :⟪r, r'⟫:∈ C ∧ !pConsGraph y e' r') ∨
      (¬!isShape x ∧ y = x) )”)
  (.mkPi “pr C u w. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ ∃ a' <⁺ a + u + w, !revalueActionGraph a' a u w ∧ !pConstGraph y a') ∨
      (!pSelfGraph x ∧ !pSelfGraph y) ∨
      (!pOppGraph x ∧ !pOppGraph y) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ a' <⁺ a + u + w, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !revalueActionGraph a' a u w ∧ !pIteGraph y b' a' p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∀ g', !revalueTemplateGraph g' u w g → ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pTvoteGraph y v th p' q') ∨
      (∃ d < x, ∃ i < x, !pSysGraph x d i ∧ ∃ d' < y, :⟪d, d'⟫:∈ C ∧ !pSysGraph y d' i) ∨
      (∃ j < x, !pSelfIdxGraph x j ∧ !pSelfIdxGraph y j) ∨
      (∃ e < x, ∃ r < x, !pConsGraph x e r ∧
        ∃ e' < y, ∃ r' < y, :⟪e, e'⟫:∈ C ∧ :⟪r, r'⟫:∈ C ∧ !pConsGraph y e' r') ∨
      (¬!isShape x ∧ y = x) )”)⟩

private lemma phi_iff (param : Fin 2 → V) (C pr : V) :
    Phi param {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧
    ( (∃ a < x, x = pConst a ∧ ∃ a' ≤ a + param 0 + param 1, a' = revalueAction a (param 0) (param 1) ∧ y = pConst a') ∨
      (x = pSelf ∧ y = pSelf) ∨
      (x = pOpp ∧ y = pOpp) ∨
      (∃ p < x, x = pBot p ∧ ∃ p' < y, ⟪p, p'⟫ ∈ C ∧ y = pBot p') ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSim p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ b' < y, ∃ a' ≤ a + param 0 + param 1, ∃ p' < y, ∃ q' < y,
          ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ a' = revalueAction a (param 0) (param 1) ∧
          y = pIte b' a' p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ p' < y, ∃ q' < y,
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSearch k (revalueTemplate (param 0) (param 1) g) p' q') ∨
      (∃ v < x, ∃ θ < x, ∃ p < x, ∃ q < x, x = pTvote v θ p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pTvote v θ p' q') ∨
      (∃ d < x, ∃ i < x, x = pSys d i ∧ ∃ d' < y, ⟪d, d'⟫ ∈ C ∧ y = pSys d' i) ∨
      (∃ j < x, x = pSelfIdx j ∧ y = pSelfIdx j) ∨
      (∃ e < x, ∃ r < x, x = pCons e r ∧
        ∃ e' < y, ∃ r' < y, ⟪e, e'⟫ ∈ C ∧ ⟪r, r'⟫ ∈ C ∧ y = pCons e' r') ∨
      (¬IsShape x ∧ y = x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ |
      ⟨v, θ, p, q, p', q', hp, hq, rfl⟩ | ⟨d, i, d', hd, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, e', r', he, hr, rfl⟩ |
      ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, _, revalueAction_le _ _ _, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, rfl, p', by simp, h, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, p', by simp, q', by simp, hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl, b', by simp, _, revalueAction_le _ _ _,
          p', by simp, q', by simp, hb, hp, hq, rfl, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, by simp, θ, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩)))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, by simp, i, by simp, rfl, d', by simp, hd, rfl⟩))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, by simp, rfl, rfl⟩)))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, by simp, r, by simp, rfl, e', by simp, r', by simp, he, hr, rfl⟩))))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))))))⟩
  · rintro ⟨x, _, y, _, rfl, (⟨a, _, rfl, a', _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, p', _, h, rfl⟩ | ⟨p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, b', _, a', _, p', _, q', _, hb, hp, hq, rfl, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨v, _, θ, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨d, _, i, _, rfl, d', _, hd, rfl⟩ | ⟨j, _, rfl, rfl⟩ |
      ⟨e, _, r, _, rfl, e', _, r', _, he, hr, rfl⟩ | ⟨hx, hyx⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q', hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, p', q', hp, hq, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, i, d', hd, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, r, e', r', he, hr, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, by rw [hyx]⟩))))))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, revalueTemplate.defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, revalueTemplate.defined.df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (fun i ↦ v i.succ.succ) (v 1) (v 0)
  monotone := by
    rintro C C' hC param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ |
      ⟨v, θ, p, q, p', q', hp, hq, rfl⟩ | ⟨d, i, d', hd, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, e', r', he, hr, rfl⟩ |
      ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, b', p', q', hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, p', q', hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, θ, p, q, p', q', hC hp, hC hq, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, i, d', hC hd, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, r, e', r', hC he, hC hr, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, rfl⟩))))))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ |
      ⟨v, θ, p, q, p', q', hp, hq, rfl⟩ | ⟨d, i, d', hd, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, e', r', he, hr, rfl⟩ |
      ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', ⟨h, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q',
        ⟨hb, pair_lt_pair (by simp) (by simp)⟩, ⟨hp, pair_lt_pair (by simp) (by simp)⟩,
        ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, i, d',
        ⟨hd, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, r, e', r', ⟨he, pair_lt_pair (by simp) (by simp)⟩, ⟨hr, pair_lt_pair (by simp) (by simp)⟩,
          rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, rfl⟩))))))))))

end Revalue

/-- `RevalueGraph u w x y`: `y` is `x` with actions re-valued `0 ↦ u, 1 ↦ w`. -/
def RevalueGraph (u w x y : V) : Prop := Revalue.construction.Fixpoint ![u, w] ⟪x, y⟫

noncomputable def revalueGraphDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “u w x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !Revalue.blueprint.fixpointDefΔ₁.sigma pr u w”)
  (.mkPi “u w x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !Revalue.blueprint.fixpointDefΔ₁.pi pr u w”)

private lemma revalue_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2] := by
  funext i; fin_cases i <;> rfl

instance revalueGraph_defined : 𝚫₁-Relation₄[V] RevalueGraph via revalueGraphDef := .mk
  ⟨by intro v
      simp [revalueGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Revalue.construction.fixpoint_definedΔ₁.proper.iff', Revalue.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [revalue_param_eq] using h
      · intro h; have := h ⟪v 2, v 3⟫ (by simp) rfl; simpa [revalue_param_eq] using this,
   by intro v
      simp [revalueGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Revalue.construction.fixpoint_definedΔ₁.df, RevalueGraph]⟩

instance revalueGraph_definable : 𝚫₁-Relation₄[V] RevalueGraph := revalueGraph_defined.to_definable

instance revalueGraph_definable' : Γ-[m + 1]-Relation₄[V] RevalueGraph :=
  revalueGraph_definable.of_deltaOne

lemma RevalueGraph.case_iff {u w x y : V} :
    RevalueGraph u w x y ↔
    (∃ a, x = pConst a ∧ y = pConst (revalueAction a u w)) ∨
    (x = pSelf ∧ y = pSelf) ∨ (x = pOpp ∧ y = pOpp) ∨
    (∃ p p', RevalueGraph u w p p' ∧ x = pBot p ∧ y = pBot p') ∨
    (∃ p q p' q', RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', RevalueGraph u w b b' ∧ RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧
      x = pIte b a p q ∧ y = pIte b' (revalueAction a u w) p' q') ∨
    (∃ k g p q p' q', RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧
      x = pSearch k g p q ∧ y = pSearch k (revalueTemplate u w g) p' q') ∨
    (∃ v θ p q p' q', RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧
      x = pTvote v θ p q ∧ y = pTvote v θ p' q') ∨
    (∃ d i d', RevalueGraph u w d d' ∧ x = pSys d i ∧ y = pSys d' i) ∨
    (∃ j, x = pSelfIdx j ∧ y = pSelfIdx j) ∨
    (∃ e r e' r', RevalueGraph u w e e' ∧ RevalueGraph u w r r' ∧ x = pCons e r ∧ y = pCons e' r') ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans Revalue.construction.case (by simp [Revalue.construction, Revalue.Phi, RevalueGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons IsShape

lemma RevalueGraph.const_iff {u w a y : V} :
    RevalueGraph u w (pConst a) y ↔ y = pConst (revalueAction a u w) := by
  rw [RevalueGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma RevalueGraph.self_iff {u w y : V} : RevalueGraph u w pSelf y ↔ y = pSelf := by
  rw [RevalueGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ _ _ _ _ h; exact absurd h.symm h₁
lemma RevalueGraph.opp_iff {u w y : V} : RevalueGraph u w pOpp y ↔ y = pOpp := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ _ _ _ _ h; exact absurd h.symm h₂
lemma RevalueGraph.bot_iff {u w p y : V} :
    RevalueGraph u w (pBot p) y ↔ ∃ p', RevalueGraph u w p p' ∧ y = pBot p' := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ _ _ _ _ h; exact absurd h.symm (h₃ p)
lemma RevalueGraph.sim_iff {u w p q y : V} :
    RevalueGraph u w (pSim p q) y ↔
    ∃ p' q', RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧ y = pSim p' q' := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ _ _ _ _ h; exact absurd h.symm (h₄ p q)
lemma RevalueGraph.ite_iff {u w b a p q y : V} :
    RevalueGraph u w (pIte b a p q) y ↔
    ∃ b' p' q', RevalueGraph u w b b' ∧ RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧
      y = pIte b' (revalueAction a u w) p' q' := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ _ _ _ _ h; exact absurd h.symm (h₅ b a p q)
lemma RevalueGraph.search_iff {u w k g p q y : V} :
    RevalueGraph u w (pSearch k g p q) y ↔
    ∃ p' q', RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧ y = pSearch k (revalueTemplate u w g) p' q' := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ _ _ _ _ h; exact absurd h.symm (h₆ k g p q)
lemma RevalueGraph.tvote_iff {u w v θ p q y : V} :
    RevalueGraph u w (pTvote v θ p q) y ↔
    ∃ p' q', RevalueGraph u w p p' ∧ RevalueGraph u w q q' ∧ y = pTvote v θ p' q' := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ h₇ _ _ _ h; exact absurd h.symm (h₇ v θ p q)
lemma RevalueGraph.sys_iff {u w d i y : V} :
    RevalueGraph u w (pSys d i) y ↔ ∃ d', RevalueGraph u w d d' ∧ y = pSys d' i := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ _ h₈ _ _ h; exact absurd h.symm (h₈ d i)
lemma RevalueGraph.selfIdx_iff {u w j y : V} : RevalueGraph u w (pSelfIdx j) y ↔ y = pSelfIdx j := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ _ _ h₉ _ h; exact absurd h.symm (h₉ j)
lemma RevalueGraph.cons_iff {u w e r y : V} :
    RevalueGraph u w (pCons e r) y ↔
    ∃ e' r', RevalueGraph u w e e' ∧ RevalueGraph u w r r' ∧ y = pCons e' r' := by
  rw [RevalueGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ _ _ _ h₁₀ h; exact absurd h.symm (h₁₀ e r)
lemma RevalueGraph.of_not_shape {u w x y : V} (hx : ¬IsShape x) : RevalueGraph u w x y ↔ y = x := by
  rw [RevalueGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, p', _, rfl, _⟩ | ⟨p, q, p', q', _, _, rfl, _⟩ |
      ⟨b, a, p, q, b', p', q', _, _, _, rfl, _⟩ | ⟨k, g, p, q, p', q', _, _, rfl, _⟩ |
      ⟨v, θ, p, q, p', q', _, _, rfl, _⟩ | ⟨d, i, d', _, rfl, _⟩ | ⟨j, rfl, _⟩ |
      ⟨e, r, e', r', _, _, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (IsShape.const a) hx
    · exact absurd IsShape.self hx
    · exact absurd IsShape.opp hx
    · exact absurd (IsShape.bot p) hx
    · exact absurd (IsShape.sim p q) hx
    · exact absurd (IsShape.ite b a p q) hx
    · exact absurd (IsShape.search k g p q) hx
    · exact absurd (IsShape.tvote v θ p q) hx
    · exact absurd (IsShape.sys d i) hx
    · exact absurd (IsShape.selfIdx j) hx
    · exact absurd (IsShape.cons e r) hx
    · exact h.symm
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hx, rfl⟩))))))))))

end inversion

/-! ### `revalue` is a total Σ₁ function -/

lemma revalueGraph_exists (u w x : V) : ∃ y, RevalueGraph u w x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · exact ⟨_, RevalueGraph.const_iff.mpr rfl⟩
      · exact ⟨_, RevalueGraph.self_iff.mpr rfl⟩
      · exact ⟨_, RevalueGraph.opp_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp)
        exact ⟨_, RevalueGraph.bot_iff.mpr ⟨p', hp, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RevalueGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RevalueGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RevalueGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RevalueGraph.tvote_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨d', hd⟩ := ih d (by simp)
        exact ⟨_, RevalueGraph.sys_iff.mpr ⟨d', hd, rfl⟩⟩
      · exact ⟨_, RevalueGraph.selfIdx_iff.mpr rfl⟩
      · obtain ⟨e', he⟩ := ih e (by simp); obtain ⟨r', hr⟩ := ih r (by simp)
        exact ⟨_, RevalueGraph.cons_iff.mpr ⟨e', r', he, hr, rfl⟩⟩
    · exact ⟨x, (RevalueGraph.of_not_shape hx).mpr rfl⟩

lemma revalueGraph_unique (u w x : V) :
    ∀ y₁ y₂, RevalueGraph u w x y₁ → RevalueGraph u w x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [RevalueGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [RevalueGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [RevalueGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases RevalueGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases RevalueGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases RevalueGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases RevalueGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases RevalueGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases RevalueGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases RevalueGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases RevalueGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases RevalueGraph.tvote_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases RevalueGraph.tvote_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases RevalueGraph.sys_iff.mp h₁ with ⟨d₁, hd₁, rfl⟩
        rcases RevalueGraph.sys_iff.mp h₂ with ⟨d₂, hd₂, rfl⟩
        rw [ih d (by simp) _ _ hd₁ hd₂]
      · rw [RevalueGraph.selfIdx_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases RevalueGraph.cons_iff.mp h₁ with ⟨e₁, r₁, he₁, hr₁, rfl⟩
        rcases RevalueGraph.cons_iff.mp h₂ with ⟨e₂, r₂, he₂, hr₂, rfl⟩
        rw [ih e (by simp) _ _ he₁ he₂, ih r (by simp) _ _ hr₁ hr₂]
    · rw [RevalueGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma revalueGraph_existsUnique (u w x : V) : ∃! y, RevalueGraph u w x y := by
  rcases revalueGraph_exists u w x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ revalueGraph_unique u w x y' y h' hy)

/-- Re-value every action of a program: `0 ↦ u`, `1 ↦ w`. -/
noncomputable def revalue (u w x : V) : V := Classical.choose! (revalueGraph_existsUnique u w x)

lemma revalue_graph (u w x : V) : RevalueGraph u w x (revalue u w x) :=
  Classical.choose!_spec (revalueGraph_existsUnique u w x)

lemma revalue_eq_of_graph {u w x y : V} (h : RevalueGraph u w x y) : revalue u w x = y :=
  revalueGraph_unique u w x _ _ (revalue_graph u w x) h

noncomputable def revalueDef : 𝚺₁.Semisentence 4 := .mkSigma “y u w x. !revalueGraphDef.sigma u w x y”

instance revalue_defined : 𝚺₁-Function₃ (revalue : V → V → V → V) via revalueDef := .mk fun v ↦ by
  simp [revalueDef, HierarchySymbol.Semiformula.val_sigma, revalueGraph_defined.df]
  constructor
  · intro h; exact (revalue_eq_of_graph h).symm
  · intro h; rw [h]; exact revalue_graph _ _ _

instance revalue_definable : 𝚺₁-Function₃ (revalue : V → V → V → V) := revalue_defined.to_definable

instance revalue_definable' : Γ-[m + 1]-Function₃ (revalue : V → V → V → V) :=
  revalue_definable.of_sigmaOne

@[simp] lemma revalue_const (u w a : V) : revalue u w (pConst a) = pConst (revalueAction a u w) :=
  revalue_eq_of_graph (RevalueGraph.const_iff.mpr rfl)
@[simp] lemma revalue_self (u w : V) : revalue u w (pSelf : V) = pSelf :=
  revalue_eq_of_graph (RevalueGraph.self_iff.mpr rfl)
@[simp] lemma revalue_opp (u w : V) : revalue u w (pOpp : V) = pOpp :=
  revalue_eq_of_graph (RevalueGraph.opp_iff.mpr rfl)
@[simp] lemma revalue_bot (u w p : V) : revalue u w (pBot p) = pBot (revalue u w p) :=
  revalue_eq_of_graph (RevalueGraph.bot_iff.mpr ⟨_, revalue_graph u w p, rfl⟩)
@[simp] lemma revalue_sim (u w p q : V) :
    revalue u w (pSim p q) = pSim (revalue u w p) (revalue u w q) :=
  revalue_eq_of_graph (RevalueGraph.sim_iff.mpr ⟨_, _, revalue_graph u w p, revalue_graph u w q, rfl⟩)
@[simp] lemma revalue_ite (u w b a p q : V) :
    revalue u w (pIte b a p q) = pIte (revalue u w b) (revalueAction a u w) (revalue u w p) (revalue u w q) :=
  revalue_eq_of_graph (RevalueGraph.ite_iff.mpr
    ⟨_, _, _, revalue_graph u w b, revalue_graph u w p, revalue_graph u w q, rfl⟩)
@[simp] lemma revalue_search (u w k g p q : V) :
    revalue u w (pSearch k g p q) = pSearch k (revalueTemplate u w g) (revalue u w p) (revalue u w q) :=
  revalue_eq_of_graph (RevalueGraph.search_iff.mpr
    ⟨_, _, revalue_graph u w p, revalue_graph u w q, rfl⟩)
/-- The vote's ENTRIES are frozen (the engine's `τ̂` on `.tvote`, `Base/Transpose`). -/
@[simp] lemma revalue_tvote (u w v θ p q : V) :
    revalue u w (pTvote v θ p q) = pTvote v θ (revalue u w p) (revalue u w q) :=
  revalue_eq_of_graph (RevalueGraph.tvote_iff.mpr
    ⟨_, _, revalue_graph u w p, revalue_graph u w q, rfl⟩)
/-- A system's MEMBERS are re-valued (the engine's `ProgList.transpose`). -/
@[simp] lemma revalue_sys (u w d i : V) : revalue u w (pSys d i) = pSys (revalue u w d) i :=
  revalue_eq_of_graph (RevalueGraph.sys_iff.mpr ⟨_, revalue_graph u w d, rfl⟩)
@[simp] lemma revalue_selfIdx (u w j : V) : revalue u w (pSelfIdx j) = pSelfIdx j :=
  revalue_eq_of_graph (RevalueGraph.selfIdx_iff.mpr rfl)
@[simp] lemma revalue_cons (u w e r : V) :
    revalue u w (pCons e r) = pCons (revalue u w e) (revalue u w r) :=
  revalue_eq_of_graph (RevalueGraph.cons_iff.mpr ⟨_, _, revalue_graph u w e, revalue_graph u w r, rfl⟩)
lemma revalue_of_not_shape {u w x : V} (hx : ¬IsShape x) : revalue u w x = x :=
  revalue_eq_of_graph ((RevalueGraph.of_not_shape hx).mpr rfl)
@[simp] lemma revalue_nil (u w : V) : revalue u w (pNil : V) = pNil := revalue_of_not_shape not_isShape_zero

/-- Re-valuing with `(0, 1)` is the identity. -/
theorem revalue_zero_one (x : V) : revalue 0 1 x = x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · simp
      · simp
      · simp
      · simp [ih p (by simp)]
      · simp [ih p (by simp), ih q (by simp)]
      · simp [ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [ih p (by simp), ih q (by simp), revalueTemplate_zero_one]
      · simp [ih p (by simp), ih q (by simp)]
      · simp [ih d (by simp)]
      · simp
      · simp [ih e (by simp), ih r (by simp)]
    · rw [revalue_of_not_shape hx]

/-- The action swap on program codes: re-value with `(1, 0)`. -/
noncomputable abbrev transposeCode (x : V) : V := revalue 1 0 x

/-- τ is an involution on codes. -/
theorem transposeCode_transposeCode (x : V) : transposeCode (transposeCode x) = x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode, ih p (by simp)]
      · simp [transposeCode, ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih p (by simp), ih q (by simp), revalueTemplate_swap_swap]
      · simp [transposeCode, ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih d (by simp)]
      · simp [transposeCode]
      · simp [transposeCode, ih e (by simp), ih r (by simp)]
    · simp only [transposeCode]; rw [revalue_of_not_shape hx, revalue_of_not_shape hx]

end ArithS
