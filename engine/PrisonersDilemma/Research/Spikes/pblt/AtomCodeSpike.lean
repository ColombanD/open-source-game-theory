import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic
import PrisonersDilemma.Program

/-!
Spike: a concrete, provably injective Gödel code for the engine `Formula`
(and its carried `Prog`s). Head-tagged `Nat.pair` scheme, mutually recursive
`progCode`/`formulaCode`, proven mutually injective.
-/

namespace PD.AtomCodeSpike
open PD

/-- `Action → Nat`, injective (2 constructors). -/
def actCode : Action → Nat
  | .C => 0
  | .D => 1

theorem actCode_inj : Function.Injective actCode := by
  intro a b h; cases a <;> cases b <;> simp_all [actCode]

mutual
  def progCode : Prog → Nat
    | .const a        => Nat.pair 0 (actCode a)
    | .self           => Nat.pair 1 0
    | .opp            => Nat.pair 2 0
    | .bot p          => Nat.pair 3 (progCode p)
    | .sim p q        => Nat.pair 4 (Nat.pair (progCode p) (progCode q))
    | .ite b a p q    => Nat.pair 5 (Nat.pair (actCode a) (Nat.pair (progCode b) (Nat.pair (progCode p) (progCode q))))
    | .search k φ p q => Nat.pair 6 (Nat.pair k (Nat.pair (formulaCode φ) (Nat.pair (progCode p) (progCode q))))

  def formulaCode : Formula → Nat
    | .plays p q a => Nat.pair 0 (Nat.pair (progCode p) (Nat.pair (progCode q) (actCode a)))
    | .impl φ ψ    => Nat.pair 1 (Nat.pair (formulaCode φ) (formulaCode ψ))
    | .neg φ       => Nat.pair 2 (formulaCode φ)
    | .box k φ     => Nat.pair 3 (Nat.pair k (formulaCode φ))
    | .eq p q      => Nat.pair 4 (Nat.pair (progCode p) (progCode q))
end

mutual
  theorem progCode_inj : ∀ {p p' : Prog}, progCode p = progCode p' → p = p'
    | .const a, p', h => by
        cases p' with
        | const a' => simp only [progCode, Nat.pair_eq_pair] at h; rw [actCode_inj h.2]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .self, p', h => by
        cases p' with
        | self => rfl
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .opp, p', h => by
        cases p' with
        | opp => rfl
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .bot p, p', h => by
        cases p' with
        | bot p'' => simp only [progCode, Nat.pair_eq_pair] at h; rw [progCode_inj h.2]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .sim p q, p', h => by
        cases p' with
        | sim p'' q'' =>
            simp only [progCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hp, hq⟩ := h; rw [progCode_inj hp, progCode_inj hq]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .ite b a p q, p', h => by
        cases p' with
        | ite b'' a'' p'' q'' =>
            simp only [progCode, Nat.pair_eq_pair] at h
            obtain ⟨_, ha, hb, hp, hq⟩ := h
            rw [actCode_inj ha, progCode_inj hb, progCode_inj hp, progCode_inj hq]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .search k φ p q, p', h => by
        cases p' with
        | search k'' φ'' p'' q'' =>
            simp only [progCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hk, hφ, hp, hq⟩ := h
            rw [hk, formulaCode_inj hφ, progCode_inj hp, progCode_inj hq]
        | _ => simp only [progCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)

  theorem formulaCode_inj : ∀ {φ φ' : Formula}, formulaCode φ = formulaCode φ' → φ = φ'
    | .plays p q a, φ', h => by
        cases φ' with
        | plays p'' q'' a'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hp, hq, ha⟩ := h
            rw [progCode_inj hp, progCode_inj hq, actCode_inj ha]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .impl φ ψ, φ', h => by
        cases φ' with
        | impl φ'' ψ'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hφ, hψ⟩ := h; rw [formulaCode_inj hφ, formulaCode_inj hψ]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .neg φ, φ', h => by
        cases φ' with
        | neg φ'' => simp only [formulaCode, Nat.pair_eq_pair] at h; rw [formulaCode_inj h.2]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .box k φ, φ', h => by
        cases φ' with
        | box k'' φ'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hk, hφ⟩ := h; rw [hk, formulaCode_inj hφ]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
    | .eq p q, φ', h => by
        cases φ' with
        | eq p'' q'' =>
            simp only [formulaCode, Nat.pair_eq_pair] at h
            obtain ⟨_, hp, hq⟩ := h; rw [progCode_inj hp, progCode_inj hq]
        | _ => simp only [formulaCode, Nat.pair_eq_pair] at h; exact absurd h.1 (by decide)
end

theorem formulaCode_injective : Function.Injective formulaCode := fun _ _ h => formulaCode_inj h

#check @formulaCode_injective

end PD.AtomCodeSpike
