import PrisonersDilemma.Base.Transpose
import PrisonersDilemma.Dynamics

/-!
# Base/EvalTranspose — τ̂ commutes with evaluation (2026-10-19)

`Pf.transpose` (`Base/Transpose.lean`) says `S` is closed under the C/D transposition τ̂ at the
same budget. This file adds the DYNAMIC half: transposing both players and the body transposes the
play. Because `proofSearch` is `decide (Pf k ·)`, the `.search` clause consults the same boolean on
both sides (`proofSearch_transpose`); every other clause is structural. `.tvote` entries are
frozen under τ̂ and evaluated in their own closed frame, so the vote fires identically and only the
continuations transpose — the lemma therefore holds for EVERY program, vote players included.

Consumer: `Tau/Theorems/TauDIMDID/Helpers.lean` — τ(DIMDID) is τ̂(τ(CIMCIC)) template by template,
so every bit of DIMDID's row against a τ̂-closed part of the roster is CIMCIC's bit against the
transposed hypothesis, with the action swapped (`play_transpose`), and every proof-search bit is
CIMCIC's by `Pf.transpose_iff`.
-/

open PD

namespace PD

/-- `proofSearch` consults the same boolean on a transposed formula. -/
theorem proofSearch_transpose (k : Nat) (φ : Formula) :
    proofSearch k φ.transpose = proofSearch k φ := by
  unfold proofSearch
  exact decide_eq_decide.mpr (Pf.transpose_iff k φ).symm

/-- Member lookup through τ̂, in `Option.map` form (both the `some` and the `none` case). -/
theorem ProgList.get?_transpose_eq : ∀ (l : ProgList) (i : Nat),
    l.transpose.get? i = (l.get? i).map Prog.transpose
  | .nil, _ => by simp [ProgList.transpose, ProgList.get?]
  | .cons p _, 0 => by simp [ProgList.transpose, ProgList.get?]
  | .cons _ rest, n + 1 => by
      simp only [ProgList.transpose, ProgList.get?]
      exact ProgList.get?_transpose_eq rest n

/-- **τ̂ commutes with `eval`**: the play of the transposed match is the transposed play. -/
theorem eval_transpose : ∀ (n : Nat) (me opponent body : Prog),
    eval n me.transpose opponent.transpose body.transpose
      = (eval n me opponent body).map Action.swap
  | 0, _, _, _ => rfl
  | n + 1, me, opp, body => by
    cases body with
    | const a => rfl
    | self => exact eval_transpose n me opp me
    | opp => exact eval_transpose n me opp opp
    | bot p => exact eval_transpose n me opp p
    | sim p q =>
        show eval n (p.transpose.subst me.transpose opp.transpose)
            (q.transpose.subst me.transpose opp.transpose)
            (p.transpose.subst me.transpose opp.transpose)
          = (eval n (p.subst me opp) (q.subst me opp) (p.subst me opp)).map Action.swap
        rw [← Prog.subst_transpose, ← Prog.subst_transpose]
        exact eval_transpose n _ _ _
    | ite b a p q =>
        show (eval n me.transpose opp.transpose b.transpose >>= fun r =>
            if r == a.swap then eval n me.transpose opp.transpose p.transpose
            else eval n me.transpose opp.transpose q.transpose)
          = (eval n me opp b >>= fun r =>
            if r == a then eval n me opp p else eval n me opp q).map Action.swap
        rw [eval_transpose n me opp b]
        cases eval n me opp b with
        | none => rfl
        | some r =>
            show (if (r.swap == a.swap) = true then eval n me.transpose opp.transpose p.transpose
                else eval n me.transpose opp.transpose q.transpose)
              = (if (r == a) = true then eval n me opp p else eval n me opp q).map Action.swap
            rw [Action.swap_beq]
            cases hra : (r == a) <;>
              simp [hra, eval_transpose n me opp p, eval_transpose n me opp q]
    | search k φ p q =>
        show (if proofSearch k (φ.transpose.subst me.transpose opp.transpose)
            then eval n me.transpose opp.transpose p.transpose
            else eval n me.transpose opp.transpose q.transpose)
          = (if proofSearch k (φ.subst me opp) then eval n me opp p else eval n me opp q).map
              Action.swap
        rw [← Formula.subst_transpose, proofSearch_transpose]
        split
        · exact eval_transpose n me opp p
        · exact eval_transpose n me opp q
    | tvote v θ p q =>
        cases v with
        | nil =>
            show (if θ = 0 then eval n me.transpose opp.transpose p.transpose
                else eval n me.transpose opp.transpose q.transpose)
              = (if θ = 0 then eval n me opp p else eval n me opp q).map Action.swap
            split
            · exact eval_transpose n me opp p
            · exact eval_transpose n me opp q
        | cons w I rest =>
            show (if θ = 0 then eval n me.transpose opp.transpose p.transpose
                else match eval n (.bot I) (.bot I) I with
                  | some Action.C =>
                      eval n me.transpose opp.transpose (.tvote rest (θ - w) p.transpose q.transpose)
                  | some Action.D =>
                      eval n me.transpose opp.transpose (.tvote rest θ p.transpose q.transpose)
                  | none => none)
              = (if θ = 0 then eval n me opp p
                else match eval n (.bot I) (.bot I) I with
                  | some Action.C => eval n me opp (.tvote rest (θ - w) p q)
                  | some Action.D => eval n me opp (.tvote rest θ p q)
                  | none => none).map Action.swap
            split
            · exact eval_transpose n me opp p
            · cases eval n (.bot I) (.bot I) I with
              | none => rfl
              | some a =>
                  cases a
                  · exact eval_transpose n me opp (.tvote rest (θ - w) p q)
                  · exact eval_transpose n me opp (.tvote rest θ p q)
    | sys defs i =>
        show (match defs.transpose.get? i with
            | some p => eval n me.transpose opp.transpose (p.sysClose defs.transpose)
            | none => none)
          = (match defs.get? i with
            | some p => eval n me opp (p.sysClose defs)
            | none => none).map Action.swap
        rw [ProgList.get?_transpose_eq]
        cases defs.get? i with
        | none => rfl
        | some p =>
            simp only [Option.map_some]
            rw [← Prog.sysClose_transpose]
            exact eval_transpose n me opp (p.sysClose defs)
    | selfIdx j => rfl

/-- The `∃ N` play form, as the tau rows state it: a transposed instance plays the swapped action. -/
theorem plays_transpose {me opp body : Prog} {a : Action}
    (h : ∃ N, eval N me opp body = some a) :
    ∃ N, eval N me.transpose opp.transpose body.transpose = some a.swap := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [eval_transpose, hN]; rfl⟩

end PD
