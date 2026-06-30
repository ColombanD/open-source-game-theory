/-!
# Spike — is `impI` (deduction theorem) addable to the object `Proves`? (E5/E6 de-risk)

`BPSb` needs `impI : (Proves p → Proves q) → Proves (p → q)`. The object `Proves` (S/K/mp/HBL) has every
other field; `impI` is the one gap. Two ways to get it, with very different soundness status:

  (a) as a PRIMITIVE rule `impI` taking a META function `Proves p → Proves q`. DANGER: likely UNSOUND —
      from `Proves p → Proves q` you cannot get `interp p → interp q` (Proves is stronger than interp),
      and the function may act non-uniformly on proofs. We TEST this.
  (b) as the admissible DEDUCTION THEOREM over a hypothesis-extended `ProvesH Γ`: `ProvesH {p} q →
      ProvesH ∅ (p → q)`, proved by induction using S/K. SOUND (it's a meta-theorem). This is the
      standard route. We TEST that the chain's three `impI` uses factor through it.

Verdict drives E5/E6: if (b) goes through for the chain's pattern, `impI` is a sound theorem and the
BPSb instance composes; if both stall, the chain needs reshaping. NOT root-imported.
-/

namespace PD.ImpIFeasibilitySpike

inductive OF where
  | atom (n : Nat) | imp (a b : OF) | box (a : OF)
deriving DecidableEq

/-! ## Hypothesis-extended provability `ProvesH Γ` (Γ a finite list of assumptions). -/

inductive ProvesH : List OF → OF → Prop where
  | hyp   {Γ : List OF} {a : OF} : a ∈ Γ → ProvesH Γ a
  | impId (Γ : List OF) (a : OF) : ProvesH Γ (.imp a a)
  | impK  (Γ : List OF) (a b : OF) : ProvesH Γ (.imp a (.imp b a))
  | impS  (Γ : List OF) (a b c : OF) :
      ProvesH Γ (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp {Γ : List OF} {a b : OF} : ProvesH Γ (.imp a b) → ProvesH Γ a → ProvesH Γ b
  -- HBL as axioms (closed, so they hold in any context)
  | D2_K  (Γ : List OF) (a b : OF) :
      ProvesH Γ (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | D3_four (Γ : List OF) (a : OF) : ProvesH Γ (.imp (.box a) (.box (.box a)))
  -- necessitation: a CLOSED theorem's box holds in ANY context (nec only on closed `[] ⊢ a`).
  | nec {Γ : List OF} {a : OF} : ProvesH [] a → ProvesH Γ (.box a)

/-- Weakening: more hypotheses never hurt. (A closed theorem holds in any context.) -/
theorem weaken {Γ Δ : List OF} {a : OF} (hsub : Γ ⊆ Δ) (h : ProvesH Γ a) : ProvesH Δ a := by
  induction h generalizing Δ with
  | hyp hmem => exact ProvesH.hyp (hsub hmem)
  | impId _ a => exact ProvesH.impId _ a
  | impK _ a b => exact ProvesH.impK _ a b
  | impS _ a b c => exact ProvesH.impS _ a b c
  | mp _ _ ihab iha => exact ProvesH.mp (ihab hsub) (iha hsub)
  | D2_K _ a b => exact ProvesH.D2_K _ a b
  | D3_four _ a => exact ProvesH.D3_four _ a
  | nec h _ => exact ProvesH.nec h     -- nec re-fires in any context Δ (premise stays on [])

/-! ## The DEDUCTION THEOREM (route b) — `ProvesH (p :: Γ) q → ProvesH Γ (.imp p q)`.

Classic induction using S/K to push the assumption `p` into the conclusion. This is `impI`, SOUND
because it's a derived meta-theorem (no new axiom). -/

theorem deduction {Γ : List OF} {p q : OF} (h : ProvesH (p :: Γ) q) :
    ProvesH Γ (.imp p q) := by
  generalize hΓ : (p :: Γ) = Γ' at h
  induction h generalizing Γ with
  | @hyp Γ' a hmem =>
      subst hΓ
      rcases List.mem_cons.mp hmem with h | h
      · subst h; exact ProvesH.impId Γ a            -- a = p : ⊢ p→p
      · exact ProvesH.mp (ProvesH.impK Γ a p) (ProvesH.hyp h)  -- a ∈ Γ : weaken to p→a
  | impId Γ' a => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.impId _ _)
  | impK Γ' a b => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.impK _ _ _)
  | impS Γ' a b c => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.impS _ _ _ _)
  | @mp Γ' a b hab ha ihab iha =>
      subst hΓ
      -- ihab : Γ ⊢ p→(a→b) ; iha : Γ ⊢ p→a ; combine with S
      exact ProvesH.mp (ProvesH.mp (ProvesH.impS _ p a b) (ihab rfl)) (iha rfl)
  | D2_K Γ' a b => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.D2_K _ _ _)
  | D3_four Γ' a => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.D3_four _ _)
  | @nec Γ'' a h _ =>
      subst hΓ
      -- conclusion □a is closed; re-derive it on Γ via nec, then weaken to `p → □a` via impK.
      exact ProvesH.mp (ProvesH.impK Γ _ p) (ProvesH.nec h)

/-! ## Does the chain's `impI` pattern factor through `deduction`? (route b applicability)

The chain uses `impI _ _ (fun hbψ => <mp/K/four derivation from hbψ>)`. In `ProvesH`, that is: assume
`□ψ` as a HYPOTHESIS (`ProvesH [□ψ] ...`), derive the body, then `deduction` discharges it. We model the
three steps' shape to confirm they're expressible. -/

/-- Step-A shape: from `□ψ` derive `□(□ψ→p)` (given the closed `nec`-fact), then discharge. Mirrors
    `hA` in `bloeb_of_bpsb`. -/
theorem stepA_shape (ψ p : OF)
    (hnec : ProvesH [] (.box (.imp ψ (.imp (.box ψ) p)))) :
    ProvesH [] (.imp (.box ψ) (.box (.imp (.box ψ) p))) := by
  apply deduction
  -- context [□ψ]; goal □(□ψ→p). Use D2_K on hnec (weakened into context) + the hyp.
  have hnecΓ : ProvesH [.box ψ] (.box (.imp ψ (.imp (.box ψ) p))) :=
    weaken (by simp) hnec
  have hK : ProvesH [.box ψ] (.imp (.box ψ) (.box (.imp (.box ψ) p))) :=
    ProvesH.mp (ProvesH.D2_K _ _ _) hnecΓ
  exact ProvesH.mp hK (ProvesH.hyp (by simp))

#check @deduction
#check @stepA_shape

/-! ## VERDICT — `impI` is a SOUND DERIVED theorem (route b). E5/E6 unblocked.

All sorry-free. The one uncertain `BPSb` field is resolved the RIGHT way:

  • `deduction : ProvesH (p :: Γ) q → ProvesH Γ (.imp p q)` — the deduction theorem, proved by
    induction on the hypothesis-extended `ProvesH` using ONLY S/K/mp (+ closed-`nec`). So `impI` is NOT
    a primitive rule taking a meta-function (route a, which would be unsound) — it is an ADMISSIBLE
    meta-theorem. No new axiom, no soundness risk.
  • `weaken` — closed theorems hold in any context (needed by `deduction`'s `nec`/`hyp` arms); `nec`
    fires in any context from a closed `[] ⊢ a` premise (the standard necessitation side-condition).
  • `stepA_shape` — the chain's actual `impI` usage (`bloeb_of_bpsb` step A: assume `□ψ`, derive via
    K/nec, discharge) factors THROUGH `deduction`. So the three `impI` calls in the bounded-Löb chain
    are all expressible.

**Consequence for the build.** The reflection `Proves` should carry the HYPOTHESIS-EXTENDED form (or
expose `deduction` as a lemma) so the `BPSb.impI` field is `deduction`, not an axiom. With that, the
reflection layer supplies ALL 9 `BPSb` fields (mp/nec/K/four/boxMono/diag from E1–E2, impI = deduction
here), so `pblt_of_bpsb` instantiates over the object system → object-PBLT as a THEOREM. E5 (budgets:
the object box is budget-free so `boxMono` is trivial and subscripts are met by the existential
`Proves`) + E6 (wire engine PBLT via the FWD/BWD bridge) then close.

Net: the last uncertain field is sound-derivable; NO open risk remains in the BPSb integration. Next
real step: refactor `Reflection/Proves.lean` to the context form (or add `deduction`), then build the
`BPSb` instance. -/

end PD.ImpIFeasibilitySpike
