import PrisonersDilemma.BaseTheorems

/-!
# Soundness certificate for the proposed `searchElseChain` constructor

The rule reads a MIXED-POLARITY `.search` telescope: layers descend either the THEN
slot (recording a `.box` guard antecedent, exactly as `searchChain`) or the ELSE slot
(recording a `.neg` guard antecedent — the Σ₁ REFUTATION of the crossed guard, exactly
the premise shape `search_f` consumes at the `PlaysProof` level). Its interp-level
content, proved here against the UNCHANGED engine: if every recorded guard fact holds
— provable boxes for then-layers, true refutations for else-layers — then the player
really plays the plugged constant.

The layer type, plug, and guard reader are proposal-local definitions (additive; the
engine is not touched). On integration they would live next to `searchPlug`/
`ctxPlug` in `ProofSystem.lean`.
-/

open PD PD.BaseTheorems

namespace SearchElseChainProposal

/-- A mixed-polarity search layer: `thenL` descends the then-slot (the else branch
    `e` is recorded but not entered); `elseL` descends the else-slot (the then
    branch `p` is recorded but not entered). -/
inductive SearchLayer2 where
  | thenL (g : Nat) (ψ : Formula) (e : Prog)
  | elseL (g : Nat) (ψ : Formula) (p : Prog)

/-- Plug a program into the polarity-selected slot of each layer. -/
def plug2 : List SearchLayer2 → Prog → Prog
  | [], x => x
  | .thenL g ψ e :: L, x => .search g ψ (plug2 L x) e
  | .elseL g ψ p :: L, x => .search g ψ p (plug2 L x)

/-- The guard fact a layer contributes as an antecedent: a `.box` for a then-layer
    (the guard search must SUCCEED), a `.neg` for an else-layer (the guard is
    REFUTED — the Σ₁ certificate that forces the search to fail, by consistency). -/
def guard2 (me opponent : Prog) : SearchLayer2 → Formula
  | .thenL g ψ _ => .box g (ψ.subst me opponent)
  | .elseL _ ψ _ => .neg (ψ.subst me opponent)

def guards2 (me opponent : Prog) : List SearchLayer2 → List Formula
  | [] => []
  | hd :: L => guard2 me opponent hd :: guards2 me opponent L

/-- The mixed-polarity telescope eval induction (the else-frontier twin of
    `searchPlug_eval`/`ctxPlug_eval` in `Base/ValuationSoundness`): if every layer's
    guard fact holds, evaluation reaches the plugged constant. A then-layer's box
    gives `proofSearch = true` by `proofSearch_spec`; an else-layer's refutation
    gives `proofSearch = false` by SOUNDNESS (a guard proof would contradict the
    refutation's truth) — the same consistency argument that makes `search_f` sound. -/
theorem plug2_eval (me opponent : Prog) (a : Action) :
    ∀ (L : List SearchLayer2),
      (∀ ψ ∈ guards2 me opponent L, ψ.interp) →
      ∃ n, eval n me opponent (plug2 L (.const a)) = some a := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨1, rfl⟩
  | cons hd rest ih =>
      cases hd with
      | thenL g ψ e =>
          intro hg
          have hhead : Pf g (ψ.subst me opponent) := hg _ List.mem_cons_self
          have hps : proofSearch g (ψ.subst me opponent) = true :=
            (proofSearch_spec _ _).2 hhead
          obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
          refine ⟨n + 1, ?_⟩
          show eval (n + 1) me opponent (.search g ψ (plug2 rest (.const a)) e) = some a
          rw [eval, if_pos hps]
          exact hn
      | elseL g ψ p =>
          intro hg
          have hhead : ¬ (ψ.subst me opponent).interp := hg _ List.mem_cons_self
          have hps : proofSearch g (ψ.subst me opponent) = false := by
            cases hps : proofSearch g (ψ.subst me opponent) with
            | false => rfl
            | true => exact absurd (proofSearch_sound _ _ hps) hhead
          obtain ⟨n, hn⟩ := ih (fun ψ' h' => hg ψ' (List.mem_cons_of_mem _ h'))
          refine ⟨n + 1, ?_⟩
          show eval (n + 1) me opponent (.search g ψ p (plug2 rest (.const a))) = some a
          rw [eval, if_neg (by simp [hps])]
          exact hn

/-- **The certificate**: the proposed rule's conclusion is TRUE — for
    `me = plug2 (hd :: L) (.const a)`, the guard-fact chain implies `me` plays `a`.
    This is the exact interp-level content of the proposed constructor (the rule is
    premise-free; its cost side-condition — each else-layer pays its full failed
    budget, the `search_f` floor — does not affect truth, only provable-soundness
    and consistency of the budget dynamics). -/
theorem searchElseChain_sound (hd : SearchLayer2) (L : List SearchLayer2)
    (a : Action) (me opponent : Prog)
    (hme : me = plug2 (hd :: L) (.const a)) :
    (Formula.impl (guard2 me opponent hd)
      (implChain (guards2 me opponent L) (.plays me opponent a))).interp := by
  intro hhd
  refine implChain_interp (guards2 me opponent L) ?_
  intro hall
  have hcons : ∀ ψ ∈ guards2 me opponent (hd :: L), ψ.interp := by
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | h
    · exact hhd
    · exact hall _ h
  obtain ⟨n, hn⟩ := plug2_eval me opponent a (hd :: L) hcons
  exact ⟨n, by rw [← hme] at hn; simpa [play] using hn⟩

end SearchElseChainProposal
