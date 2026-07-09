import PrisonersDilemma.Decidability.T50InstanceLob

/-!
# Cut relevance IV — the falsification theorem.

`cutRelevance_modestGate_false`:
`(∃ m, Provable m tgtD) ∧ ∀ N m, ¬ ProvableG (modestGate N) m tgtD` —
the DupocBot self-cooperation fact is provable (bounded Löb) yet lies outside
the modest stratum at EVERY literal bound and budget. So the original
cut-relevance conjecture (`Provable → ProvableG (modestGate N₀)`) is FALSE, and
the instance gate (T50) is a genuine repair, not a convenience.

Mechanism: a modest-gated derivation of the plays-fact must end in an atom whose
`search_t` cite re-derives the SAME fact (the fixpoint's guard instance IS the
fact — no budget descent), or cut on the guard box (never `modestF`), or come
from a `Derivation` (impossible: its only census antecedent is the underivable
box). `ModChain` closes the impl-chain detours; the proof runs on the
`ProvableG` mutual recursor with fording motives.
-/

namespace PD.T51
open PD PD.T49 PD.T50

/-- Modest-antecedent implication chains ending in the Dupoc fact. -/
inductive ModChain : Formula → Prop where
  | base : ModChain tgtD
  | step {B C : Formula} : T43.modestF B = true → ModChain C → ModChain (.impl B C)

/-- The Dupoc fact is not modest (its frames carry the open guard). -/
theorem tgtD_not_modest : T43.modestF tgtD = false := by decide

/-- No census has a box consequent. -/
theorem DAnt_box_consequent : ∀ {B : Formula} {b : Nat} {ψ : Formula},
    PD.T48.DAnt B (.box b ψ) → False := by
  intro B b ψ h
  generalize hC : Formula.box b ψ = C at h
  induction h with
  | searchBr _ => exact Formula.noConfusion hC
  | botSearchSt _ => exact Formula.noConfusion hC
  | simSt _ => exact Formula.noConfusion hC
  | botSimSt _ => exact Formula.noConfusion hC
  | iteBr₁ _ => exact Formula.noConfusion hC
  | iteBr₂ _ => exact Formula.noConfusion hC
  | trans h1 h2 ih1 ih2 => exact ih2 hC

/-- Every census antecedent into a `ModChain` formula is THE guard box. -/
theorem DAnt_chain_to : ∀ {B C : Formula}, PD.T48.DAnt B C → ModChain C →
    B = .box kD tgtD := by
  intro B C h
  induction h with
  | searchBr hme =>
      intro hm
      cases hm with
      | base =>
          rw [show meD = Prog.search kD (.plays .opp .self .C)
                (.const .C) (.const .D) from rfl] at hme
          injection hme with h1 h2 h3 h4
          subst h1; subst h2
          rfl
  | botSearchSt hme =>
      intro hm
      cases hm with
      | base => exact absurd hme (by simp [meD, Bots.DupocBot])
  | simSt hme =>
      intro hm
      cases hm with
      | base => exact absurd hme (by simp [meD, Bots.DupocBot])
  | botSimSt hme =>
      intro hm
      cases hm with
      | base => exact absurd hme (by simp [meD, Bots.DupocBot])
  | iteBr₁ hme =>
      intro hm
      cases hm with
      | step _ htail =>
          cases htail with
          | base => exact absurd hme (by simp [meD, Bots.DupocBot])
  | iteBr₂ hme =>
      intro hm
      cases hm with
      | base => exact absurd hme (by simp [meD, Bots.DupocBot])
  | trans h1 h2 ih1 ih2 =>
      intro hm
      have hD := ih2 hm
      subst hD
      exact absurd h1 DAnt_box_consequent

/-- No `Derivation` concludes the Dupoc fact: its only census antecedent is the
    guard box, and no Derivation concludes a box. -/
theorem no_deriv_tgtD (d : Derivation tgtD) : False := by
  cases d with
  | modusPonens φ ψ d1 d2 =>
      have hant := PD.T48.derivation_impl_ant d1
      have := DAnt_chain_to hant ModChain.base
      subst this
      exact PD.T48.derivation_no_box d2

/-- No `Derivation` concludes a proper `ModChain` implication either: its census
    antecedent would be the guard box, which is not modest. -/
theorem no_deriv_chain {B C : Formula} (d : Derivation (.impl B C))
    (hB : T43.modestF B = true) (hC : ModChain C) : False := by
  have hant := PD.T48.derivation_impl_ant d
  have := DAnt_chain_to hant hC
  subst this
  simp [T43.modestF, tgtD_not_modest] at hB

/-- **THE REGRESS**: no modest-gated derivation concludes any `ModChain` formula —
    atoms re-cite the fact itself (structural descent through the recursor), cuts
    and census antecedents into the chain are the non-modest guard box, and
    Derivations are dead. Fording motives: the plays layer carries frame equations,
    the atom layer the chain itself. -/
theorem regress {N : Nat} {m : Nat} {C : Formula}
    (h : T42.ProvableG (T44.modestGate N) m C) : ModChain C → False := by
  refine T42.ProvableG.rec
    (motive_1 := fun me oppo body a n _ =>
      me = meD → oppo = meD →
      ((body = meD ∧ a = Action.C) → False) ∧
      (∀ c : Action, body = .const c → a = c))
    (motive_2 := fun _ φ _ => ModChain φ → False)
    (motive_3 := fun _ C _ => ModChain C → False)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?struct ?atom ?weaken ?sts ?itrans ?atomBox ?boxIntro ?app ?axK ?box4
    ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg h
  case const =>
      intro me oppo a h1 h2
      refine ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]), fun c hc => ?_⟩
      simp only [Prog.const.injEq] at hc
      exact hc
  case self =>
      intro me oppo a n _ ih h1 h2
      exact ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]),
        fun c hc => absurd hc (by simp)⟩
  case opp =>
      intro me oppo a n _ ih h1 h2
      exact ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]),
        fun c hc => absurd hc (by simp)⟩
  case bot =>
      intro me oppo p a n _ ih h1 h2
      exact ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]),
        fun c hc => absurd hc (by simp)⟩
  case sim =>
      intro a n me oppo p q _ ih h1 h2
      exact ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]),
        fun c hc => absurd hc (by simp)⟩
  case ite_t =>
      intro me oppo g r mm a' p a n q _ hr _ ihg ihp h1 h2
      exact ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]),
        fun c hc => absurd hc (by simp)⟩
  case ite_f =>
      intro me oppo g r mm a' q a n p _ hr _ ihg ihq h1 h2
      exact ⟨fun hb => absurd hb.1 (by simp [meD, Bots.DupocBot]),
        fun c hc => absurd hc (by simp)⟩
  case search_t =>
      intro kg me oppo p a n g q _ _ ihg ihp h1 h2
      subst h1; subst h2
      refine ⟨fun hb => ?_, fun c hc => absurd hc (by simp)⟩
      rw [show meD = Prog.search kD (.plays .opp .self .C)
            (.const .C) (.const .D) from rfl] at hb
      obtain ⟨hb, _⟩ := hb
      injection hb with e1 e2 e3 e4
      subst e1; subst e2
      exact ihg ModChain.base
  case search_f =>
      intro mrf me oppo q a n kg g p _ _ ihn ihq h1 h2
      subst h1; subst h2
      refine ⟨fun hb => ?_, fun c hc => absurd hc (by simp)⟩
      obtain ⟨hb, ha⟩ := hb
      rw [show meD = Prog.search kD (.plays .opp .self .C)
            (.const .C) (.const .D) from rfl] at hb
      injection hb with e1 e2 e3 e4
      have hd := (ihq rfl rfl).2 .D e4
      rw [ha] at hd
      exact Action.noConfusion hd
  case atomMk =>
      intro me oppo a n k _ hle ih hm
      cases hm with
      | base => exact (ih rfl rfl).1 ⟨rfl, rfl⟩
  case struct =>
      intro φ0 k0 hd hm
      cases hm with
      | base => obtain ⟨d, _⟩ := hd; exact no_deriv_tgtD d
      | step hB hC' => obtain ⟨d, _⟩ := hd; exact no_deriv_chain d hB hC'
  case atom =>
      intro k0 φ0 _ ih hm
      exact ih hm
  case weaken =>
      intro k A B mm _ hle ih hm
      cases hm with
      | step hB hC' => exact ih hC'
  case sts =>
      intro k k₁ k₂ mm ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih hm
      cases hm with
      | step hB htail =>
          cases htail with
          | base => exact absurd hme (by simp [meD, Bots.DupocBot])
  case itrans =>
      intro k A B C' a b _ _ hle hg ih1 ih2 hm
      cases hm with
      | step hB hC' => exact ih2 (ModChain.step hg.2 hC')
  case atomBox =>
      intro k kBox p q a _ hle ih hm
      cases hm with
      | step hB htail => cases htail
  case boxIntro =>
      intro kIn K A _ hle ih hm
      exact nomatch hm
  case app =>
      intro k m₁ m₂ A B _ _ hle hg ih1 ih2 hm
      exact ih1 (ModChain.step hg.2 hm)
  case axK =>
      intro a b c mm K A B _ hgate hle hg ih hm
      cases hm with
      | step hB htail => cases htail
  case box4 =>
      intro a b K A hgate hle hm
      cases hm with
      | step hB htail => cases htail
  case diagF =>
      intro pm fb g K tgt' _ hle hg ih hm
      cases hm with
      | step hB htail =>
          cases htail with
          | step hB2 htt =>
              have ht : T43.modestF tgt' = true := by
                simpa [T43.modestF] using hB2
              exact ih (ModChain.step (by simpa [T43.modestF] using ht) htt)
  case diagB =>
      intro pm fb g K tgt' _ hle hg ih hm
      cases hm with
      | step hB htail => cases htail
  case axKf =>
      intro a b c K A B hgate hle hm
      cases hm with
      | step hB htail =>
          cases htail with
          | step hB2 htt => cases htt
  case impS2 =>
      intro A B C' m₁ m₂ K _ _ hle hg ih1 ih2 hm
      cases hm with
      | step hB hC' =>
          exact ih1 (ModChain.step hB (ModChain.step hg.2 hC'))
  case boxMono =>
      intro a b K A hab hle hm
      cases hm with
      | step hB htail => cases htail
  case atomNeg =>
      intro k p q b aN mm _ hne hle ih hm
      exact nomatch hm

/-- **THE FALSIFICATION THEOREM**: the DupocBot self-cooperation fact is provable,
    and lies outside the modest stratum at EVERY literal bound and budget. -/
theorem cutRelevance_modestGate_false :
    (∃ m, Provable m tgtD) ∧
    ∀ (N m : Nat), ¬ T42.ProvableG (T44.modestGate N) m tgtD :=
  ⟨⟨4096 * W, ProvT.sound treeD⟩, fun _ _ h => regress h ModChain.base⟩
