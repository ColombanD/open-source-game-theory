import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.DefectBot

/-!
# Unblocking demo for the proposed `searchElseChain` constructor

Compiled against the UNCHANGED engine, with the proposed rule taken as a HYPOTHESIS
(`hRule`, in the exact shape the constructor would have, cost side-condition
included): the Löb premise

    `□_{kSelf} (OptimBot kOpp kSelf plays D vs DefectBot)`
    `  → (OptimBot kOpp kSelf plays D vs DefectBot)`

becomes derivable at budget `P = 2·kOpp + O(log kOpp + log kSelf)` — two `search_f`
floors (the two refuted "DefectBot cooperates" rungs) plus replay overhead. This is
the exact premise shape `bloeb_engine` consumes; at staggered budgets
`kSelf ≥ 8192·(P + …)` the engine then delivers `Pf kSelf φD`, OptimBot's rung-3
self-search fires, and `llm_outcome_OptimBot_vs_DefectBot = (D, D)` follows — the
outcome `outcome_status.toml` records as the expected flip. No route to this premise
exists in the current 27-constructor `Pf` (see proposal.md, "why underivable").
-/

open PD PD.BaseTheorems PD.Bots

namespace SearchElseChainProposal

inductive SearchLayer2 where
  | thenL (g : Nat) (ψ : Formula) (e : Prog)
  | elseL (g : Nat) (ψ : Formula) (p : Prog)

def plug2 : List SearchLayer2 → Prog → Prog
  | [], x => x
  | .thenL g ψ e :: L, x => .search g ψ (plug2 L x) e
  | .elseL g ψ p :: L, x => .search g ψ p (plug2 L x)

def guard2 (me opponent : Prog) : SearchLayer2 → Formula
  | .thenL g ψ _ => .box g (ψ.subst me opponent)
  | .elseL _ ψ _ => .neg (ψ.subst me opponent)

def guards2 (me opponent : Prog) : List SearchLayer2 → List Formula
  | [] => []
  | hd :: L => guard2 me opponent hd :: guards2 me opponent L

/-- Per-layer transcript floor: an else-layer pays its full failed budget (the
    `search_f` discipline — forced by provable-soundness exactly as for `search_f`);
    a then-layer pays the `c_guard` cite of its guard proof. -/
def layerCost : SearchLayer2 → Nat
  | .thenL g _ _ => c_guard g
  | .elseL g _ _ => g + c_node

def layersCost : List SearchLayer2 → Nat
  | [] => 0
  | hd :: L => layerCost hd + layersCost L

/-- The proposed constructor, as a hypothesis (premise-free reading leaf; the cost
    side-condition charges every else-floor plus the conclusion's own size). -/
def RuleHyp : Prop :=
  ∀ (hd : SearchLayer2) (L : List SearchLayer2) (a : Action) (me opponent : Prog)
    (k : Nat),
    me = plug2 (hd :: L) (.const a) →
    layersCost (hd :: L) +
      (Formula.impl (guard2 me opponent hd)
        (implChain (guards2 me opponent L) (.plays me opponent a))).size ≤ k →
    Pf k (.impl (guard2 me opponent hd)
      (implChain (guards2 me opponent L) (.plays me opponent a)))

/-- The four-layer decomposition of OptimBot's else-else-then-then path to its
    rung-3 defection: cross the two refuted "DefectBot plays C" rungs, fire the
    "DefectBot plays D" rung, keep the rung-3 self-search as the boxed antecedent. -/
def optimLayers (kOpp kSelf : Nat) : List SearchLayer2 :=
  [ .elseL kOpp (.plays .opp .self Action.C)
      (.search kSelf (.plays .self .opp Action.D) (.const Action.D)
        (.search kOpp (.plays .opp .self Action.C)
          (.search kSelf (.plays .self .opp Action.C) (.const Action.C)
            (.search kOpp (.plays .opp .self Action.D)
              (.search kSelf (.plays .self .opp Action.D) (.const Action.D)
                (.const Action.C))
              (.const Action.C)))
          (.search kOpp (.plays .opp .self Action.D)
            (.search kSelf (.plays .self .opp Action.D) (.const Action.D)
              (.const Action.C))
            (.const Action.C)))),
    .elseL kOpp (.plays .opp .self Action.C)
      (.search kSelf (.plays .self .opp Action.C) (.const Action.C)
        (.search kOpp (.plays .opp .self Action.D)
          (.search kSelf (.plays .self .opp Action.D) (.const Action.D)
            (.const Action.C))
          (.const Action.C))),
    .thenL kOpp (.plays .opp .self Action.D) (.const Action.C),
    .thenL kSelf (.plays .self .opp Action.D) (.const Action.C) ]

/-- The telescope really is OptimBot. -/
theorem optim_is_plug2 (kOpp kSelf : Nat) :
    OptimBot kOpp kSelf = plug2 (optimLayers kOpp kSelf) (.const Action.D) := rfl

/-- **The demo**: under `RuleHyp`, the `bloeb_engine` premise for OptimBot's
    defection against DefectBot is provable at `2·kOpp` plus logarithmic overhead —
    the honest price of the two refuted cooperation rungs. -/
theorem optim_defectbot_loeb_premise (hRule : RuleHyp) (kOpp kSelf : Nat)
    (h1 : 1 ≤ kOpp) :
    Pf (2 * kOpp + 1000 * (Nat.log2 kOpp + Nat.log2 kSelf) + 100000)
       (.impl (.box kSelf (.plays (OptimBot kOpp kSelf) DefectBot Action.D))
              (.plays (OptimBot kOpp kSelf) DefectBot Action.D)) := by
  set O := OptimBot kOpp kSelf with hO
  have hlogO : Nat.log2 kOpp ≤ kOpp := log2_le_self _
  have hlogS : Nat.log2 kSelf ≤ kSelf := log2_le_self _
  -- The Σ₁ refutation of "DefectBot cooperates with O" (its actual play is D).
  have hneg : Pf (20 * (Nat.log2 kOpp + Nat.log2 kSelf) + 2000)
      (.neg (.plays DefectBot O Action.C)) := by
    refine Pf.atomNeg DefectBot O .D .C c_leaf
      ⟨(PlaysProof.const :
          PlaysProof DefectBot O (.const Action.D) Action.D c_leaf), le_rfl⟩
      (by decide) ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, c_leaf, hO]
    omega
  -- The cheap boxed fact for the fired rung: "DefectBot defects against O".
  have hboxD : Pf (300 * (Nat.log2 kOpp + Nat.log2 kSelf) + 50000)
      (.box kOpp (.plays DefectBot O Action.D)) := by
    have hlog1 : Nat.log2 1 = 0 := by decide
    have hb1 : Pf (100 * (Nat.log2 kOpp + Nat.log2 kSelf) + 20000)
        (.box 1 (.plays DefectBot O Action.D)) := by
      refine Pf.boxIntro 1 _ _
        (Pf.atom ⟨(PlaysProof.const :
            PlaysProof DefectBot O (.const Action.D) Action.D c_leaf),
          by decide⟩) ?_
      simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO, hlog1]
      omega
    have hmono : Pf (100 * (Nat.log2 kOpp + Nat.log2 kSelf) + 20000)
        (.impl (.box 1 (.plays DefectBot O Action.D))
               (.box kOpp (.plays DefectBot O Action.D))) := by
      refine Pf.boxMono 1 kOpp _ _ h1 ?_
      simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO, hlog1]
      omega
    refine Pf.mp _ _ _ _ hmono hb1 ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega
  -- The rule instance over the four-layer telescope.
  have hchain := hRule (.elseL kOpp (.plays .opp .self Action.C) _)
    (List.tail (optimLayers kOpp kSelf)) Action.D O DefectBot
    (2 * kOpp + 100 * (Nat.log2 kOpp + Nat.log2 kSelf) + 4000)
    (optim_is_plug2 kOpp kSelf)
    (by
      simp only [optimLayers, layersCost, layerCost, guards2, guard2, implChain,
        List.foldr, List.tail, Formula.size, Prog.size, Formula.subst, Prog.subst,
        numCost, c_guard, c_node, OptimBot, DefectBot, hO]
      omega)
  rw [show List.tail (optimLayers kOpp kSelf) = (optimLayers kOpp kSelf).tail from rfl]
    at hchain
  simp only [optimLayers, List.tail, guards2, guard2, implChain, List.foldr,
    Formula.subst, Prog.subst] at hchain
  -- Discharge the two refutation antecedents and the fired rung's box.
  have h2 := Pf.mp _ _ _ _ hchain hneg (k :=
      2 * kOpp + 200 * (Nat.log2 kOpp + Nat.log2 kSelf) + 10000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega)
  have h3 := Pf.mp _ _ _ _ h2 hneg (k :=
      2 * kOpp + 300 * (Nat.log2 kOpp + Nat.log2 kSelf) + 16000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega)
  have h4 := Pf.mp _ _ _ _ h3 hboxD (k :=
      2 * kOpp + 1000 * (Nat.log2 kOpp + Nat.log2 kSelf) + 100000) (by
    simp only [Formula.size, Prog.size, numCost, OptimBot, DefectBot, hO]
    omega)
  exact h4

end SearchElseChainProposal
