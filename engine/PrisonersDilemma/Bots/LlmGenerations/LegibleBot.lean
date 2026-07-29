import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- LegibleBot: cooperate iff my own cooperation is LEGIBLE — i.e. iff I can
    prove (within `kOut`) that "I cooperate with you" is provable within `kIn`.

    The guard is `□_kIn (I play C)`: the first bot in the zoo whose guard
    mentions provability itself (`.box`). Where DupocBot conditions on the
    OPPONENT's play, LegibleBot conditions on its own TRANSPARENCY: "I
    cooperate exactly when a `kIn`-budget reasoner can see that I cooperate."

    Why it is interesting:
    * It exercises the internalization layer in guard position — proving
      `□_kIn φ` at budget `kOut` is the object-level GL-4 step (`□φ → □□φ`),
      so outcome theorems for LegibleBot measure the cost overhead of one
      level of reflection, with `kOut vs kIn` as the two dials.
    * The cooperation fixpoint is DOUBLY self-referential: my play is C iff
      `Pf kOut (□_kIn C)`, and the inner sentence is about that very play.
      Bounded Löb must thread through two boxes instead of one.
    * Polarity is safe: the branch plays exactly the action whose provability
      the guard asserts, so no anti-diagonal inconsistency lurks.

    Expect `kOut` to need a margin above `kIn` (citing a `kIn`-proof costs at
    least `kIn` under transcript accounting) — quantifying that margin is the
    experiment. `LegibleBot k k` is likely below the floor, the staggered
    version the interesting one; same pattern as PrudentBot2/JustBot2. -/
def LegibleBot (kOut kIn : Nat) : Prog :=
  .search kOut
    (.box kIn (.plays .self .opp Action.C))
    (.const Action.C)
    (.const Action.D)

end PD.Bots
