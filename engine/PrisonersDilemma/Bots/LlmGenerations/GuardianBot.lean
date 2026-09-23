import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CooperateBot

open PD
namespace PD.Bots

/-- GuardianBot: cooperate by default, but defect against provable BULLIES —
    anyone I can prove defects against CooperateBot, the zoo's most defenseless
    member.

    Third-party NORM ENFORCEMENT, inverted relative to the existing probers:
    JustBot and PrudentBot use their third-party probe to REWARD good behavior
    (cooperate only if the opponent provably cooperates with / punishes the
    right partner); GuardianBot uses its probe to PUNISH bad behavior, from a
    default of trust. The probe target is frozen (`.bot CooperateBot`) exactly
    as in JustBot — `subst` must not mutate it.

    Why it is interesting:
    * Against another GuardianBot the guard is about a frozen third party, not
      about each other — there is NO Löbian fixpoint between the players.
      Mutual cooperation, if it holds, holds because the guard is refutable
      (Guardian provably does NOT bully CooperateBot), i.e. cooperation
      through norms rather than through mutual proof of cooperation.
    * It should punish DefectBot ((D,D): `DefectBot plays D vs CB` is a
      trivial positive atom) while cooperating with CooperateBot, MirrorBot,
      DupocBot — bots that don't bully the naive.
    * Its unconditional-looking else-play C is still a search else-branch, so
      the `search_f` floor applies: a same-budget DupocBot may FAIL to prove
      GuardianBot's cooperation and exploit it ((C,D)) — the moralist gets
      suckered not for its norms but for its proof-theoretic opacity. The
      staggered-budget rescue is the experiment. -/
def GuardianBot (k : Nat) : Prog :=
  .search k
    (.plays .opp (.bot CooperateBot) Action.D)
    (.const Action.D)
    (.const Action.C)

end PD.Bots
