import PrisonersDilemma.Tau.Roster

/-!
# τ(EBot), the exploiter

Base EBot is three `.sim` watches: cooperates with the defector? then exploit (D);
else cooperates with the cooperator? then C; else cooperates with the mirror? then
C; else D. The lift keeps all three as `ite (sim …)` nodes — the third needs
`.mirror` in the roster.
-/

namespace PD.Tau

/-- τ(EBot): exploitable? D; reciprocates with the cooperator or the mirror? C; else D. -/
def tauEBotSpec : Spec Tmpl :=
  .ite (.sim (.name .defect)) .C (.const .D)
    (.ite (.sim (.name .coop)) .C (.const .C)
      (.ite (.sim (.name .mirror)) .C (.const .C) (.const .D)))

end PD.Tau
