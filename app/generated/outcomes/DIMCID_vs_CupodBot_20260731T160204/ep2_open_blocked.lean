import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- guard sizes vs budget k. Both guards mention DIMCID k and CupodBot k source.
-- Each of DIMCID k, CupodBot k has size ~ log2 k + const. So guard size ~ log2 k + const << k.
-- So NO size floor for large k. Guards fit in budget. That's why (C,C) can't be a size-floor argument.
-- Confirms: the ONLY route to (C,C) is a negative census on the D-plays, which no kernel handles.

-- Let me reconsider the (D,D) route one final time via a DIFFERENT fixpoint:
-- Build the fixpoint on guard_dimcid directly. guard = P -> A.
-- diag route: use bloeb_engine on target = guard? For guard to be provable via Löb I need
--   Pf pm (□_fb guard -> guard). Do I have a leg □_something guard -> guard?
-- DIMCID leg gives □_k guard -> B, not -> guard. And Cupod: □_k B -> A -> (via L3) guard.
-- So: □_k B -> A -> guard. And I need to close □guard -> B to feed. That's L2's contrapositive dir.
-- L2: □_k guard -> B. So: □_k guard -> B -> ... need B -> □_k B to feed □_k B -> A -> guard.
--   B -> □_k B is atom Σ1-completeness (atomBoxImpl) but needs a CERTIFICATE of B. B = DIMCID plays D.
--   No certificate (that's the whole question). So can't get B -> □_k B unconditionally.
-- The mutual_loeb machinery packages exactly this and needs legPD □_kP A -> B which is walled.

-- Let me actually TRY mutual_pblt_engine_id to be 100% sure it fails, with the two legs.
-- Af = A? Let me set Af = B, Bf = A. Need hL1: □_k Bf -> ... hmm mutual needs
--   hL1: □_k (Af) -> (Bf), hL2: □_k (Bf) -> (Af). Then concludes Af provable.
-- I have L1: □_k B -> A  and L2: □_k guard -> B. These are NOT the mutual shape (guard != A).
-- To use mutual I need □_k A -> B. I only have □_k guard -> B and A->guard.
--   □_k A -> □_c guard (axK, c>k) -> can't feed □_k guard. WALL confirmed again.

example : True := trivial

end PD.Theorems

