import Foundation.FirstOrder.Incompleteness.RestrictedProvability

/-!
# ArithS.Basic — smoke test: Foundation's restricted provability is reachable.

Milestone M0 of `ARITHMETIZED_S_ROADMAP.md`. This file only checks that the pinned
Foundation builds and that the declarations M1 builds on resolve.
-/

open FFL.FirstOrder

#check @Theory.RestrictedProvable
#check @Arithmetic.lower_bound_gödelNumber_proof_restrictedGödel
