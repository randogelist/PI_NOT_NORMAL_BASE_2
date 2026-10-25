import PartA.CtMagnitude
import AWPI.VanishingCoefficientsAnchor
import PartB.ConcreteFrontier

open Filter Topology
open ANCHOPI.PartA
open AWPI.VanishingCoefficientsAnchor
open ANCHOPI.PartB.ConcreteFrontier

#check Cmag_pos
#check Cmag_ne_zero
#check concrete_pi_remainder_identity
#check AnalyticShellLimit
#check NormalityKillsActualShell
#check ActualPiNonCancellation
#check normal_pi_forces_exact_cancellation
#check pi_nonnormal_of_noncancellation
#check A_TIER_CANDIDATE_CLOSURE
#check historical_bounded_remainder_route

#print axioms ANCHOPI.PartA.Cmag_ne_zero
#print axioms ANCHOPI.PartB.ConcreteFrontier.concrete_pi_remainder_identity
#print axioms ANCHOPI.PartB.ConcreteFrontier.normal_pi_forces_exact_cancellation
#print axioms ANCHOPI.PartB.ConcreteFrontier.pi_nonnormal_of_noncancellation

example : True := by trivial
