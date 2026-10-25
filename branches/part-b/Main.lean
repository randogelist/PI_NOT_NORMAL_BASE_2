import PartA.PiRadixReadout
import PartA.CtAnalytic
import PartB.CtContradiction

open ANCHOPI.PartA
open ANCHOPI.PartB

#check ANCHOPI.PartA.Ct_ne_zero
#check ANCHOPI.PartA.Ct_even_pos
#check ANCHOPI.PartA.Ct_odd_neg
#check ANCHOPI.PartB.CtDriftBridge
#check ANCHOPI.PartB.criticalWord_eventually_absent
#check ANCHOPI.PartB.ctDriftBridge_not_everyWordRecurrent
#check ANCHOPI.PartB.analyticCtPairDrift_pos
#check ANCHOPI.PartB.CtDigitBridge
#check ANCHOPI.PartB.PART_B_CT_CONTRADICTION
#check ANCHOPI.PartB.PART_B_NORMALITY_CONTRADICTION

#print axioms ANCHOPI.PartB.criticalWord_eventually_absent
#print axioms ANCHOPI.PartB.ctDriftBridge_not_everyWordRecurrent
#print axioms ANCHOPI.PartB.PART_B_CT_CONTRADICTION
#print axioms ANCHOPI.PartB.PART_B_NORMALITY_CONTRADICTION

example : True := by trivial
