import PartA.PiRadixReadout
import PartA.CtAnalytic

open ANCHOPI.PartA

#check pi_integral_anchor
#check g1_from_integral_seed
#check localLogRatio_sub_half_eq_ctMagnitude
#check ctMagnitude_pos
#check Ct_eq_oriented_log_defect
#check Ct_ne_zero
#check Ct_even_pos
#check Ct_odd_neg
#check PART_A_CT

#print axioms ANCHOPI.PartA.pi_integral_anchor
#print axioms ANCHOPI.PartA.g1_from_integral_seed
#print axioms ANCHOPI.PartA.Ct_ne_zero
#print axioms ANCHOPI.PartA.PART_A_CT

example : True := by
  have : True := trivial
  exact this
