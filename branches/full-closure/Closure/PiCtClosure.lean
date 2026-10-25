import PartA.CtLimit

namespace ANCHOPI.Closure

open AWPIWordAnchor
open ANCHOPI.PartA
open ANCHOPI.PartB

/--
The exact actual-digit binding needed to plug the analytic coefficient into
Part B.  This deliberately contains no research axiom and no inhabitant.
An upstream `PiRadixReadout`/semantic module must construct it for the
canonical binary digit stream of π.
-/
structure ActualPiCtBinding (piBits : bitstream) where
  H : ℕ → ℕ → ℝ
  finite : FiniteObservations piBits H
  uniform : UniformTailLimit 0 H limitingCt

/-- Main rebuilt closure: the actual π C_t binding immediately refutes normality. -/
theorem actual_pi_ct_binding_not_normal
    (piBits : bitstream) (h : ActualPiCtBinding piBits) :
    ¬ normal piBits := by
  exact uniform_strict_parity_not_normal
    piBits h.H limitingCt 0 0 h.finite h.uniform limitingCt_strictParity

/-- General source-compatible interface matching the historical Rocq sign anchor. -/
structure PiCtWitness (piBits : bitstream) where
  H : ℕ → ℕ → ℝ
  C : ℕ → ℝ
  phase : ℕ
  Q : ℕ
  finite : FiniteObservations piBits H
  uniform : UniformTailLimit Q H C
  parity : WeakParity phase Q C
  nonzero : ∃ t : ℕ, Q ≤ t ∧ C t ≠ 0

theorem pi_ct_witness_not_normal
    (piBits : bitstream) (h : PiCtWitness piBits) :
    ¬ normal piBits := by
  exact uniform_nonzero_parity_not_normal
    piBits h.H h.C h.phase h.Q h.finite h.uniform h.parity h.nonzero

/-- Frozen Part-A + Part-B closure theorem. -/
theorem PART_A_PLUS_PART_B_PI_NONNORMAL_CLOSURE
    (piBits : bitstream) :
    ActualPiCtBinding piBits → ¬ normal piBits :=
  actual_pi_ct_binding_not_normal piBits

end ANCHOPI.Closure
