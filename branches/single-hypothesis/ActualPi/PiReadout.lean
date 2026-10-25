import AWPIWordAnchor.CW02_FiniteExperiment

namespace ANCHOPI.ActualPi

open AWPIWordAnchor

/-- Exact classical binary readout. Digit 0 is the first digit after the radix point. -/
noncomputable def binaryDigit (x : ℝ) (n : ℕ) : Bool :=
  decide ((Int.floor (((2 : ℝ) ^ (n + 1)) * x)) % 2 = 1)

/-- Canonical floor-defined binary digit stream of π. -/
noncomputable def actualPiDigits : bitstream :=
  fun n => binaryDigit Real.pi n

@[simp] theorem actualPiDigits_apply (n : ℕ) :
    actualPiDigits n = binaryDigit Real.pi n := rfl

/-- Exact floor/parity statement exposed by the definition. -/
theorem actualPiDigits_spec (n : ℕ) :
    actualPiDigits n =
      decide ((Int.floor (((2 : ℝ) ^ (n + 1)) * Real.pi)) % 2 = 1) := rfl

end ANCHOPI.ActualPi
