import PartA.CtLimit

namespace ANCHOPI.ActualPi

open AWPIWordAnchor

/--
Exact classical binary readout of the fractional digits of a real number.
Digit `n = 0` is the first binary digit after the radix point:
`floor (2^(n+1) x) mod 2`.

This is a mathematical readout, not an executable digit algorithm.
-/
noncomputable def binaryDigit (x : ℝ) (n : ℕ) : Bool :=
  decide ((Int.floor (((2 : ℝ) ^ (n + 1)) * x)) % 2 = 1)

/-- Canonical floor-defined binary digit stream of π. -/
noncomputable def actualPiDigits : bitstream :=
  fun n => binaryDigit Real.pi n

@[simp] theorem actualPiDigits_apply (n : ℕ) :
    actualPiDigits n = binaryDigit Real.pi n := rfl

/-- The exact floor/parity statement exposed by the readout definition. -/
theorem actualPiDigits_spec (n : ℕ) :
    actualPiDigits n =
      decide ((Int.floor (((2 : ℝ) ^ (n + 1)) * Real.pi)) % 2 = 1) := rfl

end ANCHOPI.ActualPi
