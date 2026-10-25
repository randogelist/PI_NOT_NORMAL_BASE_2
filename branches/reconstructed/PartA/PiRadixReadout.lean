import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace ANCHOPI.PartA

open scoped Interval

/-- The analytic π-anchor used by the radix state. -/
theorem pi_integral_anchor :
    (∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x ^ 2)) = Real.pi / 4 := by
  simpa using
    (intervalIntegral.integral_one_div_one_add_sq (a := (0 : ℝ)) (b := 1))

/-- One-based binary digit readout by the floor parity convention. -/
noncomputable def binaryDigit (x : ℝ) (n : ℕ) : ℤ :=
  Int.floor ((2 : ℝ) ^ n * x) % 2

theorem binaryDigit_is_bit (x : ℝ) (n : ℕ) :
    binaryDigit x n = 0 ∨ binaryDigit x n = 1 := by
  unfold binaryDigit
  exact Int.emod_two_eq _

/-- Integer feedback accumulated by the base-256 recurrence. -/
def feedbackInteger (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => 256 * feedbackInteger f n + f n

/-- Semantic analytic radix state.  No computability claim is made here. -/
noncomputable def radixState (f : ℕ → ℤ) : ℕ → ℝ
  | 0 => Real.pi / 4
  | n + 1 => 256 * radixState f n + (f n : ℝ)

/-- Multiplying the radix state by four isolates π plus an integer multiple of four. -/
theorem radix_scaled_identity (f : ℕ → ℤ) (m : ℕ) :
    4 * radixState f m =
      (256 : ℝ) ^ m * Real.pi + ((4 * feedbackInteger f m : ℤ) : ℝ) := by
  induction m with
  | zero =>
      simp [radixState, feedbackInteger]
      ring
  | succ m ih =>
      simp only [radixState, feedbackInteger, pow_succ]
      calc
        4 * (256 * radixState f m + (f m : ℝ))
            = 256 * (4 * radixState f m) + 4 * (f m : ℝ) := by ring
        _ = 256 * ((256 : ℝ) ^ m * Real.pi +
              ((4 * feedbackInteger f m : ℤ) : ℝ)) + 4 * (f m : ℝ) := by rw [ih]
        _ = (256 : ℝ) ^ m * 256 * Real.pi +
              ((4 * (256 * feedbackInteger f m + f m) : ℤ) : ℝ) := by
              push_cast
              ring

/-- 256^m is exactly the binary scale 2^(8m). -/
theorem radix256_eq_two_pow_eight (m : ℕ) :
    (256 : ℝ) ^ m = (2 : ℝ) ^ (8 * m) := by
  calc
    (256 : ℝ) ^ m = ((2 : ℝ) ^ 8) ^ m := by norm_num
    _ = (2 : ℝ) ^ (8 * m) := by rw [← pow_mul]

/-- Exact floor translation for the radix state. -/
theorem radix_floor_exact (f : ℕ → ℤ) (m : ℕ) :
    Int.floor (4 * radixState f m) =
      Int.floor ((256 : ℝ) ^ m * Real.pi) + 4 * feedbackInteger f m := by
  rw [radix_scaled_identity]
  simpa using
    (Int.floor_add_intCast ((256 : ℝ) ^ m * Real.pi)
      (4 * feedbackInteger f m))

/-- The floor parity of every integer-feedback radix state is an actual binary digit of π. -/
theorem radix_pi_readout (f : ℕ → ℤ) (m : ℕ) :
    Int.floor (4 * radixState f m) % 2 = binaryDigit Real.pi (8 * m) := by
  rw [radix_floor_exact, radix256_eq_two_pow_eight]
  unfold binaryDigit
  have hfour : (4 * feedbackInteger f m : ℤ) =
      (2 * feedbackInteger f m) * 2 := by ring
  rw [hfour]
  simpa using
    (Int.add_mul_emod_self_right
      (Int.floor ((2 : ℝ) ^ (8 * m) * Real.pi))
      (2 * feedbackInteger f m) 2)

/-- Legacy G1 shell addresses: bit position 2^(10+a). -/
def bitPosition (a : ℕ) : ℕ := 2 ^ (10 + a)

/-- One base-256 carry corresponds to eight binary positions. -/
def carryIndex (a : ℕ) : ℕ := 2 ^ (7 + a)

/-- The actual π bit read by G1 at shell a. -/
noncomputable def g1Bit (a : ℕ) : ℤ := binaryDigit Real.pi (bitPosition a)

theorem bitPosition_eq_eight_mul_carryIndex (a : ℕ) :
    bitPosition a = 8 * carryIndex a := by
  unfold bitPosition carryIndex
  rw [show 10 + a = 3 + (7 + a) by omega, pow_add]
  norm_num

/-- The semantic radix state reveals the actual π bit at the G1 address. -/
theorem g1_from_radix (f : ℕ → ℤ) (a : ℕ) :
    Int.floor (4 * radixState f (carryIndex a)) % 2 = g1Bit a := by
  rw [radix_pi_readout]
  unfold g1Bit
  rw [bitPosition_eq_eight_mul_carryIndex]

/-- Any independently defined analytic state with the same π/4 seed and
    integer base-256 recurrence equals the canonical radix state. -/
theorem external_radix_unique (f : ℕ → ℤ) (J : ℕ → ℝ)
    (h0 : J 0 = Real.pi / 4)
    (hstep : ∀ m, J (m + 1) = 256 * J m + (f m : ℝ)) :
    ∀ m, J m = radixState f m := by
  intro m
  induction m with
  | zero => simpa [radixState] using h0
  | succ m ih =>
      rw [hstep, radixState, ih]

/-- External analytic recurrence → actual π G1 readout. -/
theorem g1_from_external_radix (f : ℕ → ℤ) (J : ℕ → ℝ)
    (h0 : J 0 = Real.pi / 4)
    (hstep : ∀ m, J (m + 1) = 256 * J m + (f m : ℝ))
    (a : ℕ) :
    Int.floor (4 * J (carryIndex a)) % 2 = g1Bit a := by
  rw [external_radix_unique f J h0 hstep]
  exact g1_from_radix f a

/-- The same theorem with π/4 supplied analytically as an integral. -/
theorem g1_from_integral_seed (f : ℕ → ℤ) (J : ℕ → ℝ)
    (h0 : J 0 = ∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x ^ 2))
    (hstep : ∀ m, J (m + 1) = 256 * J m + (f m : ℝ))
    (a : ℕ) :
    Int.floor (4 * J (carryIndex a)) % 2 = g1Bit a := by
  apply g1_from_external_radix f J
  · calc
      J 0 = (∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x ^ 2)) := h0
      _ = Real.pi / 4 := pi_integral_anchor
  · exact hstep

end ANCHOPI.PartA
