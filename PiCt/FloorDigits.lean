import PiCt.ParityDrift

/-!
Exact floor formulas for actual binary digits.  The formulas apply to every
real anchor, and hence to the proved anchor of the pi representative.  This
module does not assert any bound on sums of these floor expressions.
-/

namespace PiCt.FloorDigits

open BinaryWords ParityDrift

noncomputable section

/-- The integer prefix at precision `n`; the integer part is retained. -/
def prefixFloor (x : ℝ) (n : ℕ) : ℤ := Int.floor ((2 : ℝ) ^ n * x)

/-- Doubling a real number extracts exactly the next canonical binary bit. -/
theorem floor_double (y : ℝ) :
    Int.floor (2 * y) = 2 * Int.floor y +
      if (1 / 2 : ℝ) ≤ Int.fract y then 1 else 0 := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  by_cases h : (1 / 2 : ℝ) ≤ Int.fract y
  · rw [if_pos h]
    apply Int.floor_eq_iff.mpr
    push_cast
    unfold Int.fract at h h0 h1
    constructor <;> linarith
  · rw [if_neg h]
    apply Int.floor_eq_iff.mpr
    push_cast
    unfold Int.fract at h h0 h1
    constructor <;> linarith

/-- The actual bit is the difference of consecutive integer prefixes. -/
theorem digit_eq_floor_difference (x : ℝ) (n : ℕ) :
    digit (bit x) n =
      (prefixFloor x (n + 1) : ℝ) - 2 * (prefixFloor x n : ℝ) := by
  have hp : (2 : ℝ) ^ (n + 1) * x = 2 * ((2 : ℝ) ^ n * x) := by
    rw [pow_succ]
    ring
  unfold prefixFloor
  rw [hp, floor_double]
  unfold digit bit
  simp

/-- A pair difference depends on three adjacent integer prefixes. -/
theorem pairDifference_eq_floors (x : ℝ) (j : ℕ) :
    pairDifference (bit x) j =
      3 * (prefixFloor x (2 * j + 1) : ℝ) -
      2 * (prefixFloor x (2 * j) : ℝ) -
      (prefixFloor x (2 * j + 2) : ℝ) := by
  unfold pairDifference
  rw [digit_eq_floor_difference, digit_eq_floor_difference]
  ring

/-- The signed pair count, written entirely in integer floor prefixes. -/
def floorParity (x : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m,
    (3 * (prefixFloor x (2 * j + 1) : ℝ) -
      2 * (prefixFloor x (2 * j) : ℝ) -
      (prefixFloor x (2 * j + 2) : ℝ))

theorem paritySum_eq_floorParity (x : ℝ) (m : ℕ) :
    paritySum (bit x) m = floorParity x m := by
  unfold paritySum floorParity
  apply Finset.sum_congr rfl
  intro j _hj
  exact pairDifference_eq_floors x j

/-- The expression is obtained directly from the analytic representative's
anchored value, with no digit-statistics hypothesis. -/
theorem PI_PARITY_FROM_ANALYTIC_ANCHOR (m : ℕ) :
    paritySum piBits m = floorParity ((Pi.toFun 1).re) m := by
  exact paritySum_eq_floorParity ((Pi.toFun 1).re) m

/-- Identification with the actual constant `Real.pi`. -/
theorem PI_PARITY_FLOOR_IDENTITY (m : ℕ) :
    paritySum piBits m = floorParity Real.pi m := by
  rw [PI_PARITY_FROM_ANALYTIC_ANCHOR, PI_ANCHOR]
  simp

/-- A rational or real enclosure certifies a floor when it fits inside one
integer cell.  This is a finite certificate, not a uniform orbit estimate. -/
theorem floor_of_enclosure {x lo hi : ℝ} {k : ℤ}
    (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hcellLo : (k : ℝ) ≤ lo) (hcellHi : hi < (k : ℝ) + 1) :
    Int.floor x = k :=
  Int.floor_eq_iff.mpr ⟨hcellLo.trans hlo, hhi.trans_lt hcellHi⟩

end

end PiCt.FloorDigits
