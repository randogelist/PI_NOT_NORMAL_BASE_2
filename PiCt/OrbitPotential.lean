import PiCt.ParityClosure
import PiCt.FloorDigits

/-!
A precise potential-certificate interface for the base-four digit orbit.
Its inequalities must be established on the actual orbit in question.
A universal all-phase subaction is impossible, already at the fixed phase 1/3.
-/

namespace PiCt.OrbitPotential

open BinaryWords ParityDrift

noncomputable section

/-- The base-four shift on fractional parts. -/
def phaseMap (y : ℝ) : ℝ := Int.fract (4 * y)

/-- Values 0, -1, 1, 0 on the four quarter intervals of [0,1). -/
def observable (y : ℝ) : ℝ := 3 * (⌊2 * y⌋ : ℝ) - (⌊4 * y⌋ : ℝ)

/-- The actual fractional phase after j binary digit pairs. -/
def phase (x : ℝ) (j : ℕ) : ℝ := Int.fract ((2 : ℝ) ^ (2 * j) * x)

private theorem floor_mul_fract (k : ℤ) (u : ℝ) :
    ⌊(k : ℝ) * Int.fract u⌋ = ⌊(k : ℝ) * u⌋ - k * ⌊u⌋ := by
  have he : (k : ℝ) * Int.fract u = (k : ℝ) * u - ((k * ⌊u⌋ : ℤ) : ℝ) := by
    simp only [Int.fract, Int.cast_mul]
    ring
  rw [he, Int.floor_sub_intCast]

theorem phase_succ (x : ℝ) (j : ℕ) : phase x (j + 1) = phaseMap (phase x j) := by
  have hp : (2 : ℝ) ^ (2 * (j + 1)) * x = 4 * ((2 : ℝ) ^ (2 * j) * x) := by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    norm_num
    ring
  unfold phase phaseMap
  rw [hp]
  apply Int.fract_eq_fract.mpr
  refine ⟨4 * ⌊(2 : ℝ) ^ (2 * j) * x⌋, ?_⟩
  simp only [Int.fract, Int.cast_mul, Int.cast_ofNat]
  ring

/-- This observable is identified with the actual digits, without a bridge premise. -/
theorem pairDifference_eq_observable (x : ℝ) (j : ℕ) :
    pairDifference (bit x) j = observable (phase x j) := by
  rw [FloorDigits.pairDifference_eq_floors]
  unfold observable phase
  rw [show (2 : ℝ) = ((2 : ℤ) : ℝ) by norm_num,
    floor_mul_fract, show (4 : ℝ) = ((4 : ℤ) : ℝ) by norm_num, floor_mul_fract]
  push_cast
  unfold FloorDigits.prefixFloor
  have h1 : (2 : ℝ) ^ (2 * j + 1) * x = 2 * ((2 : ℝ) ^ (2 * j) * x) := by
    rw [pow_add]
    norm_num
    ring
  have h2 : (2 : ℝ) ^ (2 * j + 2) * x = 4 * ((2 : ℝ) ^ (2 * j) * x) := by
    rw [pow_add]
    norm_num
    ring
  rw [h1, h2]
  ring

@[simp] theorem phaseMap_one_third : phaseMap (1 / 3) = 1 / 3 := by
  norm_num [phaseMap, Int.fract]

@[simp] theorem observable_one_third : observable (1 / 3) = -1 := by
  norm_num [observable]

/-- The repeating base-four digit 1 prevents a global nonnegative-drift
potential inequality. No regularity or boundedness of F is needed. -/
theorem no_global_subaction :
    ¬ ∃ F : ℝ → ℝ, ∀ y : ℝ, 0 ≤ y → y < 1 →
      F (phaseMap y) - F y ≤ observable y := by
  rintro ⟨F, hF⟩
  have h := hF (1 / 3) (by norm_num) (by norm_num)
  rw [phaseMap_one_third, observable_one_third, sub_self] at h
  linarith

/-- A bounded potential sequence is a sufficient certificate if its
one-step increase is at most the actual digit-pair increment. -/
theorem not_normal_of_potential_sequence
    (b : ℕ → Bool) (V : ℕ → ℝ) (B : ℝ)
    (hstep : ∀ j, V (j + 1) - V j ≤ pairDifference b j)
    (hbound : ∀ j, |V j| ≤ B) : ¬ BinaryNormal b := by
  apply ParityClosure.not_normal_of_monotone_drift b
    (fun m => paritySum b m - V m) V B
  · apply monotone_nat_of_le_succ
    intro j
    have hs : paritySum b (j + 1) = paritySum b j + pairDifference b j := by
      simp only [paritySum, Finset.sum_range_succ]
    have hv := hstep j
    rw [hs]
    linarith
  · intro m
    ring
  · exact hbound

/-- Orbit form. The observable identification, subaction, and boundedness
are explicit inputs. This theorem does not construct them for pi. -/
theorem not_normal_of_orbit_potential
    (b : ℕ → Bool) (y : ℕ → ℝ) (F : ℝ → ℝ) (B : ℝ)
    (horbit : ∀ j, y (j + 1) = phaseMap (y j))
    (hobs : ∀ j, pairDifference b j = observable (y j))
    (hsubaction : ∀ j, F (phaseMap (y j)) - F (y j) ≤ observable (y j))
    (hbound : ∀ j, |F (y j)| ≤ B) : ¬ BinaryNormal b := by
  apply not_normal_of_potential_sequence b (fun j => F (y j)) B
  · intro j
    rw [horbit j, hobs j]
    exact hsubaction j
  · exact hbound

/-- An actual-anchor endpoint. Only the potential inequalities remain hypotheses. -/
theorem real_not_normal_of_orbit_potential
    (x : ℝ) (F : ℝ → ℝ) (B : ℝ)
    (hsubaction : ∀ j, F (phaseMap (phase x j)) - F (phase x j) ≤
      observable (phase x j))
    (hbound : ∀ j, |F (phase x j)| ≤ B) : ¬ BinaryNormal (bit x) :=
  not_normal_of_orbit_potential (bit x) (phase x) F B
    (phase_succ x) (pairDifference_eq_observable x) hsubaction hbound

end

end PiCt.OrbitPotential
