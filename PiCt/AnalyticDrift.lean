import PiCt.ParityDrift
import PiCt.Instance

/-!
The exact analytic pair drift and its summable harmonic approximation.
These are analytic quantities. No bound for their residual against actual
digit parity sums is asserted in this module.
-/

namespace PiCt.AnalyticDrift

open ParityDrift

noncomputable section

/-- A summable pointwise error, with the physical location as denominator. -/
theorem delta_harmonic_error {M : ℝ} (hM : 0 < M) :
    0 ≤ 1 / (4 * M) - delta M ∧
      1 / (4 * M) - delta M ≤ (1 / 2) * (1 / M - 1 / (M + 1)) := by
  obtain ⟨hlo, hhi⟩ := delta_bounds hM
  constructor
  · linarith
  · have he : (1 / 2) * (1 / M - 1 / (M + 1)) -
          (1 / (4 * M) - M / (4 * (M + 1) ^ 2)) =
          1 / (4 * M * (M + 1) ^ 2) := by
      field_simp [ne_of_gt hM, ne_of_gt (show 0 < M + 1 by linarith)]
      ring
    have hp : 0 ≤ 1 / (4 * M * (M + 1) ^ 2) := by positivity
    linarith

def analyticStep (j : ℕ) : ℝ :=
  if j < 512 then 0 else delta (2 * (j : ℝ)) + delta (2 * (j : ℝ) + 1)

def harmonicStep (j : ℕ) : ℝ :=
  if j < 512 then 0 else 1 / (4 * (2 * (j : ℝ))) + 1 / (4 * (2 * (j : ℝ) + 1))

def analyticAccumulated (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, analyticStep j

def harmonicAccumulated (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, harmonicStep j

theorem analyticStep_nonneg (j : ℕ) : 0 ≤ analyticStep j := by
  unfold analyticStep
  split_ifs with hj
  · exact le_refl _
  · have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have h0 := (delta_bounds (M := 2 * (j : ℝ)) (by positivity)).1
    have h1 := (delta_bounds (M := 2 * (j : ℝ) + 1) (by positivity)).1
    have hp0 : 0 ≤ (2 * (j : ℝ)) / (4 * (2 * (j : ℝ) + 1) ^ 2) := by positivity
    have hp1 : 0 ≤ (2 * (j : ℝ) + 1) / (4 * (2 * (j : ℝ) + 1 + 1) ^ 2) := by positivity
    linarith

theorem analyticAccumulated_monotone : Monotone analyticAccumulated :=
  partialSums_monotone analyticStep analyticStep_nonneg

@[simp] theorem analyticAccumulated_zero : analyticAccumulated 0 = 0 := by
  simp [analyticAccumulated]

@[simp] theorem harmonicAccumulated_zero : harmonicAccumulated 0 = 0 := by
  simp [harmonicAccumulated]

theorem analyticAccumulated_succ (m : ℕ) :
    analyticAccumulated (m + 1) = analyticAccumulated m + analyticStep m := by
  simp only [analyticAccumulated, Finset.sum_range_succ]

theorem harmonicAccumulated_succ (m : ℕ) :
    harmonicAccumulated (m + 1) = harmonicAccumulated m + harmonicStep m := by
  simp only [harmonicAccumulated, Finset.sum_range_succ]

/-- Consecutive scalar errors telescope at the pair level. -/
theorem step_error (j : ℕ) (hj : 512 ≤ j) :
    0 ≤ harmonicStep j - analyticStep j ∧
      harmonicStep j - analyticStep j ≤
        1 / (4 * (j : ℝ)) - 1 / (4 * ((j + 1 : ℕ) : ℝ)) := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have h0 := delta_harmonic_error (M := 2 * (j : ℝ)) (by positivity)
  have h1 := delta_harmonic_error (M := 2 * (j : ℝ) + 1) (by positivity)
  have he : (1 / 2 : ℝ) * (1 / (2 * (j : ℝ)) - 1 / (2 * (j : ℝ) + 1)) +
      (1 / 2) * (1 / (2 * (j : ℝ) + 1) - 1 / (2 * (j : ℝ) + 1 + 1)) =
      1 / (4 * (j : ℝ)) - 1 / (4 * ((j + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hjp,
      ne_of_gt (show 0 < 2 * (j : ℝ) + 1 by positivity),
      ne_of_gt (show 0 < 2 * (j : ℝ) + 1 + 1 by positivity),
      ne_of_gt (show 0 < (j : ℝ) + 1 by positivity)]
    ring
  simp only [harmonicStep, analyticStep, if_neg (show ¬j < 512 by omega)]
  constructor <;> linarith

/-- A quantitative telescoping bound, including the initial zero segment. -/
theorem drift_error_tight (m : ℕ) :
    0 ≤ harmonicAccumulated m - analyticAccumulated m ∧
      harmonicAccumulated m - analyticAccumulated m ≤
        1 / 2048 - 1 / (4 * ((max m 512 : ℕ) : ℝ)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [harmonicAccumulated_succ, analyticAccumulated_succ]
      by_cases hm : m < 512
      · have hmax : max m 512 = 512 := max_eq_right (by omega)
        have hnext : max (m + 1) 512 = 512 := max_eq_right (by omega)
        simp only [harmonicStep, analyticStep, if_pos hm, add_zero]
        simpa only [hmax, hnext] using ih
      · have hml : 512 ≤ m := by omega
        have hmax : max m 512 = m := max_eq_left hml
        have hnext : max (m + 1) 512 = m + 1 := max_eq_left (by omega)
        have hs := step_error m hml
        rw [hmax] at ih
        rw [hnext]
        constructor <;> linarith

/-- The analytic and harmonic drifts stay within `1/2048` for every prefix. -/
theorem drift_error (m : ℕ) :
    0 ≤ harmonicAccumulated m - analyticAccumulated m ∧
      harmonicAccumulated m - analyticAccumulated m ≤ 1 / 2048 := by
  obtain ⟨hlo, hhi⟩ := drift_error_tight m
  have hp : 0 ≤ 1 / (4 * ((max m 512 : ℕ) : ℝ)) := by positivity
  constructor <;> linarith

end

end PiCt.AnalyticDrift
