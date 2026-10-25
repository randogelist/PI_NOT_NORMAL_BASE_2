import PartA.CtLimit

/-!
Source port of NormalityClosure/src/Critical00.v through Critical03_Rate.v.
This file derives the coefficient from the actual logarithmic kernel.
It makes no identification between that kernel and a statistic of pi's digits.
Prepared by source inspection; no Lean compiler was run for this extension.
-/

namespace ANCHOPI.PartA

noncomputable def pairMean (N : ℝ) : ℝ :=
  Real.log (1 + 1 / N) / Real.log (1 + 2 / N)

noncomputable def criticalDefect (N : ℝ) : ℝ :=
  Real.log (1 + 1 / (N * (N + 2))) / (2 * Real.log (1 + 2 / N))

noncomputable def scaledDefect (N : ℝ) : ℝ :=
  N * criticalDefect N

/-- Keep denominator cancellation separate from the logarithm arguments. -/
private theorem scalar_div_sub_half (a b : ℝ) (hb : b ≠ 0) :
    a / b - 1 / 2 = (2 * a - b) / (2 * b) := by
  field_simp [hb] <;> ring

private theorem log_one_add_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x := by
  have hp : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hp
  linarith

private theorem log_one_add_lower (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hp : 0 < 1 + x := by linarith
  have hn : 1 + x ≠ 0 := ne_of_gt hp
  have hid : x / (1 + x) = 1 - (1 + x)⁻¹ := by
    field_simp [hn] <;> ring
  rw [hid]
  exact Real.one_sub_inv_le_log_of_pos hp

theorem criticalDefect_pos (N : ℝ) (hN : 0 < N) :
    0 < criticalDefect N := by
  have hy : 0 < 1 / (N * (N + 2)) := by positivity
  have hz : 0 < 2 / N := by positivity
  have hnum : 0 < Real.log (1 + 1 / (N * (N + 2))) :=
    Real.log_pos (by linarith)
  have hlog : 0 < Real.log (1 + 2 / N) :=
    Real.log_pos (by linarith)
  unfold criticalDefect
  exact div_pos hnum (by linarith)

theorem scaledDefect_pos (N : ℝ) (hN : 0 < N) :
    0 < scaledDefect N := by
  exact mul_pos hN (criticalDefect_pos N hN)

theorem pairMean_sub_half (N : ℝ) (hN : 0 < N) :
    pairMean N - 1 / 2 = criticalDefect N := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hN2 : N + 2 ≠ 0 := by linarith
  have hp : 0 < 1 + 1 / N := by positivity
  have hq : 0 < 1 + 2 / N := by positivity
  have hz : 0 < 2 / N := by positivity
  have hlog : 0 < Real.log (1 + 2 / N) :=
    Real.log_pos (by linarith)
  have hlog0 : Real.log (1 + 2 / N) ≠ 0 := ne_of_gt hlog
  have hratio :
      ((1 + 1 / N) * (1 + 1 / N)) / (1 + 2 / N) =
        1 + 1 / (N * (N + 2)) := by
    field_simp [hN0, hN2, ne_of_gt hq] <;> ring
  have hidentity :
      2 * Real.log (1 + 1 / N) - Real.log (1 + 2 / N) =
        Real.log (1 + 1 / (N * (N + 2))) := by
    calc
      2 * Real.log (1 + 1 / N) - Real.log (1 + 2 / N) =
          Real.log (((1 + 1 / N) * (1 + 1 / N)) / (1 + 2 / N)) := by
            rw [Real.log_div (mul_ne_zero (ne_of_gt hp) (ne_of_gt hp))
              (ne_of_gt hq), Real.log_mul (ne_of_gt hp) (ne_of_gt hp)]
            ring
      _ = Real.log (1 + 1 / (N * (N + 2))) := congrArg Real.log hratio
  have halgebra :
      pairMean N - 1 / 2 =
        (2 * Real.log (1 + 1 / N) - Real.log (1 + 2 / N)) /
          (2 * Real.log (1 + 2 / N)) := by
    unfold pairMean
    exact scalar_div_sub_half
      (Real.log (1 + 1 / N)) (Real.log (1 + 2 / N)) hlog0
  rw [halgebra, hidentity] <;> rfl

theorem pairMean_gt_half (N : ℝ) (hN : 0 < N) :
    1 / 2 < pairMean N := by
  have hd := criticalDefect_pos N hN
  have he := pairMean_sub_half N hN
  linarith

theorem criticalDefect_sandwich (N : ℝ) (hN : 0 < N) :
    N / (4 * (N + 1) ^ 2) ≤ criticalDefect N ∧
      criticalDefect N ≤ 1 / (4 * N) := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hN1 : N + 1 ≠ 0 := by linarith
  have hN2 : N + 2 ≠ 0 := by linarith
  have hy : 0 < 1 / (N * (N + 2)) := by positivity
  have hz : 0 < 2 / N := by positivity
  have hy1 : 1 + 1 / (N * (N + 2)) ≠ 0 := by positivity
  have hz1 : 1 + 2 / N ≠ 0 := by positivity
  have hnumlo := log_one_add_lower (1 / (N * (N + 2))) (le_of_lt hy)
  have hnumhi := log_one_add_upper (1 / (N * (N + 2))) (le_of_lt hy)
  have hdenlo := log_one_add_lower (2 / N) (le_of_lt hz)
  have hdenhi := log_one_add_upper (2 / N) (le_of_lt hz)
  have hlog : 0 < Real.log (1 + 2 / N) := Real.log_pos (by linarith)
  have hden : 0 < 2 * Real.log (1 + 2 / N) := by linarith
  have hlower : 0 ≤ N / (4 * (N + 1) ^ 2) := by positivity
  have hupper : 0 ≤ (1 : ℝ) / (4 * N) := by positivity
  have hidlo :
      (N / (4 * (N + 1) ^ 2)) * (2 * (2 / N)) =
        (1 / (N * (N + 2))) / (1 + 1 / (N * (N + 2))) := by
    field_simp [hN0, hN1, hN2, hy1] <;> ring
  have hidhi :
      1 / (N * (N + 2)) =
        (1 / (4 * N)) * (2 * ((2 / N) / (1 + 2 / N))) := by
    field_simp [hN0, hN2, hz1] <;> ring
  constructor
  · unfold criticalDefect
    apply (le_div_iff₀ hden).2
    calc
      (N / (4 * (N + 1) ^ 2)) * (2 * Real.log (1 + 2 / N)) ≤
          (N / (4 * (N + 1) ^ 2)) * (2 * (2 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) hlower
      _ = (1 / (N * (N + 2))) / (1 + 1 / (N * (N + 2))) := hidlo
      _ ≤ Real.log (1 + 1 / (N * (N + 2))) := hnumlo
  · unfold criticalDefect
    apply (div_le_iff₀ hden).2
    calc
      Real.log (1 + 1 / (N * (N + 2))) ≤ 1 / (N * (N + 2)) := hnumhi
      _ = (1 / (4 * N)) * (2 * ((2 / N) / (1 + 2 / N))) := hidhi
      _ ≤ (1 / (4 * N)) * (2 * Real.log (1 + 2 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) hupper

theorem scaledDefect_sandwich (N : ℝ) (hN : 0 < N) :
    N ^ 2 / (4 * (N + 1) ^ 2) ≤ scaledDefect N ∧
      scaledDefect N ≤ 1 / 4 := by
  rcases criticalDefect_sandwich N hN with ⟨hlo, hhi⟩
  have hlo' := mul_le_mul_of_nonneg_left hlo (le_of_lt hN)
  have hhi' := mul_le_mul_of_nonneg_left hhi (le_of_lt hN)
  have hidlo : N * (N / (4 * (N + 1) ^ 2)) =
      N ^ 2 / (4 * (N + 1) ^ 2) := by ring
  have hidhi : N * (1 / (4 * N)) = (1 : ℝ) / 4 := by
    field_simp [ne_of_gt hN] <;> ring
  rw [hidlo] at hlo'
  rw [hidhi] at hhi'
  exact ⟨hlo', hhi'⟩

/-- Explicit rational upper envelope for the coefficient error. -/
theorem scaledDefect_error_rational (N : ℝ) (hN : 0 < N) :
    0 ≤ (1 : ℝ) / 4 - scaledDefect N ∧
      (1 : ℝ) / 4 - scaledDefect N ≤
        (2 * N + 1) / (4 * (N + 1) ^ 2) := by
  rcases scaledDefect_sandwich N hN with ⟨hlo, hhi⟩
  have hN1 : N + 1 ≠ 0 := by linarith
  have hid :
      (1 : ℝ) / 4 - N ^ 2 / (4 * (N + 1) ^ 2) =
        (2 * N + 1) / (4 * (N + 1) ^ 2) := by
    field_simp [hN1] <;> ring
  constructor
  · linarith
  · rw [← hid]
    linarith

/-- The quantitative bound used by the uniform physical-coordinate limit. -/
theorem scaledDefect_error (N : ℝ) (hN : 0 < N) :
    0 ≤ (1 : ℝ) / 4 - scaledDefect N ∧
      (1 : ℝ) / 4 - scaledDefect N ≤ 1 / (N + 1) := by
  rcases scaledDefect_error_rational N hN with ⟨hlo, hhi⟩
  have hN1 : N + 1 ≠ 0 := by linarith
  have hden : 0 < 4 * (N + 1) ^ 2 := by positivity
  have hid : (1 / (N + 1)) * (4 * (N + 1) ^ 2) =
      4 * (N + 1) := by
    field_simp [hN1] <;> ring
  have hbound : (2 * N + 1) / (4 * (N + 1) ^ 2) ≤ 1 / (N + 1) := by
    apply (div_le_iff₀ hden).2
    rw [hid]
    linarith
  exact ⟨hlo, hhi.trans hbound⟩

theorem pairMean_scaled_error (N : ℝ) (hN : 0 < N) :
    0 ≤ (1 : ℝ) / 4 - N * (pairMean N - 1 / 2) ∧
      (1 : ℝ) / 4 - N * (pairMean N - 1 / 2) ≤ 1 / (N + 1) := by
  rw [pairMean_sub_half N hN]
  exact scaledDefect_error N hN

end ANCHOPI.PartA
