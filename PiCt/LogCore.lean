import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Exact logarithmic split and its rational bounds.
These are analytic split coefficients, not digit-frequency coefficients.
-/

namespace PiCt

noncomputable def delta (M : ℝ) : ℝ :=
  Real.log (1 + 1 / (M * (M + 2))) / (2 * Real.log (1 + 2 / M))

noncomputable def split (M : ℝ) : ℝ :=
  Real.log (1 + 1 / M) / Real.log (1 + 2 / M)

theorem log_one_add_bounds {u : ℝ} (hu : 0 ≤ u) :
    u / (1 + u) ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  have hp : 0 < 1 + u := by linarith
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hp
    have he : 1 - (1 + u)⁻¹ = u / (1 + u) := by
      field_simp
      ring
    simpa only [he] using h
  · have h := Real.log_le_sub_one_of_pos hp
    linarith

theorem delta_bounds {M : ℝ} (hM : 0 < M) :
    M / (4 * (M + 1) ^ 2) ≤ delta M ∧ delta M ≤ 1 / (4 * M) := by
  have hm0 : M ≠ 0 := ne_of_gt hM
  have hm1 : M + 1 ≠ 0 := by positivity
  have hm2 : M + 2 ≠ 0 := by positivity
  have hnum := log_one_add_bounds (u := 1 / (M * (M + 2))) (by positivity)
  have hden := log_one_add_bounds (u := 2 / M) (by positivity)
  have hnlo : 1 / (M + 1) ^ 2 ≤ Real.log (1 + 1 / (M * (M + 2))) := by
    convert hnum.1 using 1
    field_simp
    ring
  have hdlo : 2 / (M + 2) ≤ Real.log (1 + 2 / M) := by
    convert hden.1 using 1
    field_simp
  have hlpos : 0 < Real.log (1 + 2 / M) := by
    apply Real.log_pos
    have : 0 < 2 / M := by positivity
    linarith
  have hdp : 0 < 2 * Real.log (1 + 2 / M) := by positivity
  constructor
  · unfold delta
    apply (le_div_iff₀ hdp).2
    calc
      M / (4 * (M + 1) ^ 2) * (2 * Real.log (1 + 2 / M))
          ≤ M / (4 * (M + 1) ^ 2) * (2 * (2 / M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hden.2 (by norm_num)) (by positivity)
      _ = 1 / (M + 1) ^ 2 := by field_simp; ring
      _ ≤ Real.log (1 + 1 / (M * (M + 2))) := hnlo
  · unfold delta
    apply (div_le_iff₀ hdp).2
    calc
      Real.log (1 + 1 / (M * (M + 2))) ≤ 1 / (M * (M + 2)) := hnum.2
      _ = (1 / (4 * M)) * (2 * (2 / (M + 2))) := by field_simp; ring
      _ ≤ (1 / (4 * M)) * (2 * Real.log (1 + 2 / M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdlo (by norm_num)) (by positivity)

theorem split_eq_half_add_delta {M : ℝ} (hM : 0 < M) :
    split M = 1 / 2 + delta M := by
  have hm0 : M ≠ 0 := ne_of_gt hM
  have hm2 : M + 2 ≠ 0 := by positivity
  have ha : 1 + 1 / M ≠ 0 := by positivity
  have hb : 1 + 2 / M ≠ 0 := by positivity
  have harg : (1 + 1 / M) ^ 2 / (1 + 2 / M) =
      1 + 1 / (M * (M + 2)) := by field_simp; ring
  have hlog : Real.log (1 + 1 / (M * (M + 2))) =
      2 * Real.log (1 + 1 / M) - Real.log (1 + 2 / M) := by
    rw [← harg, Real.log_div (pow_ne_zero 2 ha) hb, Real.log_pow]
    norm_num
  have hl : Real.log (1 + 2 / M) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have : 0 < 2 / M := by positivity
    linarith
  unfold split delta
  rw [hlog]
  generalize Real.log (1 + 1 / M) = A
  generalize hB : Real.log (1 + 2 / M) = B
  have hB0 : B ≠ 0 := by simpa only [hB] using hl
  field_simp
  ring

theorem scaled_bounds {N t : ℝ} (hN : 0 < N) (ht : 0 ≤ t) :
    0 ≤ 1 / 4 - N * delta (N + t) ∧
      1 / 4 - N * delta (N + t) ≤ (t + 2) / (4 * N) := by
  have hM : 0 < N + t := by positivity
  have hM1 : N + t + 1 ≠ 0 := by positivity
  have hD : 0 < 4 * (N + t + 1) ^ 2 := by positivity
  have h4M : 0 < 4 * (N + t) := by positivity
  have h4N : 0 < 4 * N := by positivity
  obtain ⟨hlo, hhi⟩ := delta_bounds hM
  have hu : N * delta (N + t) ≤ 1 / 4 := by
    calc
      N * delta (N + t) ≤ N * (1 / (4 * (N + t))) :=
        mul_le_mul_of_nonneg_left hhi hN.le
      _ = N / (4 * (N + t)) := by ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ h4M).2
        nlinarith
  have hl : N * (N + t) / (4 * (N + t + 1) ^ 2) ≤
      N * delta (N + t) := by
    calc
      N * (N + t) / (4 * (N + t + 1) ^ 2) =
          N * ((N + t) / (4 * (N + t + 1) ^ 2)) := by ring
      _ ≤ N * delta (N + t) := mul_le_mul_of_nonneg_left hlo hN.le
  have hr : 1 / 4 - N * (N + t) / (4 * (N + t + 1) ^ 2) ≤
      (t + 2) / (4 * N) := by
    have he : 1 / 4 - N * (N + t) / (4 * (N + t + 1) ^ 2) =
        ((N + t + 1) ^ 2 - N * (N + t)) / (4 * (N + t + 1) ^ 2) := by
      field_simp
    rw [he]
    apply (div_le_div_iff₀ hD h4N).2
    have hp : 0 ≤ t * (t + 2) * (N + t) +
        (2 * t + 3) * (N + t) + 2 * t + 2 := by positivity
    nlinarith only [hp]
  constructor <;> linarith

end PiCt
