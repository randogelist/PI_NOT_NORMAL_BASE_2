import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Tactic
import PiCt.LogCore

namespace PiCt
namespace ComplexRepresentative

/-- The standard complex arctangent primitive, anchored at the genuine real pi. -/
noncomputable def primitive (z : ℂ) : ℂ := 4 * Complex.arctan z

theorem primitive_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 4 * ((-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)))
      (primitive z) := by
  simpa only [primitive] using (Complex.hasSum_arctan hz).mul_left (4 : ℂ)

theorem primitive_one : primitive 1 = (Real.pi : ℂ) := by
  unfold primitive
  rw [← Complex.ofReal_one, ← Complex.ofReal_arctan, Real.arctan_one]
  push_cast
  ring

theorem primitive_log_quotient (z : ℂ) :
    primitive z = (-2 * Complex.I) *
      Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  unfold primitive Complex.arctan
  ring

theorem primitive_log_difference {z : ℂ} (hz : ‖z‖ < 1) :
    primitive z = (-2 * Complex.I) *
      (Complex.log (1 + z * Complex.I) - Complex.log (1 - z * Complex.I)) := by
  rw [primitive_log_quotient, ← Complex.hasSum_arctan_aux hz]
  simp only [sub_eq_add_neg]

/-- The imaginary slice stays strictly between the branch singularities. -/
theorem primitive_imaginary {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    primitive (Complex.I * (u : ℂ)) =
      (2 * Complex.I) * ((Real.log (1 + u) - Real.log (1 - u) : ℝ) : ℂ) := by
  have hm : 0 < 1 - u := sub_pos.mpr hu1
  have hp : 0 < 1 + u := by linarith
  have harg : (1 + (Complex.I * (u : ℂ)) * Complex.I) /
      (1 - (Complex.I * (u : ℂ)) * Complex.I) =
      (((1 - u) / (1 + u) : ℝ) : ℂ) := by
    push_cast
    have hi : Complex.I * (u : ℂ) * Complex.I = -(u : ℂ) := by
      calc
        Complex.I * (u : ℂ) * Complex.I = (u : ℂ) * (Complex.I * Complex.I) := by ring
        _ = -(u : ℂ) := by simp
    rw [hi]
    ring
  rw [primitive_log_quotient, harg, ← Complex.ofReal_log (le_of_lt (div_pos hm hp)),
    Real.log_div hm.ne' hp.ne']
  push_cast
  ring

theorem primitive_imaginary_im {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (primitive (Complex.I * (u : ℂ))).im =
      2 * (Real.log (1 + u) - Real.log (1 - u)) := by
  rw [primitive_imaginary hu0 hu1]
  simp

/-- Rational imaginary-ray inputs to the same arctangent representative. -/
noncomputable def ray (M s : ℝ) : ℝ := s / (2 * M + s)

theorem ray_nonneg {M s : ℝ} (hM : 0 < M) (hs : 0 ≤ s) : 0 ≤ ray M s := by
  unfold ray
  positivity

theorem ray_lt_one {M s : ℝ} (hM : 0 < M) (hs : 0 ≤ s) : ray M s < 1 := by
  unfold ray
  apply (div_lt_one (by linarith : 0 < 2 * M + s)).2
  linarith

theorem ray_ratio {M s : ℝ} (hM : 0 < M) (hs : 0 ≤ s) :
    (1 + ray M s) / (1 - ray M s) = 1 + s / M := by
  have hd : 2 * M + s ≠ 0 := ne_of_gt (by linarith : 0 < 2 * M + s)
  have hm : 1 - ray M s ≠ 0 := ne_of_gt (sub_pos.mpr (ray_lt_one hM hs))
  unfold ray at *
  field_simp
  ring

theorem primitive_ray_im {M s : ℝ} (hM : 0 < M) (hs : 0 ≤ s) :
    (primitive (Complex.I * (ray M s : ℂ))).im = 2 * Real.log (1 + s / M) := by
  have h0 := ray_nonneg hM hs
  have h1 := ray_lt_one hM hs
  have hm : 1 - ray M s ≠ 0 := ne_of_gt (sub_pos.mpr h1)
  have hp : 1 + ray M s ≠ 0 := ne_of_gt (by linarith)
  rw [primitive_imaginary_im h0 h1, ← Real.log_div hp hm, ray_ratio hM hs]

theorem ray_one (M : ℝ) : ray M 1 = 1 / (2 * M + 1) := rfl

theorem ray_two {M : ℝ} (hM : 0 < M) : ray M 2 = 1 / (M + 1) := by
  unfold ray
  field_simp

/-- Readout of the two rational imaginary points, not a binary-digit frequency. -/
noncomputable def splitReadout (M : ℝ) : ℝ :=
  (primitive (Complex.I * (ray M 1 : ℂ))).im /
  (primitive (Complex.I * (ray M 2 : ℂ))).im

theorem splitReadout_eq_split {M : ℝ} (hM : 0 < M) :
    splitReadout M = PiCt.split M := by
  unfold splitReadout
  rw [primitive_ray_im hM (by norm_num), primitive_ray_im hM (by norm_num)]
  unfold PiCt.split
  have hl : Real.log (1 + 2 / M) ≠ 0 := ne_of_gt (Real.log_pos (by
    have h : 0 < 2 / M := div_pos (by norm_num) hM
    linarith))
  field_simp

theorem splitReadout_eq_half_add_delta {M : ℝ} (hM : 0 < M) :
    splitReadout M = 1 / 2 + PiCt.delta M := by
  rw [splitReadout_eq_split hM, PiCt.split_eq_half_add_delta hM]

end ComplexRepresentative
end PiCt
