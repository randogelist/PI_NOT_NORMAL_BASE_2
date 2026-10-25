import PiCt.LogCore
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The frozen dyadic coefficient

All limits below hold for each fixed natural offset `t`.
`C` is the original signed logarithmic coefficient, not a digit frequency.
-/

open Filter
open scoped Topology

namespace PiCt

noncomputable def scale (a : ℕ) : ℝ := 2 ^ (10 + a)

noncomputable def G (a t : ℕ) : ℝ :=
  1 / 2 + (-1 : ℝ) ^ t * delta (scale a + t)

noncomputable def scaled (a t : ℕ) : ℝ :=
  scale a * (G a t - 1 / 2)

noncomputable def C (t : ℕ) : ℝ := (-1 : ℝ) ^ t / 4

theorem scale_pos (a : ℕ) : 0 < scale a := by
  unfold scale
  positivity

theorem scale_succ (a : ℕ) : scale (a + 1) = 2 * scale a := by
  unfold scale
  rw [show 10 + (a + 1) = (10 + a) + 1 by omega, pow_succ]
  ring

theorem scale_mono {a b : ℕ} (hab : a ≤ b) : scale a ≤ scale b := by
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.add_le_add_left hab 10)

theorem inverse_scale_tendsto :
    Tendsto (fun a : ℕ => 1 / scale a) atTop (𝓝 0) := by
  have h : Tendsto (fun a : ℕ => (1 / 2 : ℝ) ^ a) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h' := h.const_mul ((1 : ℝ) / 2 ^ 10)
  convert h' using 1 <;>
    simp [scale, pow_add, div_eq_mul_inv, inv_pow, mul_inv_rev, mul_comm]

theorem error_tendsto (t : ℕ) :
    Tendsto (fun a : ℕ => ((t : ℝ) + 2) / (4 * scale a)) atTop (𝓝 0) := by
  have h := inverse_scale_tendsto.const_mul (((t : ℝ) + 2) / 4)
  convert h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]

theorem scaled_eq (a t : ℕ) :
    scaled a t = (-1 : ℝ) ^ t * (scale a * delta (scale a + t)) := by
  unfold scaled G
  ring

theorem coefficient_error (a t : ℕ) :
    |scaled a t - C t| ≤ ((t : ℝ) + 2) / (4 * scale a) := by
  have hb := scaled_bounds (scale_pos a) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  rw [scaled_eq, C]
  have heq : (-1 : ℝ) ^ t * (scale a * delta (scale a + t)) - (-1 : ℝ) ^ t / 4 =
      (-1 : ℝ) ^ t * (scale a * delta (scale a + t) - 1 / 4) := by ring
  rw [heq, abs_mul, abs_neg_one_pow, one_mul, abs_sub_comm,
    abs_of_nonneg hb.1]
  exact hb.2

/-- Existence and identification of the original, signed coefficient. -/
theorem C_tendsto (t : ℕ) :
    Tendsto (fun a : ℕ => scaled a t) atTop (𝓝 (C t)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _) (fun a => coefficient_error a t)
    (error_tendsto t)

theorem C_exists_unique (t : ℕ) :
    ∃! c : ℝ, Tendsto (fun a : ℕ => scale a * (G a t - 1 / 2)) atTop (𝓝 c) := by
  refine ⟨C t, C_tendsto t, ?_⟩
  intro c hc
  exact tendsto_nhds_unique hc (C_tendsto t)

theorem C_abs (t : ℕ) : |C t| = 1 / 4 := by
  simp [C, abs_div]

theorem C_ne_zero (t : ℕ) : C t ≠ 0 := by
  unfold C
  exact div_ne_zero (pow_ne_zero t (by norm_num)) (by norm_num)

/-- The finite, explicit second-order remainder retained in the frozen result. -/
theorem G_remainder (a t : ℕ) :
    |G a t - 1 / 2 - C t / scale a| ≤ ((t : ℝ) + 2) / (4 * scale a ^ 2) := by
  have hn := scale_pos a
  have heq : G a t - 1 / 2 - C t / scale a = (scaled a t - C t) / scale a := by
    unfold scaled
    field_simp
  rw [heq, abs_div, abs_of_pos hn]
  calc
    |scaled a t - C t| / scale a ≤
        (((t : ℝ) + 2) / (4 * scale a)) / scale a :=
      div_le_div_of_nonneg_right (coefficient_error a t) hn.le
    _ = ((t : ℝ) + 2) / (4 * scale a ^ 2) := by ring

/-- Dyadic Cauchy control: the bound depends on the earlier scale only. -/
theorem coefficient_cauchy {a b : ℕ} (hab : a ≤ b) (t : ℕ) :
    |scaled b t - scaled a t| ≤ ((t : ℝ) + 2) / (4 * scale a) := by
  have hapos := scale_pos a
  have ha := scaled_bounds (scale_pos a) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  have hb := scaled_bounds (scale_pos b) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  have herr : ((t : ℝ) + 2) / (4 * scale b) ≤ ((t : ℝ) + 2) / (4 * scale a) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (scale_mono hab) (by norm_num)
  rw [scaled_eq, scaled_eq, ← mul_sub, abs_mul, abs_neg_one_pow, one_mul]
  apply abs_le.mpr
  constructor <;> linarith

/-- The unscaled analytic split still tends to one half. -/
theorem G_tendsto_half (t : ℕ) :
    Tendsto (fun a : ℕ => G a t) atTop (𝓝 (1 / 2)) := by
  have hp : Tendsto (fun a : ℕ => (1 / scale a) * scaled a t)
      atTop (𝓝 (0 * C t)) := inverse_scale_tendsto.mul (C_tendsto t)
  have heq (a : ℕ) : (1 / scale a) * scaled a t = G a t - 1 / 2 := by
    have hn : scale a ≠ 0 := (scale_pos a).ne'
    unfold scaled
    field_simp [hn]
  simp only [heq, zero_mul] at hp
  have hh := hp.add_const (1 / 2 : ℝ)
  simpa using hh

end PiCt
