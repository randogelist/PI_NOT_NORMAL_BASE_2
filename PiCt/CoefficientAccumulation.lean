import PiCt.Instance

/-! Signed coefficients, aligned magnitudes, and the actual analytic mass
of a finite block. No digit-frequency identification is asserted. -/

open Filter
open scoped Topology

namespace PiCt.CoefficientAccumulation

theorem C_adjacent_cancel (t : ℕ) : C t + C (t + 1) = 0 := by
  unfold C
  rw [pow_succ]
  ring

theorem C_prefix_sum (L : ℕ) :
    (∑ t ∈ Finset.range L, C t) = (1 - (-1 : ℝ) ^ L) / 8 := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      unfold C
      rw [pow_succ]
      ring

theorem C_even_prefix_sum (r : ℕ) : (∑ t ∈ Finset.range (2 * r), C t) = 0 := by
  rw [C_prefix_sum]
  simp [pow_mul]

theorem C_aligned (t : ℕ) : (-1 : ℝ) ^ t * C t = 1 / 4 := by
  unfold C
  rw [← mul_div_assoc, ← mul_pow]
  norm_num

theorem C_aligned_prefix_sum (L : ℕ) :
    (∑ t ∈ Finset.range L, (-1 : ℝ) ^ t * C t) = (L : ℝ) / 4 := by
  simp only [C_aligned, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

noncomputable def blockMass (M : ℝ) (L : ℕ) : ℝ :=
  ∑ t ∈ Finset.range L, delta (M + (t : ℝ))

theorem blockMass_bounds {M : ℝ} (hM : 0 < M) (L : ℕ) :
    0 ≤ blockMass M L ∧ blockMass M L ≤ (L : ℝ) / (4 * M) := by
  have hterm (t : ℕ) : 0 ≤ delta (M + (t : ℝ)) ∧
      delta (M + (t : ℝ)) ≤ 1 / (4 * M) := by
    have ht := delta_bounds (by positivity : 0 < M + (t : ℝ))
    constructor
    · exact (by positivity : 0 ≤ (M + (t : ℝ)) /
        (4 * (M + (t : ℝ) + 1) ^ 2)).trans ht.1
    · exact ht.2.trans (one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) t]))
  constructor
  · exact Finset.sum_nonneg (fun t _ => (hterm t).1)
  · calc
      blockMass M L ≤ ∑ _t ∈ Finset.range L, 1 / (4 * M) :=
        Finset.sum_le_sum (fun t _ => (hterm t).2)
      _ = (L : ℝ) / (4 * M) := by simp [div_eq_mul_inv]

/-- For every fixed word length, its analytic block correction vanishes
as the starting dyadic scale tends to infinity. -/
theorem fixed_length_mass_tendsto_zero (L : ℕ) :
    Tendsto (fun a => blockMass (scale a) L) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero
  · intro a
    exact (blockMass_bounds (scale_pos a) L).1
  · intro a
    exact (blockMass_bounds (scale_pos a) L).2
  · have h := inverse_scale_tendsto.const_mul ((L : ℝ) / 4)
    convert h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]

end PiCt.CoefficientAccumulation
