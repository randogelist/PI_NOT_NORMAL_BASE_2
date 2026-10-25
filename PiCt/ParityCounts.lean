import PiCt.ParityDrift

/-! Exact counts of even-aligned `01` and `10` pairs and the quantization
obstruction to a pointwise approximation by a small positive drift. -/

namespace PiCt.ParityCounts

open BinaryWords ParityDrift

noncomputable section

/-- Number of `01` words among the first `m` even-aligned pairs. -/
def count01 (b : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, if blockCode b (2 * j) 2 = 1 then (1 : ℝ) else 0

/-- Number of `10` words among the first `m` even-aligned pairs. -/
def count10 (b : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, if blockCode b (2 * j) 2 = 2 then (1 : ℝ) else 0

theorem pairDifference_eq_code_indicators (b : ℕ → Bool) (j : ℕ) :
    pairDifference b j =
      (if blockCode b (2 * j) 2 = 2 then (1 : ℝ) else 0) -
      (if blockCode b (2 * j) 2 = 1 then (1 : ℝ) else 0) := by
  cases hb : b (2 * j) <;> cases hc : b (2 * j + 1) <;>
    simp [pairDifference, digit, blockCode, hb, hc]

theorem paritySum_eq_count_difference (b : ℕ → Bool) (m : ℕ) :
    paritySum b m = count10 b m - count01 b m := by
  unfold paritySum count10 count01
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  exact pairDifference_eq_code_indicators b j

theorem pairDifference_values (b : ℕ → Bool) (j : ℕ) :
    pairDifference b j = -1 ∨ pairDifference b j = 0 ∨ pairDifference b j = 1 := by
  cases hb : b (2 * j) <;> cases hc : b (2 * j + 1) <;>
    simp [pairDifference, digit, hb, hc]

/-- Quantization prevents approximating any of these three values with error
smaller than a positive target of size at most one half. -/
theorem quantized_error_ge_step {q h : ℝ}
    (hq : q = -1 ∨ q = 0 ∨ q = 1) (h0 : 0 < h) (hhalf : h ≤ 1 / 2) :
    h ≤ |q - h| := by
  rcases hq with hq | hq | hq
  · rw [hq, abs_of_neg (by linarith : -1 - h < 0)]
    linarith
  · rw [hq, zero_sub, abs_neg, abs_of_pos h0]
  · rw [hq, abs_of_nonneg (by linarith : 0 ≤ 1 - h)]
    linarith

theorem pair_error_ge_step (b : ℕ → Bool) (j : ℕ) {h : ℝ}
    (h0 : 0 < h) (hhalf : h ≤ 1 / 2) :
    h ≤ |pairDifference b j - h| :=
  quantized_error_ge_step (pairDifference_values b j) h0 hhalf

end

end PiCt.ParityCounts
