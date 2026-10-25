import PiCt.LogCore
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Products of the analytic split factors. These are an explicitly defined
analytic model, not actual pi word frequencies or conditional digit laws.
For any fixed finite sign pattern the correction vanishes with the starting
position. Growing word length is a different limiting question.
-/

open Filter
open scoped Topology

namespace PiCt.AnalyticWordProduct

noncomputable section

/-- `true` selects the minus sign; `false` selects the plus sign. -/
def factor (negative : ℕ → Bool) (n k : ℕ) : ℝ :=
  if negative k then 1 / 2 - delta ((n : ℝ) + k + 1)
  else 1 / 2 + delta ((n : ℝ) + k + 1)

def wordProduct (negative : ℕ → Bool) (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | len + 1 => wordProduct negative n len * factor negative n len

theorem wordProduct_eq_prod (negative : ℕ → Bool) (n len : ℕ) :
    wordProduct negative n len = ∏ k ∈ Finset.range len, factor negative n k := by
  induction len with
  | zero => simp [wordProduct]
  | succ len ih => simp only [wordProduct, Finset.prod_range_succ, ih]

theorem offset_delta_bounds (n k : ℕ) :
    0 ≤ delta ((n : ℝ) + k + 1) ∧
      delta ((n : ℝ) + k + 1) ≤ 1 / (4 * ((n : ℝ) + 1)) := by
  have hp : 0 < (n : ℝ) + k + 1 := by positivity
  obtain ⟨hlo, hhi⟩ := delta_bounds hp
  constructor
  · have hq : 0 ≤ ((n : ℝ) + k + 1) / (4 * ((n : ℝ) + k + 1 + 1) ^ 2) :=
      le_of_lt (by positivity)
    exact hq.trans hlo
  · exact hhi.trans (one_div_le_one_div_of_le (by positivity)
      (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith))

theorem factor_bounds (negative : ℕ → Bool) (n k : ℕ) :
    0 ≤ factor negative n k ∧ factor negative n k ≤ 1 := by
  have hd := offset_delta_bounds n k
  have hc : 1 / (4 * ((n : ℝ) + 1)) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  unfold factor
  split_ifs <;> constructor <;> linarith

theorem factor_error (negative : ℕ → Bool) (n k : ℕ) :
    |factor negative n k - 1 / 2| ≤ 1 / (4 * ((n : ℝ) + 1)) := by
  have hd := offset_delta_bounds n k
  unfold factor
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem wordProduct_nonneg (negative : ℕ → Bool) (n len : ℕ) :
    0 ≤ wordProduct negative n len := by
  induction len with
  | zero => norm_num [wordProduct]
  | succ len ih => exact mul_nonneg ih (factor_bounds negative n len).1

/-- Accumulating finitely many analytic corrections still gives an error
that tends to zero with the starting position. -/
theorem wordProduct_error (negative : ℕ → Bool) (n len : ℕ) :
    |wordProduct negative n len - (1 / 2 : ℝ) ^ len| ≤
      (len : ℝ) / (4 * ((n : ℝ) + 1)) := by
  induction len with
  | zero => simp [wordProduct]
  | succ len ih =>
      have hf := factor_bounds negative n len
      have hfa : |factor negative n len| ≤ 1 :=
        by rw [abs_of_nonneg hf.1]; exact hf.2
      have hp0 : 0 ≤ (1 / 2 : ℝ) ^ len := by positivity
      have hp1 : |(1 / 2 : ℝ) ^ len| ≤ 1 := by
        rw [abs_of_nonneg hp0]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have he : wordProduct negative n (len + 1) - (1 / 2 : ℝ) ^ (len + 1) =
          (wordProduct negative n len - (1 / 2 : ℝ) ^ len) * factor negative n len +
          (1 / 2 : ℝ) ^ len * (factor negative n len - 1 / 2) := by
        rw [wordProduct, pow_succ]
        ring
      rw [he]
      calc
        |(wordProduct negative n len - (1 / 2 : ℝ) ^ len) * factor negative n len +
            (1 / 2 : ℝ) ^ len * (factor negative n len - 1 / 2)|
            ≤ |wordProduct negative n len - (1 / 2 : ℝ) ^ len| * |factor negative n len| +
              |(1 / 2 : ℝ) ^ len| * |factor negative n len - 1 / 2| := by
                simpa only [abs_mul] using abs_add_le
                  ((wordProduct negative n len - (1 / 2 : ℝ) ^ len) * factor negative n len)
                  ((1 / 2 : ℝ) ^ len * (factor negative n len - 1 / 2))
        _ ≤ (len : ℝ) / (4 * ((n : ℝ) + 1)) + 1 / (4 * ((n : ℝ) + 1)) := by
          have hfirst := mul_le_mul ih hfa (abs_nonneg _) (by positivity : 0 ≤
            (len : ℝ) / (4 * ((n : ℝ) + 1)))
          have hsecond := mul_le_mul hp1 (factor_error negative n len) (abs_nonneg _) zero_le_one
          nlinarith
        _ = ((len + 1 : ℕ) : ℝ) / (4 * ((n : ℝ) + 1)) := by
          push_cast
          ring

/-- Fixed word length is essential in this statement. -/
theorem wordProduct_fixed_length_limit (negative : ℕ → Bool) (len : ℕ) :
    Tendsto (fun n : ℕ => wordProduct negative n len) atTop
      (𝓝 ((1 / 2 : ℝ) ^ len)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => wordProduct_error negative n len)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((len : ℝ) / 4)
  convert h using 1
  · ext n
    field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  · simp only [mul_zero]

/-- Averaging the analytic model over starting positions also retains the
uniform fixed-word value. This is not an assertion about actual word counts. -/
theorem wordProduct_average_limit (negative : ℕ → Bool) (len : ℕ) :
    Tendsto (fun N : ℕ => (N⁻¹ : ℝ) *
      ∑ n ∈ Finset.range N, wordProduct negative n len) atTop
      (𝓝 ((1 / 2 : ℝ) ^ len)) :=
  (wordProduct_fixed_length_limit negative len).cesaro

/-- Choosing the suppressed factor at every position decreases the finite
product, but does not change its fixed-length limit. -/
theorem suppressedProduct_le (n len : ℕ) :
    wordProduct (fun _ => true) n len ≤ (1 / 2 : ℝ) ^ len := by
  induction len with
  | zero => simp [wordProduct]
  | succ len ih =>
      have hf0 := (factor_bounds (fun _ => true) n len).1
      have hf1 : factor (fun _ => true) n len ≤ (1 / 2 : ℝ) := by
        have hd := (offset_delta_bounds n len).1
        simp only [factor, if_true]
        linarith
      rw [wordProduct, pow_succ]
      exact mul_le_mul ih hf1 hf0 (by positivity)

theorem suppressedProduct_error (n len : ℕ) :
    0 ≤ (1 / 2 : ℝ) ^ len - wordProduct (fun _ => true) n len ∧
      (1 / 2 : ℝ) ^ len - wordProduct (fun _ => true) n len ≤
        (len : ℝ) / (4 * ((n : ℝ) + 1)) := by
  have hle := suppressedProduct_le n len
  constructor
  · linarith
  · have h := wordProduct_error (fun _ => true) n len
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at h
    exact h

/-- Coherent positive analytic bias favors the plus product over the minus product. -/
theorem minusProduct_le_plusProduct (n len : ℕ) :
    wordProduct (fun _ => true) n len ≤ wordProduct (fun _ => false) n len := by
  induction len with
  | zero => simp [wordProduct]
  | succ len ih =>
      rw [wordProduct, wordProduct]
      have hf : factor (fun _ => true) n len ≤ factor (fun _ => false) n len := by
        have hd := (offset_delta_bounds n len).1
        simp only [factor, Bool.false_eq_true, if_false, if_true]
        linarith
      exact mul_le_mul ih hf (factor_bounds (fun _ => true) n len).1
        (wordProduct_nonneg (fun _ => false) n len)

/-- For the two coherent orientations together, this analytic product model
has no total suppression: the combined mass is at least the uniform baseline. -/
theorem combinedProduct_ge_uniform (n len : ℕ) :
    2 * (1 / 2 : ℝ) ^ len ≤
      wordProduct (fun _ => false) n len + wordProduct (fun _ => true) n len := by
  induction len with
  | zero => norm_num [wordProduct]
  | succ len ih =>
      have horder := minusProduct_le_plusProduct n len
      have hd := (offset_delta_bounds n len).1
      have hp : 0 ≤ delta ((n : ℝ) + len + 1) *
          (wordProduct (fun _ => false) n len - wordProduct (fun _ => true) n len) :=
        mul_nonneg hd (sub_nonneg.mpr horder)
      simp only [wordProduct, factor, Bool.false_eq_true, if_false, if_true, pow_succ]
      nlinarith

end

end PiCt.AnalyticWordProduct
