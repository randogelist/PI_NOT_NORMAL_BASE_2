import PiCt.AlternatingFrequency
import PiCt.AlternatingExcursions

/-!
Ordinary overlapping frequencies of long alternating words are controlled
by empirical tails of the actual parity residual.  A sufficiently small
residual-tail frequency is a conditional route to nonnormality.  No such
estimate is asserted for pi.
-/

open Filter
open scoped Topology

namespace PiCt.AlternatingTailClosure

open BinaryWords AlternatingFrequency AlternatingExcursions

noncomputable section

private theorem disjoint_indicators_le (p q s : Prop)
    (hpq : ¬(p ∧ q)) (hp : p → s) (hq : q → s) :
    indicator p + indicator q ≤ indicator s := by
  classical
  by_cases h1 : p
  · have h2 : ¬q := fun h => hpq ⟨h1, h⟩
    simp [indicator, h1, h2, hp h1]
  · by_cases h2 : q
    · simp [indicator, h1, h2, hq h2]
    · simpa only [indicator, if_neg h1, if_neg h2, zero_add] using
        (indicator_bounds s).1

/-- For positive `len`, the sum is 0 or 1 because the two alternating words differ. -/
def wordIndicator (b : ℕ → Bool) (len n : ℕ) : ℝ :=
  indicator (blockCode b n len = blockCode (alternating false) 0 len) +
  indicator (blockCode b n len = blockCode (alternating true) 0 len)

private theorem wordIndicator_le_of_occurrence
    (b : ℕ → Bool) (len n : ℕ) (hlen : 0 < len) (s : Prop)
    (hs : ∀ orientation : Bool,
      blockCode b n len = blockCode (alternating orientation) 0 len → s) :
    wordIndicator b len n ≤ indicator s := by
  apply disjoint_indicators_le
  · rintro ⟨h0, h1⟩
    exact alternating_codes_ne len hlen (h0.symm.trans h1)
  · exact hs false
  · exact hs true

theorem wordIndicator_even_le (b : ℕ → Bool) (j r : ℕ) :
    wordIndicator b (2 * r + 1) (2 * j) ≤ indicator (AltEitherAt b j r) := by
  apply wordIndicator_le_of_occurrence b _ _ (by omega)
  intro orientation hc
  have hp := code_occurrence_even_pairs b j r orientation hc
  cases orientation
  · exact Or.inl hp
  · exact Or.inr hp

theorem wordIndicator_odd_le (b : ℕ → Bool) (j r : ℕ) :
    wordIndicator b (2 * r + 1) (2 * j + 1) ≤
      indicator (AltEitherAt b (j + 1) r) := by
  apply wordIndicator_le_of_occurrence b _ _ (by omega)
  intro orientation hc
  have hp := code_occurrence_odd_pairs b j r orientation hc
  cases orientation
  · exact Or.inr hp
  · exact Or.inl hp

private theorem sum_range_even_odd (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), g n) =
      ∑ j ∈ Finset.range N, (g (2 * j) + g (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

theorem totalFreq_eq_indicator_sum (b : ℕ → Bool) (N len : ℕ) :
    totalFreq b N len = (∑ n ∈ Finset.range N, wordIndicator b len n) / N := by
  unfold totalFreq wordFreq freq wordIndicator indicator
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs <;> rfl

/-- The odd starts cost one extra aligned starting position. -/
theorem ordinary_count_le_aligned (b : ℕ → Bool) (r N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), wordIndicator b (2 * r + 1) n) ≤
      2 * alignedCount b r N + 1 := by
  rw [sum_range_even_odd]
  have hp (j : ℕ) := add_le_add
    (wordIndicator_even_le b j r) (wordIndicator_odd_le b j r)
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hp j)
  simp only [Finset.sum_add_distrib] at hs
  have hshift := shifted_sum_le (fun j => indicator (AltEitherAt b j r))
    (fun j => indicator_bounds _) N 1
  unfold alignedCount
  simp only [Finset.sum_add_distrib]
  norm_num only [Nat.cast_one] at hshift
  linarith

/-- Exact finite ordinary-frequency bound, including the endpoint cost. -/
theorem totalFreq_le_residual_tail
    (b : ℕ → Bool) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) (r N : ℕ) (hN : 0 < N) :
    totalFreq b (2 * N) (2 * r + 1) ≤
      2 * tailFrequency (residual b a) ((r : ℝ) / 4) N +
        ((r : ℝ) + 1 / 2) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hordinary := ordinary_count_le_aligned b r N
  have haligned := aligned_count_le_tail b a ha r N
  rw [totalFreq_eq_indicator_sum]
  unfold tailFrequency
  push_cast
  apply (div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))).mpr
  have he :
      (2 * (tailCount (residual b a) ((r : ℝ) / 4) N / (N : ℝ)) +
        ((r : ℝ) + 1 / 2) / (N : ℝ)) * (2 * (N : ℝ)) =
      4 * tailCount (residual b a) ((r : ℝ) / 4) N + 2 * (r : ℝ) + 1 := by
    (field_simp [ne_of_gt hn]; ring)
  rw [he]
  linarith

/-- Normality has an explicit positive long-word target at every fixed `r`. -/
theorem normal_odd_alternating_target {b : ℕ → Bool}
    (hn : BinaryNormal b) (r : ℕ) :
    Tendsto (fun N : ℕ => totalFreq b (2 * N) (2 * r + 1)) atTop
      (𝓝 (1 / (4 : ℝ) ^ r)) := by
  have ht : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => show N ≤ 2 * N by omega) tendsto_id
  have h := (normal_totalFreq hn (2 * r + 1)).comp ht
  have he : (2 : ℝ) / 2 ^ (2 * r + 1) = 1 / (4 : ℝ) ^ r := by
    calc
      (2 : ℝ) / 2 ^ (2 * r + 1) = 2 / ((4 : ℝ) ^ r * 2) := by
        rw [pow_succ, pow_mul]
        norm_num
      _ = 1 / (4 : ℝ) ^ r := by field_simp
  simpa only [Function.comp_def, he] using h

/-- Sparse large residuals suffice.  Unlike the earlier closure, a uniform
bound on every residual value is not needed. -/
theorem not_normal_of_eventually_small_residual_tail
    (b : ℕ → Bool) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) (r : ℕ) {η : ℝ}
    (hgap : 2 * η < 1 / (4 : ℝ) ^ r)
    (htail : ∀ᶠ N : ℕ in atTop,
      tailFrequency (residual b a) ((r : ℝ) / 4) N ≤ η) :
    ¬ BinaryNormal b := by
  intro hn
  have hfreq := normal_odd_alternating_target hn r
  have herr : Tendsto (fun N : ℕ => ((r : ℝ) + 1 / 2) / (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun N : ℕ => 2 * η + ((r : ℝ) + 1 / 2) / (N : ℝ))
      atTop (𝓝 (2 * η)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  have hle : ∀ᶠ N : ℕ in atTop,
      totalFreq b (2 * N) (2 * r + 1) ≤
        2 * η + ((r : ℝ) + 1 / 2) / (N : ℝ) := by
    filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with N htail hN
    exact (totalFreq_le_residual_tail b a ha r N hN).trans (by linarith)
  exact (not_le_of_gt hgap) (le_of_tendsto_of_tendsto hfreq hupper hle)

/-- The actual-pi endpoint retains the empirical-tail estimate explicitly. -/
theorem PI_NOT_NORMAL_OF_SMALL_RESIDUAL_TAIL
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2)
    (r : ℕ) {η : ℝ} (hgap : 2 * η < 1 / (4 : ℝ) ^ r)
    (htail : ∀ᶠ N : ℕ in atTop,
      tailFrequency (residual piBits a) ((r : ℝ) / 4) N ≤ η) :
    ¬ BinaryNormal (bit Real.pi) := by
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact not_normal_of_eventually_small_residual_tail piBits a ha r hgap htail

/-- The finite bound for actual pi digits and the already defined analytic drift. -/
theorem PI_ALTERNATING_FREQUENCY_TAIL_BOUND (r N : ℕ) (hN : 0 < N) :
    totalFreq piBits (2 * N) (2 * r + 1) ≤
      2 * tailFrequency (AnalyticParityClosure.analyticResidual piBits)
        ((r : ℝ) / 4) N + ((r : ℝ) + 1 / 2) / N := by
  exact totalFreq_le_residual_tail piBits AnalyticDrift.analyticStep
    analyticStep_bounds r N hN

/-- The remaining actual-pi estimate is a tail-frequency bound, not a
uniform bound on all residuals. It remains an explicit hypothesis. -/
theorem PI_NOT_NORMAL_OF_SMALL_ANALYTIC_RESIDUAL_TAIL
    (r : ℕ) {η : ℝ} (hgap : 2 * η < 1 / (4 : ℝ) ^ r)
    (htail : ∀ᶠ N : ℕ in atTop,
      tailFrequency (AnalyticParityClosure.analyticResidual piBits)
        ((r : ℝ) / 4) N ≤ η) :
    ¬ BinaryNormal (bit Real.pi) := by
  exact PI_NOT_NORMAL_OF_SMALL_RESIDUAL_TAIL AnalyticDrift.analyticStep
    analyticStep_bounds r hgap htail

end

end PiCt.AlternatingTailClosure
