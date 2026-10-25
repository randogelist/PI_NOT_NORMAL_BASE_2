import PiCt.ParityDrift
import PiCt.AnalyticParityClosure

/-!
Long alternating words force large residual excursions.  This gives a
frequency bound in terms of the density of large residual values, without
assuming that the residual is uniformly bounded.  No tail estimate for
pi's actual digit residual is asserted here.
-/

namespace PiCt.AlternatingExcursions

open ParityDrift

noncomputable section

def Alternating10At (b : ℕ → Bool) (j r : ℕ) : Prop :=
  ∀ k < r, b (2 * (j + k)) = true ∧ b (2 * (j + k) + 1) = false

def AltEitherAt (b : ℕ → Bool) (j r : ℕ) : Prop :=
  Alternating01At b j r ∨ Alternating10At b j r

def accumulated (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, a j

def residual (b : ℕ → Bool) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  paritySum b m - accumulated a m

theorem paritySum_sub_of_alternating10 {b : ℕ → Bool} {j r : ℕ}
    (hblock : Alternating10At b j r) :
    paritySum b (j + r) - paritySum b j = (r : ℝ) := by
  unfold paritySum
  rw [Finset.sum_range_add_sub_sum_range]
  calc
    (∑ k ∈ Finset.range r, pairDifference b (j + k)) =
        ∑ _k ∈ Finset.range r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hzero, hone⟩ := hblock k (Finset.mem_range.mp hk)
      simp [pairDifference, digit, hzero, hone]
    _ = (r : ℝ) := by simp

theorem accumulated_block_bounds (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) (j r : ℕ) :
    0 ≤ accumulated a (j + r) - accumulated a j ∧
      accumulated a (j + r) - accumulated a j ≤ (r : ℝ) / 2 := by
  unfold accumulated
  rw [Finset.sum_range_add_sub_sum_range]
  constructor
  · exact Finset.sum_nonneg (fun k _ => (ha (j + k)).1)
  · calc
      (∑ k ∈ Finset.range r, a (j + k)) ≤
          ∑ _k ∈ Finset.range r, (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun k _ => (ha (j + k)).2)
      _ = (r : ℝ) / 2 := by simp [div_eq_mul_inv]

/-- Both orientations cost at least half the run length in endpoint
residual magnitudes when the analytic drift step is between zero and one half. -/
theorem residual_excursion (b : ℕ → Bool) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) {j r : ℕ}
    (hblock : AltEitherAt b j r) :
    (r : ℝ) / 2 ≤ |residual b a j| + |residual b a (j + r)| := by
  have hA := accumulated_block_bounds a ha j r
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases hblock with hblock | hblock
  · have hS := paritySum_sub_of_alternating01 hblock
    have h0 := le_abs_self (residual b a j)
    have h1 := neg_le_abs (residual b a (j + r))
    unfold residual at *
    linarith
  · have hS := paritySum_sub_of_alternating10 hblock
    have h0 := neg_le_abs (residual b a j)
    have h1 := le_abs_self (residual b a (j + r))
    unfold residual at *
    linarith

theorem alternating_endpoint_tail (b : ℕ → Bool) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) {j r : ℕ}
    (hblock : AltEitherAt b j r) :
    (r : ℝ) / 4 ≤ |residual b a j| ∨
      (r : ℝ) / 4 ≤ |residual b a (j + r)| := by
  have h := residual_excursion b a ha hblock
  by_contra hn
  push Not at hn
  linarith

def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

theorem indicator_bounds (p : Prop) : 0 ≤ indicator p ∧ indicator p ≤ 1 := by
  classical
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_le_add_of_or (p q r : Prop) (h : p → q ∨ r) :
    indicator p ≤ indicator q + indicator r := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp_all [indicator]

def alignedCount (b : ℕ → Bool) (r N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, indicator (AltEitherAt b j r)

def tailCount (E : ℕ → ℝ) (h : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, indicator (h ≤ |E j|)

def alignedFrequency (b : ℕ → Bool) (r N : ℕ) : ℝ := alignedCount b r N / N

def tailFrequency (E : ℕ → ℝ) (h : ℝ) (N : ℕ) : ℝ := tailCount E h N / N

/-- Shifting an indicator average changes its unnormalized count by at most
its shift length.  The statement also holds for any values in `[0,1]`. -/
theorem shifted_sum_le (g : ℕ → ℝ)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 1) (N r : ℕ) :
    (∑ j ∈ Finset.range N, g (j + r)) ≤
      (∑ j ∈ Finset.range N, g j) + (r : ℝ) := by
  have h0 : 0 ≤ ∑ j ∈ Finset.range r, g j :=
    Finset.sum_nonneg (fun j _ => (hg j).1)
  have h1 : (∑ j ∈ Finset.range r, g (N + j)) ≤ (r : ℝ) := by
    calc
      (∑ j ∈ Finset.range r, g (N + j)) ≤
          ∑ _j ∈ Finset.range r, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (hg (N + j)).2)
      _ = (r : ℝ) := by simp
  have hs : (∑ j ∈ Finset.range N, g (j + r)) =
      ∑ j ∈ Finset.range N, g (r + j) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Nat.add_comm]
  have he0 := Finset.sum_range_add g r N
  have he1 := Finset.sum_range_add g N r
  rw [Nat.add_comm r N] at he0
  linarith

theorem aligned_count_le_tail (b : ℕ → Bool) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) (r N : ℕ) :
    alignedCount b r N ≤
      2 * tailCount (residual b a) ((r : ℝ) / 4) N + (r : ℝ) := by
  have hpoint (j : ℕ) := indicator_le_add_of_or
    (AltEitherAt b j r)
    ((r : ℝ) / 4 ≤ |residual b a j|)
    ((r : ℝ) / 4 ≤ |residual b a (j + r)|)
    (alternating_endpoint_tail b a ha)
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hpoint j)
  rw [Finset.sum_add_distrib] at hsum
  have hshift := shifted_sum_le
    (fun j => indicator ((r : ℝ) / 4 ≤ |residual b a j|))
    (fun j => indicator_bounds _) N r
  unfold alignedCount tailCount
  linarith

/-- A statistical bound: large residuals may exist, provided their empirical
tail frequency is small enough.  No such tail-frequency estimate for pi is
asserted by this theorem. -/
theorem aligned_frequency_le_tail (b : ℕ → Bool) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / 2) (r N : ℕ) (hN : 0 < N) :
    alignedFrequency b r N ≤
      2 * tailFrequency (residual b a) ((r : ℝ) / 4) N + (r : ℝ) / N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := div_le_div_of_nonneg_right (aligned_count_le_tail b a ha r N) hNp.le
  unfold alignedFrequency tailFrequency
  simpa only [add_div, mul_div_assoc] using h

/-- The exact pi-representative drift satisfies the required step bounds
unconditionally, including its initial zero segment. -/
theorem analyticStep_bounds (j : ℕ) :
    0 ≤ AnalyticDrift.analyticStep j ∧ AnalyticDrift.analyticStep j ≤ 1 / 2 := by
  refine ⟨AnalyticDrift.analyticStep_nonneg j, ?_⟩
  by_cases hj : j < 512
  · simp [AnalyticDrift.analyticStep, hj]
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have h0 := (delta_bounds (M := 2 * (j : ℝ)) (by linarith)).2
    have h1 := (delta_bounds (M := 2 * (j : ℝ) + 1) (by linarith)).2
    have hu0 : 1 / (4 * (2 * (j : ℝ))) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hu1 : 1 / (4 * (2 * (j : ℝ) + 1)) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    simp only [AnalyticDrift.analyticStep, if_neg hj]
    linarith

theorem residual_analyticStep (b : ℕ → Bool) (m : ℕ) :
    residual b AnalyticDrift.analyticStep m =
      AnalyticParityClosure.analyticResidual b m := rfl

/-- Actual pi specialization: the frequency bound has no caller-supplied
analytic or digit-identification premise. The residual tail remains unevaluated. -/
theorem PI_ALIGNED_ALTERNATING_FREQUENCY_BOUND (r N : ℕ) (hN : 0 < N) :
    alignedFrequency BinaryWords.piBits r N ≤
      2 * tailFrequency (AnalyticParityClosure.analyticResidual BinaryWords.piBits)
        ((r : ℝ) / 4) N + (r : ℝ) / N := by
  exact aligned_frequency_le_tail BinaryWords.piBits AnalyticDrift.analyticStep
    analyticStep_bounds r N hN

end

end PiCt.AlternatingExcursions
