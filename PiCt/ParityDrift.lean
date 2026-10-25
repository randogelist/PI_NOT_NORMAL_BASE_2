import PiCt.BinaryWords

/-!+A zero-allowed drift criterion for a bounded even-aligned alternating run.
Every assumption about the drift and its residual is explicit. In particular,
this module does not assert that the digits of pi admit such a decomposition.
-/

namespace PiCt.ParityDrift

noncomputable section

def digit (b : ℕ → Bool) (n : ℕ) : ℝ := if b n then 1 else 0

def pairDifference (b : ℕ → Bool) (j : ℕ) : ℝ :=
  digit b (2 * j) - digit b (2 * j + 1)

def paritySum (b : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, pairDifference b j

/-- An occurrence of `(01)^r` starting at the even position `2*j`. -/
def Alternating01At (b : ℕ → Bool) (j r : ℕ) : Prop :=
  ∀ k < r, b (2 * (j + k)) = false ∧ b (2 * (j + k) + 1) = true

theorem pairDifference_of_alternating01 {b : ℕ → Bool} {j r k : ℕ}
    (hblock : Alternating01At b j r) (hk : k < r) :
    pairDifference b (j + k) = -1 := by
  obtain ⟨hzero, hone⟩ := hblock k hk
  simp [pairDifference, digit, hzero, hone]

/-- Every pair in the specified run contributes exactly `-1`. -/
theorem paritySum_sub_of_alternating01 {b : ℕ → Bool} {j r : ℕ}
    (hblock : Alternating01At b j r) :
    paritySum b (j + r) - paritySum b j = -(r : ℝ) := by
  unfold paritySum
  rw [Finset.sum_range_add_sub_sum_range]
  calc
    (∑ k ∈ Finset.range r, pairDifference b (j + k)) =
        ∑ _k ∈ Finset.range r, (-1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact pairDifference_of_alternating01 hblock (Finset.mem_range.mp hk)
    _ = -(r : ℝ) := by simp

/-- A nondecreasing drift and uniformly bounded residual bound every such run.
The drift may be constant, including identically zero. -/
theorem alternating01_bound_of_monotone
    (b : ℕ → Bool) (H V : ℕ → ℝ) (B : ℝ)
    (hH : Monotone H)
    (hdecomp : ∀ m, paritySum b m = H m + V m)
    (hbound : ∀ m, |V m| ≤ B)
    {j r : ℕ} (hblock : Alternating01At b j r) :
    (r : ℝ) ≤ 2 * B := by
  have hinc : H j ≤ H (j + r) := hH (Nat.le_add_right j r)
  have hleft : V j ≤ B := (abs_le.mp (hbound j)).2
  have hright : -B ≤ V (j + r) := (abs_le.mp (hbound (j + r))).1
  have hsum := paritySum_sub_of_alternating01 hblock
  rw [hdecomp (j + r), hdecomp j] at hsum
  linarith

/-- Partial sums of nonnegative increments form a nondecreasing drift. -/
theorem partialSums_monotone (h : ℕ → ℝ) (hh : ∀ j, 0 ≤ h j) :
    Monotone (fun m => ∑ j ∈ Finset.range m, h j) := by
  intro m n hmn
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro j _hj _hnot
  exact hh j

/-- Increment form of the criterion; strict positivity is not required. -/
theorem alternating01_bound_of_increments
    (b : ℕ → Bool) (h V : ℕ → ℝ) (B : ℝ)
    (hh : ∀ j, 0 ≤ h j)
    (hdecomp : ∀ m, paritySum b m = (∑ j ∈ Finset.range m, h j) + V m)
    (hbound : ∀ m, |V m| ≤ B)
    {j r : ℕ} (hblock : Alternating01At b j r) :
    (r : ℝ) ≤ 2 * B := by
  exact alternating01_bound_of_monotone b
    (fun m => ∑ j ∈ Finset.range m, h j) V B
    (partialSums_monotone h hh) hdecomp hbound hblock

theorem not_alternating01_of_monotone
    (b : ℕ → Bool) (H V : ℕ → ℝ) (B : ℝ)
    (hH : Monotone H)
    (hdecomp : ∀ m, paritySum b m = H m + V m)
    (hbound : ∀ m, |V m| ≤ B)
    {j r : ℕ} (hr : 2 * B < (r : ℝ)) :
    ¬ Alternating01At b j r := by
  intro hblock
  have hle := alternating01_bound_of_monotone b H V B hH hdecomp hbound hblock
  linarith

end

end PiCt.ParityDrift
