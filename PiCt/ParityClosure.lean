import PiCt.DyadicParity
import PiCt.WordOccurrence

/-!
Closure for the original even/odd digit architecture, allowing zero drift.
All pi-specific remainder estimates are explicit unresolved hypotheses.
This route excludes a sufficiently long alternating word; it does not
assert an incorrect frequency for either four-bit constant word.
-/

namespace PiCt.ParityClosure

open BinaryWords ParityDrift

theorem not_normal_of_monotone_drift
    (b : ℕ → Bool) (H V : ℕ → ℝ) (B : ℝ)
    (hH : Monotone H)
    (hdecomp : ∀ m, paritySum b m = H m + V m)
    (hbound : ∀ m, |V m| ≤ B) : ¬ BinaryNormal b := by
  intro hn
  obtain ⟨r, hr⟩ := exists_nat_gt (2 * B)
  obtain ⟨j, hj⟩ := WordOccurrence.normal_even_alternating hn r
  exact (not_le_of_gt hr)
    (alternating01_bound_of_monotone b H V B hH hdecomp hbound hj)

/-- The case where every drift coefficient vanishes is included explicitly. -/
theorem not_normal_of_bounded_parity_sum
    (b : ℕ → Bool) (B : ℝ) (hbound : ∀ m, |paritySum b m| ≤ B) :
    ¬ BinaryNormal b := by
  apply not_normal_of_monotone_drift b (fun _ => 0) (paritySum b) B
  · intro a c hac
    exact le_refl _
  · intro m
    simp
  · exact hbound

/-- Any bound after a finite initial segment extends to some global bound. -/
theorem exists_global_bound_of_tail (V : ℕ → ℝ) (B : ℝ) (M : ℕ)
    (hb : ∀ m, M ≤ m → |V m| ≤ B) : ∃ B' : ℝ, ∀ m, |V m| ≤ B' := by
  refine ⟨|B| + ∑ k ∈ Finset.range M, |V k|, ?_⟩
  intro m
  have hs : 0 ≤ ∑ k ∈ Finset.range M, |V k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg (V k))
  by_cases hm : m < M
  · have hterm : |V m| ≤ ∑ k ∈ Finset.range M, |V k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (V k)) (Finset.mem_range.mpr hm)
    linarith [abs_nonneg B]
  · have ht := hb m (Nat.le_of_not_gt hm)
    linarith [le_abs_self B]

theorem not_normal_of_tail_bounded_monotone_drift
    (b : ℕ → Bool) (H V : ℕ → ℝ) (B : ℝ) (M : ℕ)
    (hH : Monotone H)
    (hdecomp : ∀ m, paritySum b m = H m + V m)
    (hbound : ∀ m, M ≤ m → |V m| ≤ B) : ¬ BinaryNormal b := by
  obtain ⟨B', hb⟩ := exists_global_bound_of_tail V B M hbound
  exact not_normal_of_monotone_drift b H V B' hH hdecomp hb

/-- Nonnegative coefficient magnitudes may tend to zero or equal zero.
The exact remainder is taken from actual digits and actual dyadic addresses. -/
theorem not_normal_of_dyadic_remainder
    (b : ℕ → Bool) (magnitude : ℕ → ℝ)
    (hc : ∀ t, 0 ≤ magnitude t)
    (hbound : ∃ B : ℝ, ∀ m, |DyadicParity.remainder b magnitude m| ≤ B) :
    ¬ BinaryNormal b := by
  obtain ⟨B, hb⟩ := hbound
  exact not_normal_of_monotone_drift b (DyadicParity.accumulated magnitude)
    (DyadicParity.remainder b magnitude) B
    (DyadicParity.accumulated_monotone magnitude hc)
    (DyadicParity.decomposition b magnitude) hb

theorem PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER
    (magnitude : ℕ → ℝ) (hc : ∀ t, 0 ≤ magnitude t)
    (hbound : ∃ B : ℝ, ∀ m, |DyadicParity.remainder piBits magnitude m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) := by
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact not_normal_of_dyadic_remainder piBits magnitude hc hbound

theorem PI_NOT_NORMAL_OF_TAIL_PARITY_REMAINDER
    (magnitude : ℕ → ℝ) (hc : ∀ t, 0 ≤ magnitude t)
    (hbound : ∃ B : ℝ, ∃ M : ℕ, ∀ m, M ≤ m →
      |DyadicParity.remainder piBits magnitude m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) := by
  obtain ⟨B, M, hb⟩ := hbound
  exact PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER magnitude hc
    (exists_global_bound_of_tail (DyadicParity.remainder piBits magnitude) B M hb)

/-- The old frozen analytic coefficient is used without changing its value.
Only the actual digit remainder bound remains a premise here. -/
theorem PI_NOT_NORMAL_OF_FROZEN_PARITY_REMAINDER
    (hbound : ∃ B : ℝ, ∀ m,
      |DyadicParity.remainder piBits DyadicParity.frozenMagnitude m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) :=
  PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER
    DyadicParity.frozenMagnitude DyadicParity.frozenMagnitude_nonneg hbound

/-- An explicit zero-coefficient instance, still conditional on its remainder bound. -/
theorem PI_NOT_NORMAL_OF_ZERO_COEFFICIENT_REMAINDER
    (hbound : ∃ B : ℝ, ∀ m, |DyadicParity.remainder piBits (fun _ => 0) m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) :=
  PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER (fun _ => 0) (fun _ => le_refl _) hbound

/-- Existence of a suitable model, with no nonvanishing requirement. -/
theorem PI_NOT_NORMAL_OF_EXISTS_PARITY_MODEL
    (hmodel : ∃ magnitude : ℕ → ℝ, (∀ t, 0 ≤ magnitude t) ∧
      ∃ B : ℝ, ∀ m, |DyadicParity.remainder piBits magnitude m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) := by
  obtain ⟨magnitude, hc, hb⟩ := hmodel
  exact PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER magnitude hc hb

end PiCt.ParityClosure
