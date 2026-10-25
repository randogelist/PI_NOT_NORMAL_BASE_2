import PiCt.RunFrequency
import PiCt.ParityDrift

/-!
Canonical dyadic addresses for the actual even/odd digit pairs.
`magnitude` is a nonnegative coefficient family, allowed to vanish.
It is kept separate from the previously frozen signed `Pi.C_T`.
The remainder is defined exactly from actual digits; its boundedness is
an additional proposition, not a consequence of this definition.
-/

namespace PiCt.DyadicParity

open RunFrequency ParityDrift

def plane (j : ℕ) : ℕ := Nat.log2 (2 * j) - 10

def offset (j : ℕ) : ℕ := 2 * j - dyadicLength (plane j)

theorem plane_exponent (j : ℕ) (hj : 512 ≤ j) :
    10 + plane j = Nat.log2 (2 * j) := by
  have hn : 2 * j ≠ 0 := by omega
  have hp : 2 ^ 10 ≤ 2 * j := by norm_num; omega
  have hlog : 10 ≤ Nat.log2 (2 * j) := (Nat.le_log2 hn).2 hp
  unfold plane
  omega

/-- Every pair at or beyond bit 1024 lies in its actual dyadic shell. -/
theorem address (j : ℕ) (hj : 512 ≤ j) :
    2 * j = dyadicLength (plane j) + offset j ∧
      offset j < dyadicLength (plane j) := by
  have hn : 2 * j ≠ 0 := by omega
  have hlo : 2 ^ Nat.log2 (2 * j) ≤ 2 * j :=
    (Nat.le_log2 hn).1 (le_refl _)
  have hhi : 2 * j < 2 ^ (Nat.log2 (2 * j) + 1) :=
    (Nat.log2_lt hn).1 (Nat.lt_succ_self _)
  have hN : dyadicLength (plane j) = 2 ^ Nat.log2 (2 * j) := by
    simp only [dyadicLength, plane_exponent j hj]
  rw [pow_succ] at hhi
  unfold offset
  rw [hN]
  omega

/-- Before the first frozen shell the modeled drift is zero. -/
noncomputable def increment (magnitude : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < 512 then 0 else
    (magnitude (offset j) + magnitude (offset j + 1)) / scale (plane j)

theorem increment_nonneg (magnitude : ℕ → ℝ)
    (hc : ∀ t, 0 ≤ magnitude t) (j : ℕ) : 0 ≤ increment magnitude j := by
  unfold increment
  split_ifs
  · exact le_refl _
  · exact div_nonneg (add_nonneg (hc _) (hc _)) (le_of_lt (scale_pos _))

@[simp] theorem increment_zero (j : ℕ) : increment (fun _ => 0) j = 0 := by
  simp [increment]

noncomputable def accumulated (magnitude : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, increment magnitude j

noncomputable def remainder (b : ℕ → Bool) (magnitude : ℕ → ℝ) (m : ℕ) : ℝ :=
  paritySum b m - accumulated magnitude m

theorem decomposition (b : ℕ → Bool) (magnitude : ℕ → ℝ) (m : ℕ) :
    paritySum b m = accumulated magnitude m + remainder b magnitude m := by
  unfold remainder
  ring

theorem accumulated_monotone (magnitude : ℕ → ℝ)
    (hc : ∀ t, 0 ≤ magnitude t) : Monotone (accumulated magnitude) :=
  partialSums_monotone _ (increment_nonneg magnitude hc)

@[simp] theorem remainder_zero (b : ℕ → Bool) (m : ℕ) :
    remainder b (fun _ => 0) m = paritySum b m := by
  simp [remainder, accumulated]

/-- This supplies the previously frozen analytic coefficient's magnitude.
It does not assert any bound for the actual digit remainder. -/
noncomputable def frozenMagnitude (t : ℕ) : ℝ := |Pi.C_T t|

theorem frozenMagnitude_nonneg (t : ℕ) : 0 ≤ frozenMagnitude t := abs_nonneg _

theorem frozenMagnitude_value (t : ℕ) : frozenMagnitude t = 1 / 4 := by
  unfold frozenMagnitude
  rw [PI_CT_EQ_FROZEN, C_abs]

end PiCt.DyadicParity
