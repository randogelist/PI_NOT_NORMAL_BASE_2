import PartB.SignAnchor

namespace ANCHOPI.PartA

open ANCHOPI.PartB

/-- The limiting signed coefficient from the analytic G1 branch. -/
noncomputable def limitingCt (t : ℕ) : ℝ := paritySign t / 4

theorem limitingCt_ne_zero (t : ℕ) : limitingCt t ≠ 0 := by
  unfold limitingCt
  rcases paritySign_cases t with h | h <;> rw [h] <;> norm_num

theorem limitingCt_even_pos (k : ℕ) : 0 < limitingCt (2 * k) := by
  unfold limitingCt
  have hdouble : paritySign (k + k) = 1 := paritySign_double k
  have hidx : 2 * k = k + k := by omega
  rw [hidx, hdouble]
  norm_num

theorem limitingCt_odd_neg (k : ℕ) : limitingCt (2 * k + 1) < 0 := by
  unfold limitingCt
  have hdouble : paritySign (k + k) = 1 := paritySign_double k
  have hidx : 2 * k + 1 = (k + k) + 1 := by omega
  rw [hidx]
  simp only [paritySign]
  rw [hdouble]
  norm_num

theorem limitingCt_strictParity : StrictParity 0 0 limitingCt := by
  intro t _ht
  unfold limitingCt
  simp only [Nat.zero_add]
  rcases paritySign_cases t with h | h <;> rw [h] <;> norm_num

end ANCHOPI.PartA
