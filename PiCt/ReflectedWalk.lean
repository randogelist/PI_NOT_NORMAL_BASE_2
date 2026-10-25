import PiCt.Drawdown
import PiCt.FloorDigits

/-!
A natural-number counter computed directly from actual digit pairs.
Its boundedness is equivalent to bounded drawdown, not assumed automatically.
-/

namespace PiCt.ReflectedWalk

open BinaryWords ParityDrift Drawdown

/-- `01` increases the counter, `10` decreases it toward zero, and equal
digits leave it unchanged. This definition is executable for executable bits. -/
def counter (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if b (2 * m) then
      if b (2 * m + 1) then counter b m else counter b m - 1
    else
      if b (2 * m + 1) then counter b m + 1 else counter b m

theorem counter_succ_real (b : ℕ → Bool) (m : ℕ) :
    (counter b (m + 1) : ℝ) = max 0 ((counter b m : ℝ) - pairDifference b m) := by
  cases h0 : b (2 * m) <;> cases h1 : b (2 * m + 1) <;>
    cases hc : counter b m <;>
    simp [counter, h0, h1, hc, pairDifference, digit, Nat.cast_add] <;>
    positivity

theorem paritySum_succ (b : ℕ → Bool) (m : ℕ) :
    paritySum b (m + 1) = paritySum b m + pairDifference b m := by
  simp only [paritySum, Finset.sum_range_succ]

theorem drawdown_succ (b : ℕ → Bool) (m : ℕ) :
    drawdown (paritySum b) (m + 1) =
      max 0 (drawdown (paritySum b) m - pairDifference b m) := by
  simp only [drawdown, runningMax, paritySum_succ]
  rw [← max_sub_sub_right]
  have he : runningMax (paritySum b) m - (paritySum b m + pairDifference b m) =
      runningMax (paritySum b) m - paritySum b m - pairDifference b m := by ring
  rw [he, sub_self, max_comm]

/-- The executable counter is exactly the loss from the running maximum. -/
theorem counter_eq_drawdown (b : ℕ → Bool) (m : ℕ) :
    (counter b m : ℝ) = drawdown (paritySum b) m := by
  induction m with
  | zero => simp [counter]
  | succ m ih => rw [counter_succ_real, drawdown_succ, ih]

/-- The counter is instantiated using the floors of the actual pi anchor. -/
theorem PI_COUNTER_FLOOR_IDENTITY (m : ℕ) :
    (counter piBits m : ℝ) = drawdown (FloorDigits.floorParity Real.pi) m := by
  rw [counter_eq_drawdown]
  have he : paritySum piBits = FloorDigits.floorParity Real.pi :=
    funext FloorDigits.PI_PARITY_FLOOR_IDENTITY
  rw [he]

/-- The natural-number barrier is exactly the real drawdown criterion. -/
theorem bounded_counter_iff (b : ℕ → Bool) :
    (∃ K : ℕ, ∀ m, counter b m ≤ K) ↔ BoundedDrawdown (paritySum b) := by
  rw [boundedDrawdown_iff_drawdown_bounded]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨(K : ℝ), Nat.cast_nonneg K, ?_⟩
    intro m
    rw [← counter_eq_drawdown]
    exact_mod_cast hK m
  · rintro ⟨K, _hK0, hK⟩
    obtain ⟨n, hn⟩ := exists_nat_ge K
    refine ⟨n, ?_⟩
    intro m
    have h := (hK m).trans hn
    rw [← counter_eq_drawdown] at h
    exact_mod_cast h

/-- An inductive barrier only needs to forbid `01` when the counter is full.
This remains a quantified condition on the actual infinite digit sequence. -/
theorem bounded_counter_iff_boundary (b : ℕ → Bool) (K : ℕ) :
    (∀ m, counter b m ≤ K) ↔
      ∀ m, counter b m = K → ¬ (b (2 * m) = false ∧ b (2 * m + 1) = true) := by
  constructor
  · intro hb m hm hp
    have hs := hb (m + 1)
    simp only [counter, hp.1, hp.2, Bool.false_eq_true, if_false, if_true] at hs
    omega
  · intro hboundary m
    induction m with
    | zero => simp [counter]
    | succ m ih =>
        cases h0 : b (2 * m) <;> cases h1 : b (2 * m + 1)
        · simpa [counter, h0, h1] using ih
        · have hn : counter b m ≠ K := by
            intro heq
            exact hboundary m heq ⟨h0, h1⟩
          simp only [counter, h0, h1, Bool.false_eq_true, if_false, if_true]
          omega
        · simp only [counter, h0, h1, Bool.false_eq_true, if_false, if_true]
          omega
        · simpa [counter, h0, h1] using ih

theorem not_normal_of_bounded_counter (b : ℕ → Bool)
    (hb : ∃ K : ℕ, ∀ m, counter b m ≤ K) : ¬ BinaryNormal b :=
  not_normal_of_bounded_drawdown b ((bounded_counter_iff b).1 hb)

theorem PI_NOT_NORMAL_OF_COUNTER_BARRIER
    (hb : ∃ K : ℕ, ∀ m, counter piBits m ≤ K) :
    ¬ BinaryNormal (bit Real.pi) :=
  PI_NOT_NORMAL_OF_BOUNDED_DRAWDOWN ((bounded_counter_iff piBits).1 hb)

theorem PI_NOT_NORMAL_OF_BOUNDARY_INVARIANT
    (hb : ∃ K : ℕ, ∀ m, counter piBits m = K →
      ¬ (piBits (2 * m) = false ∧ piBits (2 * m + 1) = true)) :
    ¬ BinaryNormal (bit Real.pi) := by
  obtain ⟨K, hK⟩ := hb
  exact PI_NOT_NORMAL_OF_COUNTER_BARRIER ⟨K, (bounded_counter_iff_boundary piBits K).2 hK⟩

end PiCt.ReflectedWalk
