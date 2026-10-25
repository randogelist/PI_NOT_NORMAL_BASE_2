import PiCt.AnalyticParityClosure

/-!
An exact digit-only form of the monotone-drift closure.
Bounded drawdown is equivalent to proximity to some nondecreasing sequence.
It is not asserted for the parity sums of pi.
-/

namespace PiCt.Drawdown

open BinaryWords ParityDrift

noncomputable section

/-- Every loss from an earlier value to a later value is bounded by `K`. -/
def BoundedDrawdown (S : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ i j : ℕ, i ≤ j → S i - S j ≤ K

/-- The running maximum, including the value at index zero. -/
def runningMax (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => S 0
  | n + 1 => max (runningMax S n) (S (n + 1))

/-- Current loss below the largest value seen so far. -/
def drawdown (S : ℕ → ℝ) (m : ℕ) : ℝ := runningMax S m - S m

theorem runningMax_monotone (S : ℕ → ℝ) : Monotone (runningMax S) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem self_le_runningMax (S : ℕ → ℝ) (n : ℕ) : S n ≤ runningMax S n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

@[simp] theorem drawdown_zero (S : ℕ → ℝ) : drawdown S 0 = 0 := by
  simp [drawdown, runningMax]

theorem drawdown_nonneg (S : ℕ → ℝ) (n : ℕ) : 0 ≤ drawdown S n := by
  unfold drawdown
  exact sub_nonneg.mpr (self_le_runningMax S n)

theorem le_runningMax (S : ℕ → ℝ) {i n : ℕ} (hin : i ≤ n) :
    S i ≤ runningMax S n :=
  (self_le_runningMax S i).trans (runningMax_monotone S hin)

theorem runningMax_le_of_bound (S : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (h : ∀ i ≤ n, S i ≤ x) : runningMax S n ≤ x := by
  induction n with
  | zero => exact h 0 (le_refl _)
  | succ n ih =>
      apply max_le
      · exact ih (fun i hi => h i (Nat.le_succ_of_le hi))
      · exact h (n + 1) (le_refl _)

/-- A drawdown bound gives the canonical nondecreasing approximation with
one-sided residual in `[-K, 0]`. -/
theorem runningMax_residual_bounds (S : ℕ → ℝ) (K : ℝ)
    (h : ∀ i j : ℕ, i ≤ j → S i - S j ≤ K) (n : ℕ) :
    -K ≤ S n - runningMax S n ∧ S n - runningMax S n ≤ 0 := by
  have htop : runningMax S n ≤ S n + K := by
    apply runningMax_le_of_bound
    intro i hi
    linarith [h i n hi]
  have hself := self_le_runningMax S n
  constructor <;> linarith

/-- The two-index condition is exactly a bound for the single canonical loss. -/
theorem boundedDrawdown_iff_drawdown_bounded (S : ℕ → ℝ) :
    BoundedDrawdown S ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ n, drawdown S n ≤ K := by
  constructor
  · rintro ⟨K, hK, h⟩
    refine ⟨K, hK, ?_⟩
    intro n
    have hlo := (runningMax_residual_bounds S K h n).1
    unfold drawdown
    linarith
  · rintro ⟨K, hK, h⟩
    refine ⟨K, hK, ?_⟩
    intro i j hij
    have hi := le_runningMax S hij
    have hj := h j
    unfold drawdown at hj
    linarith

theorem drawdown_bound_of_monotone_residual
    (S H : ℕ → ℝ) (B : ℝ) (hH : Monotone H)
    (hb : ∀ n, |S n - H n| ≤ B) {i j : ℕ} (hij : i ≤ j) :
    S i - S j ≤ 2 * B := by
  have hi := (abs_le.mp (hb i)).2
  have hj := (abs_le.mp (hb j)).1
  have hm := hH hij
  linarith

/-- No coefficient or specific harmonic drift is needed: this is exactly
the existence of some nondecreasing approximation with bounded error. -/
theorem boundedDrawdown_iff_monotone_approximation (S : ℕ → ℝ) :
    BoundedDrawdown S ↔
      ∃ H : ℕ → ℝ, Monotone H ∧ ∃ B : ℝ, ∀ n, |S n - H n| ≤ B := by
  constructor
  · rintro ⟨K, hK, h⟩
    refine ⟨runningMax S, runningMax_monotone S, K, ?_⟩
    intro n
    obtain ⟨hlo, hhi⟩ := runningMax_residual_bounds S K h n
    exact abs_le.mpr ⟨hlo, hhi.trans hK⟩
  · rintro ⟨H, hH, B, hb⟩
    have hB : 0 ≤ B := (abs_nonneg (S 0 - H 0)).trans (hb 0)
    refine ⟨2 * B, by positivity, ?_⟩
    intro i j hij
    exact drawdown_bound_of_monotone_residual S H B hH hb hij

/-- Binary normality forces losses larger than every real bound. -/
theorem normal_unbounded_drawdowns {b : ℕ → Bool} (hn : BinaryNormal b) (K : ℝ) :
    ∃ i j : ℕ, i ≤ j ∧ K < paritySum b i - paritySum b j := by
  obtain ⟨r, hr⟩ := exists_nat_gt K
  obtain ⟨i, hi⟩ := WordOccurrence.normal_even_alternating hn r
  have hd := paritySum_sub_of_alternating01 hi
  refine ⟨i, i + r, Nat.le_add_right i r, ?_⟩
  linarith

/-- Equivalently, the canonical one-variable loss escapes every bound. -/
theorem normal_unbounded_drawdown {b : ℕ → Bool} (hn : BinaryNormal b) (K : ℝ) :
    ∃ n : ℕ, K < drawdown (paritySum b) n := by
  obtain ⟨i, j, hij, hlt⟩ := normal_unbounded_drawdowns hn K
  refine ⟨j, ?_⟩
  have hi := le_runningMax (paritySum b) hij
  unfold drawdown
  linarith

theorem not_normal_of_bounded_drawdown (b : ℕ → Bool)
    (h : BoundedDrawdown (paritySum b)) : ¬ BinaryNormal b := by
  rintro hn
  obtain ⟨K, _hK, hK⟩ := h
  obtain ⟨i, j, hij, hlt⟩ := normal_unbounded_drawdowns hn K
  exact (not_le_of_gt hlt) (hK i j hij)

/-- The previously proposed analytic remainder bound implies the weaker,
digit-only drawdown condition. The remainder bound remains a premise. -/
theorem boundedDrawdown_of_analytic_residual (b : ℕ → Bool)
    (h : ∃ B : ℝ, ∀ m, |AnalyticParityClosure.analyticResidual b m| ≤ B) :
    BoundedDrawdown (paritySum b) := by
  apply (boundedDrawdown_iff_monotone_approximation _).2
  exact ⟨AnalyticDrift.analyticAccumulated, AnalyticDrift.analyticAccumulated_monotone, h⟩

theorem boundedDrawdown_of_harmonic_residual (b : ℕ → Bool)
    (h : ∃ B : ℝ, ∀ m, |AnalyticParityClosure.harmonicResidual b m| ≤ B) :
    BoundedDrawdown (paritySum b) :=
  boundedDrawdown_of_analytic_residual b
    ((AnalyticParityClosure.bounded_analytic_iff_harmonic b).2 h)

/-- Actual pi closure, conditional on the actual digit drawdown bound. -/
theorem PI_NOT_NORMAL_OF_BOUNDED_DRAWDOWN
    (h : BoundedDrawdown (paritySum piBits)) :
    ¬ BinaryNormal (bit Real.pi) := by
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact not_normal_of_bounded_drawdown piBits h

end

end PiCt.Drawdown
