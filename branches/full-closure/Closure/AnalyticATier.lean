import PartA.CtAnalyticLimit
import Closure.FiniteParityFrontier

/-!
Source-only assembly of the full analytic Part A with the existing
conditional pi closure. No actual-pi tracking witness is asserted here.
-/

namespace ANCHOPI.Closure

open AWPIWordAnchor
open ANCHOPI.PartA
open ANCHOPI.PartB
open ANCHOPI.ActualPi
open ANCHOPI.Frontier

/-- The coefficient now has its logarithmic derivation in the Lean sources. -/
theorem PART_A_CT_ANALYTIC_DERIVATION :
    (∀ N : ℝ, 0 < N → pairMean N - 1 / 2 = criticalDefect N) ∧
    (∀ N : ℝ, 0 < N → 0 < criticalDefect N) ∧
    (∀ N : ℝ, 0 < N →
      0 ≤ (1 : ℝ) / 4 - scaledDefect N ∧
      (1 : ℝ) / 4 - scaledDefect N ≤ 1 / (N + 1)) ∧
    (∀ Q : ℕ, UniformTailLimit Q analyticRescaled limitingCt) ∧
    (∀ t : ℕ, limitingCt t ≠ 0) ∧
    (∀ k : ℕ, 0 < limitingCt (2 * k)) ∧
    (∀ k : ℕ, limitingCt (2 * k + 1) < 0) := by
  exact ⟨pairMean_sub_half, criticalDefect_pos, scaledDefect_error,
    analytic_scaled_uniform_limit, limitingCt_ne_zero,
    limitingCt_even_pos, limitingCt_odd_neg⟩

/-- Complete analytic reduction, with the actual digit premise explicit. -/
theorem ACTUAL_PI_ANALYTIC_A_TIER_ATLAS :
    (∀ Q : ℕ, UniformTailLimit Q analyticRescaled limitingCt) ∧
    (ActualPiAnalyticTracking ↔ ActualPiCtTracking) ∧
    (ActualPiCtTracking ↔ FiniteParitySeparation actualPiDigits) ∧
    (ActualPiAnalyticTracking → ¬ normal actualPiDigits) := by
  exact ⟨analytic_scaled_uniform_limit,
    actualPiAnalyticTracking_iff_ctTracking,
    actualPiCtTracking_iff_finiteParitySeparation,
    ACTUAL_PI_ANALYTIC_TRACKING_CLOSURE⟩

end ANCHOPI.Closure
