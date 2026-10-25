import Closure.AnalyticATier

/-!
Full project closure: canonical pi readout, analytic coefficient derivation,
uniform analytic limit, semantic-frontier equivalences, and nonnormality.
The analytic theorems are proved without a research premise. The final
nonnormality implication retains ActualPiAnalyticTracking explicitly.
-/

namespace ANCHOPI.Closure

open AWPIWordAnchor
open ANCHOPI.PartA
open ANCHOPI.PartB
open ANCHOPI.ActualPi
open ANCHOPI.Frontier

/-- Full actual-pi endpoint through the derived analytic family. -/
theorem ACTUAL_PI_FULL_A_TIER_CLOSURE :
    ActualPiAnalyticTracking → ¬ normal actualPiDigits :=
  ACTUAL_PI_ANALYTIC_TRACKING_CLOSURE

/-- The same endpoint through the coefficient-tracking interface. -/
theorem ACTUAL_PI_FULL_CLOSURE_OF_CT_TRACKING :
    ActualPiCtTracking → ¬ normal actualPiDigits :=
  ACTUAL_PI_CT_A_TIER_CLOSURE

/-- A data witness can be consumed directly without a separate existence step. -/
theorem ACTUAL_PI_FULL_CLOSURE_OF_BINDING
    (h : ActualPiCtBinding actualPiDigits) : ¬ normal actualPiDigits :=
  actual_pi_nonnormal_of_binding h

/-- All four formulations refer to the same explicit actual-digit premise. -/
theorem ACTUAL_PI_FULL_FRONTIER_EQUIVALENCES :
    (ActualPiAnalyticTracking ↔ ActualPiCtTracking) ∧
    (ActualPiCtTracking ↔ Nonempty (ActualPiCtBinding actualPiDigits)) ∧
    (ActualPiCtTracking ↔ FiniteParitySeparation actualPiDigits) ∧
    (ActualPiCtTracking ↔ OneScaleCtApproximation actualPiDigits) := by
  exact ⟨actualPiAnalyticTracking_iff_ctTracking,
    actualPiCtTracking_iff_binding,
    actualPiCtTracking_iff_finiteParitySeparation,
    actualPiCtTracking_iff_oneScaleCtApproximation⟩

/--
The complete theorem atlas, including the literal pi readout and the full
analytic estimates. Its final clause is an implication, not an assertion
that the actual-digit tracking premise has been proved.
-/
theorem ACTUAL_PI_FULL_A_TIER_ATLAS :
    (∀ n : ℕ, actualPiDigits n =
      decide ((Int.floor (((2 : ℝ) ^ (n + 1)) * Real.pi)) % 2 = 1)) ∧
    (∀ N : ℝ, 0 < N → pairMean N - 1 / 2 = criticalDefect N) ∧
    (∀ N : ℝ, 0 < N → 0 < criticalDefect N) ∧
    (∀ N : ℝ, 0 < N →
      0 ≤ (1 : ℝ) / 4 - scaledDefect N ∧
      (1 : ℝ) / 4 - scaledDefect N ≤ 1 / (N + 1)) ∧
    (∀ a t : ℕ, |analyticRescaled a t - limitingCt t| ≤
      1 / ((shellDepth a : ℝ) + 1)) ∧
    (∀ Q : ℕ, UniformTailLimit Q analyticRescaled limitingCt) ∧
    (∀ t : ℕ, limitingCt t ≠ 0) ∧
    (∀ k : ℕ, 0 < limitingCt (2 * k)) ∧
    (∀ k : ℕ, limitingCt (2 * k + 1) < 0) ∧
    (ActualPiAnalyticTracking ↔ ActualPiCtTracking) ∧
    (ActualPiAnalyticTracking → ¬ normal actualPiDigits) := by
  exact ⟨actualPiDigits_spec, pairMean_sub_half, criticalDefect_pos,
    scaledDefect_error, analyticRescaled_error_shell,
    analytic_scaled_uniform_limit, limitingCt_ne_zero,
    limitingCt_even_pos, limitingCt_odd_neg,
    actualPiAnalyticTracking_iff_ctTracking, ACTUAL_PI_FULL_A_TIER_CLOSURE⟩

end ANCHOPI.Closure
