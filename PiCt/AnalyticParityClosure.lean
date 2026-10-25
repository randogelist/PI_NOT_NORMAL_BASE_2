import PiCt.AnalyticDrift
import PiCt.ParityClosure
import PiCt.ParityCounts

/-!
The actual even/odd digit remainder against the exact analytic drift.
The uniformly summable analytic approximation is proved; the actual-digit
bound remains an explicit hypothesis in every pi nonnormality endpoint.
-/

namespace PiCt.AnalyticParityClosure

open BinaryWords ParityDrift AnalyticDrift ParityCounts

/-- The exact positive drift is read from the same analytic pi representative. -/
theorem analyticStep_eq_internal_readout (j : ℕ) (hj : 512 ≤ j) :
    analyticStep j = Pi.split (2 * (j : ℝ)) + Pi.split (2 * (j : ℝ) + 1) - 1 := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  rw [PI_INTERNAL_LOG_READOUT (by positivity : 0 < 2 * (j : ℝ)),
    PI_INTERNAL_LOG_READOUT (by positivity : 0 < 2 * (j : ℝ) + 1)]
  simp only [analyticStep, if_neg (show ¬j < 512 by omega)]
  ring

/-- The frozen coefficient is divided by the actual address, not just the shell scale. -/
theorem harmonicStep_eq_frozen (j : ℕ) (hj : 512 ≤ j) :
    harmonicStep j =
      DyadicParity.frozenMagnitude (DyadicParity.offset j) / (2 * (j : ℝ)) +
      DyadicParity.frozenMagnitude (DyadicParity.offset j + 1) / (2 * (j : ℝ) + 1) := by
  simp only [harmonicStep, if_neg (show ¬j < 512 by omega),
    DyadicParity.frozenMagnitude_value]
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  field_simp [ne_of_gt hjp, ne_of_gt (show 0 < 2 * (j : ℝ) + 1 by positivity)]

noncomputable def analyticResidual (b : ℕ → Bool) (m : ℕ) : ℝ :=
  paritySum b m - analyticAccumulated m

noncomputable def harmonicResidual (b : ℕ → Bool) (m : ℕ) : ℝ :=
  paritySum b m - harmonicAccumulated m

theorem residual_difference (b : ℕ → Bool) (m : ℕ) :
    analyticResidual b m - harmonicResidual b m =
      harmonicAccumulated m - analyticAccumulated m := by
  unfold analyticResidual harmonicResidual
  ring

theorem residual_difference_bound (b : ℕ → Bool) (m : ℕ) :
    |analyticResidual b m - harmonicResidual b m| ≤ 1 / 2048 := by
  rw [residual_difference, abs_of_nonneg (drift_error m).1]
  exact (drift_error m).2

/-- A proved equivalence of the two unresolved actual-digit bounds. -/
theorem bounded_analytic_iff_harmonic (b : ℕ → Bool) :
    (∃ B : ℝ, ∀ m, |analyticResidual b m| ≤ B) ↔
      (∃ B : ℝ, ∀ m, |harmonicResidual b m| ≤ B) := by
  constructor
  · rintro ⟨B, hb⟩
    refine ⟨B + 1 / 2048, ?_⟩
    intro m
    have he := drift_error m
    have hv := abs_le.mp (hb m)
    apply abs_le.mpr
    unfold analyticResidual harmonicResidual at *
    constructor <;> linarith
  · rintro ⟨B, hb⟩
    refine ⟨B + 1 / 2048, ?_⟩
    intro m
    have he := drift_error m
    have hv := abs_le.mp (hb m)
    apply abs_le.mpr
    unfold analyticResidual harmonicResidual at *
    constructor <;> linarith

theorem not_normal_of_analytic_residual (b : ℕ → Bool)
    (hbound : ∃ B : ℝ, ∀ m, |analyticResidual b m| ≤ B) :
    ¬ BinaryNormal b := by
  obtain ⟨B, hb⟩ := hbound
  apply ParityClosure.not_normal_of_monotone_drift b analyticAccumulated
    (analyticResidual b) B analyticAccumulated_monotone
  · intro m
    unfold analyticResidual
    ring
  · exact hb

theorem PI_NOT_NORMAL_OF_ANALYTIC_PARITY_REMAINDER
    (hbound : ∃ B : ℝ, ∀ m, |analyticResidual piBits m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) := by
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact not_normal_of_analytic_residual piBits hbound

theorem PI_NOT_NORMAL_OF_HARMONIC_PARITY_REMAINDER
    (hbound : ∃ B : ℝ, ∀ m, |harmonicResidual piBits m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) :=
  PI_NOT_NORMAL_OF_ANALYTIC_PARITY_REMAINDER
    ((bounded_analytic_iff_harmonic piBits).2 hbound)

/-- The remaining estimate is explicitly a statement about actual 10/01 counts. -/
theorem PI_NOT_NORMAL_OF_HARMONIC_PAIR_COUNT_BOUND
    (hbound : ∃ B : ℝ, ∀ m,
      |count10 piBits m - count01 piBits m - harmonicAccumulated m| ≤ B) :
    ¬ BinaryNormal (bit Real.pi) := by
  apply PI_NOT_NORMAL_OF_HARMONIC_PARITY_REMAINDER
  obtain ⟨B, hb⟩ := hbound
  refine ⟨B, ?_⟩
  intro m
  simpa only [harmonicResidual, paritySum_eq_count_difference] using hb m

/-- Digit quantization forbids transferring the analytic second-order error
pointwise to the actual pair difference. Cumulative cancellation is needed. -/
theorem harmonic_pointwise_gap (b : ℕ → Bool) (j : ℕ) (hj : 512 ≤ j) :
    1 / (8 * (j : ℝ)) ≤ |pairDifference b j - harmonicStep j| := by
  have hj1 : 1 ≤ (j : ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
  have hp : 0 < harmonicStep j := by
    simp only [harmonicStep, if_neg (show ¬j < 512 by omega)]
    positivity
  have hhalf : harmonicStep j ≤ 1 / 2 := by
    have h0 : 1 / (4 * (2 * (j : ℝ))) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h1 : 1 / (4 * (2 * (j : ℝ) + 1)) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    simp only [harmonicStep, if_neg (show ¬j < 512 by omega)]
    linarith
  have hlo : 1 / (8 * (j : ℝ)) ≤ harmonicStep j := by
    simp only [harmonicStep, if_neg (show ¬j < 512 by omega)]
    have h0 : 0 ≤ 1 / (4 * (2 * (j : ℝ) + 1)) := by positivity
    have he : 1 / (8 * (j : ℝ)) = 1 / (4 * (2 * (j : ℝ))) := by ring
    linarith
  exact hlo.trans (pair_error_ge_step b j hp hhalf)

end PiCt.AnalyticParityClosure
