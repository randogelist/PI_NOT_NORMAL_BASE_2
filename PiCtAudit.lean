import PiCt.CoefficientAccumulation
import PiCt.AnalyticWordProduct
import PiCt.AlternatingFrequency
import PiCt.AlternatingExcursions
import PiCt.AlternatingTailClosure
import PiCt.FloorDigits
import PiCt.Drawdown
import PiCt.ReflectedWalk
import PiCt.OrbitPotential
import PiCt.Usage
import PiCt.RunClosure
import PiCt.ParityClosure
import PiCt.MovingOffset
import PiCt.AnalyticParityClosure

#check PiCt.ComplexRepresentative.primitive_one
#check PiCt.ComplexRepresentative.primitive_hasSum
#check PiCt.ComplexRepresentative.primitive_log_difference
#check PiCt.ComplexRepresentative.primitive_ray_im
#check PiCt.ComplexRepresentative.splitReadout_eq_half_add_delta
#check PiCt.delta_bounds
#check PiCt.scaled_bounds
#check PiCt.scale_succ
#check PiCt.C_tendsto
#check PiCt.C_exists_unique
#check PiCt.C_ne_zero
#check PiCt.G_remainder
#check PiCt.coefficient_cauchy
#check PiCt.PI_REPRESENTATIVE_CT
#check PiCt.PI_REPRESENTATIVE_CT_UNIQUE
#check PiCt.PI_REPRESENTATIVE_REMAINDER
#check PiCt.PI_REPRESENTATIVE_CAUCHY
#check PiCt.PI_REPRESENTATIVE_UNSCALED_LIMIT

#print axioms PiCt.ComplexRepresentative.primitive_one
#print axioms PiCt.ComplexRepresentative.primitive_hasSum
#print axioms PiCt.ComplexRepresentative.primitive_ray_im
#print axioms PiCt.ComplexRepresentative.splitReadout_eq_half_add_delta
#print axioms PiCt.delta_bounds
#print axioms PiCt.scaled_bounds
#print axioms PiCt.C_tendsto
#print axioms PiCt.C_exists_unique
#print axioms PiCt.G_remainder
#print axioms PiCt.coefficient_cauchy
#print axioms PiCt.PI_REPRESENTATIVE_CT
#print axioms PiCt.PI_REPRESENTATIVE_CT_UNIQUE
#print axioms PiCt.PI_REPRESENTATIVE_REMAINDER
#print axioms PiCt.PI_REPRESENTATIVE_CAUCHY
#print axioms PiCt.PI_REPRESENTATIVE_UNSCALED_LIMIT

#check PiCt.Pi
#check PiCt.PI_ANCHOR
#check PiCt.PI_POWER_SERIES
#check PiCt.PI_INTERNAL_LOG_READOUT
#check PiCt.Pi.coefficient
#check PiCt.Pi.C_T
#check PiCt.PI_CT_INSTANTIATED
#check PiCt.PI_CT_VALUE
#check PiCt.PI_CT_EQ_FROZEN
#check PiCt.PI_CT_NE_ZERO
#check PiCt.PI_CT_REMAINDER
#check PiCt.PI_CT_CAUCHY
#check PiCt.PI_CT_UNIQUE
#check PiCt.PI_COEFFICIENT_VALUE
#check PiCt.PI_CT_UNSCALED_LIMIT

#print axioms PiCt.PI_ANCHOR
#print axioms PiCt.piHasDyadicCoefficients
#print axioms PiCt.PI_CT_INSTANTIATED
#print axioms PiCt.PI_CT_VALUE
#print axioms PiCt.PI_CT_EQ_FROZEN
#print axioms PiCt.PI_CT_REMAINDER
#print axioms PiCt.PI_CT_CAUCHY
#print axioms PiCt.PI_CT_UNIQUE
#print axioms PiCt.PI_COEFFICIENT_VALUE

-- Actual digit definitions and exact finite word-frequency identities.
#check PiCt.BinaryWords.bit
#check PiCt.BinaryWords.piBits_eq
#check PiCt.BinaryWords.blockCode4_zero_iff
#check PiCt.BinaryWords.blockCode4_fifteen_iff
#check PiCt.BinaryWords.root_freq
#check PiCt.BinaryWords.split_freq
#check PiCt.BinaryWords.BinaryNormal
#check PiCt.RunFrequency.zeroRun_identity
#check PiCt.RunFrequency.oneRun_identity
#check PiCt.RunFrequency.runDefect_identity
#check PiCt.RunFrequency.pair_frequency_identity
#check PiCt.RunFrequency.dyadicLength_cast
#check PiCt.RunFrequency.normal_extremeWordsBalanced
#check PiCt.RunFrequency.balanced_dyadicDefect_zero
#check PiCt.RunFrequency.not_normal_of_persistent_defect

-- The bridge is a proposition, not an established theorem or an axiom.
#check PiCt.RunClosure.CtRunBridge
#check PiCt.RunClosure.PI_RUN_DEFECT_OF_CT_BRIDGE
#check PiCt.RunClosure.PI_EXTREME_WORD_FAILURE_OF_CT_BRIDGE
#check PiCt.RunClosure.REAL_PI_NOT_NORMAL_OF_CT_RUN_BRIDGE
#check PiCt.RunClosure.PI_PAIR_FREQUENCY_OF_CT_BRIDGE
#check PiCt.RunClosure.PI_PAIR_LIMIT_FIVE_THIRTYTWO_OF_BRIDGE
#check PiCt.RunClosure.PI_NOT_NORMAL_OF_PERSISTENT_RUN_DEFECT
#check PiCt.RunClosure.PI_BRIDGE_RESIDUAL_UNDER_NORMALITY

-- The analytic ratio and its frozen coefficient are unchanged by nonzero scaling.
#check PiCt.ReadoutInvariant.scaledPrimitive_anchor
#check PiCt.ReadoutInvariant.rawSplit_scaledPrimitive
#check PiCt.ReadoutInvariant.scaledPrimitive_frozen_limit

#print axioms PiCt.BinaryWords.piBits_eq
#print axioms PiCt.BinaryWords.blockCode4_zero_iff
#print axioms PiCt.BinaryWords.blockCode4_fifteen_iff
#print axioms PiCt.BinaryWords.split_freq
#print axioms PiCt.RunFrequency.zeroRun_identity
#print axioms PiCt.RunFrequency.oneRun_identity
#print axioms PiCt.RunFrequency.runDefect_identity
#print axioms PiCt.RunFrequency.not_normal_of_persistent_defect
#print axioms PiCt.RunClosure.PI_RUN_DEFECT_OF_CT_BRIDGE
#print axioms PiCt.RunClosure.PI_EXTREME_WORD_FAILURE_OF_CT_BRIDGE
#print axioms PiCt.RunClosure.REAL_PI_NOT_NORMAL_OF_CT_RUN_BRIDGE
#print axioms PiCt.RunClosure.PI_PAIR_LIMIT_FIVE_THIRTYTWO_OF_BRIDGE
#print axioms PiCt.RunClosure.PI_NOT_NORMAL_OF_PERSISTENT_RUN_DEFECT
#print axioms PiCt.RunClosure.PI_BRIDGE_RESIDUAL_UNDER_NORMALITY
#print axioms PiCt.ReadoutInvariant.scaledPrimitive_anchor
#print axioms PiCt.ReadoutInvariant.scaledPrimitive_frozen_limit

-- Original parity-drift architecture: zero coefficient magnitudes are allowed.
#check PiCt.ParityDrift.paritySum
#check PiCt.ParityDrift.paritySum_sub_of_alternating01
#check PiCt.ParityDrift.alternating01_bound_of_monotone
#check PiCt.ParityDrift.alternating01_bound_of_increments
#check PiCt.WordOccurrence.normal_word_occurs
#check PiCt.WordOccurrence.normal_even_alternating
#check PiCt.DyadicParity.address
#check PiCt.DyadicParity.increment_nonneg
#check PiCt.DyadicParity.increment_zero
#check PiCt.DyadicParity.decomposition
#check PiCt.DyadicParity.remainder_zero
#check PiCt.DyadicParity.frozenMagnitude_value
#check PiCt.ParityClosure.not_normal_of_monotone_drift
#check PiCt.ParityClosure.not_normal_of_bounded_parity_sum
#check PiCt.ParityClosure.PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER
#check PiCt.ParityClosure.PI_NOT_NORMAL_OF_TAIL_PARITY_REMAINDER
#check PiCt.ParityClosure.PI_NOT_NORMAL_OF_FROZEN_PARITY_REMAINDER
#check PiCt.ParityClosure.PI_NOT_NORMAL_OF_ZERO_COEFFICIENT_REMAINDER
#check PiCt.ParityClosure.PI_NOT_NORMAL_OF_EXISTS_PARITY_MODEL

#print axioms PiCt.ParityDrift.paritySum_sub_of_alternating01
#print axioms PiCt.ParityDrift.alternating01_bound_of_monotone
#print axioms PiCt.WordOccurrence.normal_word_occurs
#print axioms PiCt.WordOccurrence.normal_even_alternating
#print axioms PiCt.DyadicParity.address
#print axioms PiCt.DyadicParity.decomposition
#print axioms PiCt.DyadicParity.frozenMagnitude_value
#print axioms PiCt.ParityClosure.not_normal_of_monotone_drift
#print axioms PiCt.ParityClosure.not_normal_of_bounded_parity_sum
#print axioms PiCt.ParityClosure.PI_NOT_NORMAL_OF_NONNEGATIVE_COEFFICIENT_REMAINDER
#print axioms PiCt.ParityClosure.PI_NOT_NORMAL_OF_TAIL_PARITY_REMAINDER
#print axioms PiCt.ParityClosure.PI_NOT_NORMAL_OF_FROZEN_PARITY_REMAINDER
#print axioms PiCt.ParityClosure.PI_NOT_NORMAL_OF_ZERO_COEFFICIENT_REMAINDER
#print axioms PiCt.ParityClosure.PI_NOT_NORMAL_OF_EXISTS_PARITY_MODEL

-- Uniform analytic control uses the actual position inside each growing shell.
#check PiCt.MovingOffset.profile_bounds
#check PiCt.MovingOffset.relative_offset_limit
#check PiCt.MovingOffset.half_shell_limit
#check PiCt.AnalyticDrift.delta_harmonic_error
#check PiCt.AnalyticDrift.analyticAccumulated_monotone
#check PiCt.AnalyticDrift.drift_error_tight
#check PiCt.AnalyticDrift.drift_error
#check PiCt.ParityCounts.paritySum_eq_count_difference
#check PiCt.ParityCounts.pairDifference_values
#check PiCt.ParityCounts.pair_error_ge_step
#check PiCt.AnalyticParityClosure.analyticStep_eq_internal_readout
#check PiCt.AnalyticParityClosure.harmonicStep_eq_frozen
#check PiCt.AnalyticParityClosure.residual_difference_bound
#check PiCt.AnalyticParityClosure.bounded_analytic_iff_harmonic
#check PiCt.AnalyticParityClosure.harmonic_pointwise_gap
#check PiCt.AnalyticParityClosure.PI_NOT_NORMAL_OF_ANALYTIC_PARITY_REMAINDER
#check PiCt.AnalyticParityClosure.PI_NOT_NORMAL_OF_HARMONIC_PARITY_REMAINDER
#check PiCt.AnalyticParityClosure.PI_NOT_NORMAL_OF_HARMONIC_PAIR_COUNT_BOUND

#print axioms PiCt.MovingOffset.profile_bounds
#print axioms PiCt.MovingOffset.relative_offset_limit
#print axioms PiCt.MovingOffset.half_shell_limit
#print axioms PiCt.AnalyticDrift.delta_harmonic_error
#print axioms PiCt.AnalyticDrift.analyticAccumulated_monotone
#print axioms PiCt.AnalyticDrift.drift_error_tight
#print axioms PiCt.AnalyticDrift.drift_error
#print axioms PiCt.ParityCounts.paritySum_eq_count_difference
#print axioms PiCt.ParityCounts.pair_error_ge_step
#print axioms PiCt.AnalyticParityClosure.analyticStep_eq_internal_readout
#print axioms PiCt.AnalyticParityClosure.harmonicStep_eq_frozen
#print axioms PiCt.AnalyticParityClosure.residual_difference_bound
#print axioms PiCt.AnalyticParityClosure.bounded_analytic_iff_harmonic
#print axioms PiCt.AnalyticParityClosure.harmonic_pointwise_gap
#print axioms PiCt.AnalyticParityClosure.PI_NOT_NORMAL_OF_ANALYTIC_PARITY_REMAINDER
#print axioms PiCt.AnalyticParityClosure.PI_NOT_NORMAL_OF_HARMONIC_PARITY_REMAINDER
#print axioms PiCt.AnalyticParityClosure.PI_NOT_NORMAL_OF_HARMONIC_PAIR_COUNT_BOUND

-- Version 0.6.0: exact actual-digit formulas and conditional counter closure.

#check PiCt.FloorDigits.floor_double
#print axioms PiCt.FloorDigits.floor_double
#check PiCt.FloorDigits.digit_eq_floor_difference
#print axioms PiCt.FloorDigits.digit_eq_floor_difference
#check PiCt.FloorDigits.pairDifference_eq_floors
#print axioms PiCt.FloorDigits.pairDifference_eq_floors
#check PiCt.FloorDigits.paritySum_eq_floorParity
#print axioms PiCt.FloorDigits.paritySum_eq_floorParity
#check PiCt.FloorDigits.PI_PARITY_FROM_ANALYTIC_ANCHOR
#print axioms PiCt.FloorDigits.PI_PARITY_FROM_ANALYTIC_ANCHOR
#check PiCt.FloorDigits.PI_PARITY_FLOOR_IDENTITY
#print axioms PiCt.FloorDigits.PI_PARITY_FLOOR_IDENTITY
#check PiCt.FloorDigits.floor_of_enclosure
#print axioms PiCt.FloorDigits.floor_of_enclosure

#check PiCt.Drawdown.runningMax_monotone
#print axioms PiCt.Drawdown.runningMax_monotone
#check PiCt.Drawdown.self_le_runningMax
#print axioms PiCt.Drawdown.self_le_runningMax
#check PiCt.Drawdown.drawdown_zero
#print axioms PiCt.Drawdown.drawdown_zero
#check PiCt.Drawdown.drawdown_nonneg
#print axioms PiCt.Drawdown.drawdown_nonneg
#check PiCt.Drawdown.le_runningMax
#print axioms PiCt.Drawdown.le_runningMax
#check PiCt.Drawdown.runningMax_le_of_bound
#print axioms PiCt.Drawdown.runningMax_le_of_bound
#check PiCt.Drawdown.runningMax_residual_bounds
#print axioms PiCt.Drawdown.runningMax_residual_bounds
#check PiCt.Drawdown.boundedDrawdown_iff_drawdown_bounded
#print axioms PiCt.Drawdown.boundedDrawdown_iff_drawdown_bounded
#check PiCt.Drawdown.drawdown_bound_of_monotone_residual
#print axioms PiCt.Drawdown.drawdown_bound_of_monotone_residual
#check PiCt.Drawdown.boundedDrawdown_iff_monotone_approximation
#print axioms PiCt.Drawdown.boundedDrawdown_iff_monotone_approximation
#check PiCt.Drawdown.normal_unbounded_drawdowns
#print axioms PiCt.Drawdown.normal_unbounded_drawdowns
#check PiCt.Drawdown.normal_unbounded_drawdown
#print axioms PiCt.Drawdown.normal_unbounded_drawdown
#check PiCt.Drawdown.not_normal_of_bounded_drawdown
#print axioms PiCt.Drawdown.not_normal_of_bounded_drawdown
#check PiCt.Drawdown.boundedDrawdown_of_analytic_residual
#print axioms PiCt.Drawdown.boundedDrawdown_of_analytic_residual
#check PiCt.Drawdown.boundedDrawdown_of_harmonic_residual
#print axioms PiCt.Drawdown.boundedDrawdown_of_harmonic_residual
#check PiCt.Drawdown.PI_NOT_NORMAL_OF_BOUNDED_DRAWDOWN
#print axioms PiCt.Drawdown.PI_NOT_NORMAL_OF_BOUNDED_DRAWDOWN

#check PiCt.ReflectedWalk.counter_succ_real
#print axioms PiCt.ReflectedWalk.counter_succ_real
#check PiCt.ReflectedWalk.paritySum_succ
#print axioms PiCt.ReflectedWalk.paritySum_succ
#check PiCt.ReflectedWalk.drawdown_succ
#print axioms PiCt.ReflectedWalk.drawdown_succ
#check PiCt.ReflectedWalk.counter_eq_drawdown
#print axioms PiCt.ReflectedWalk.counter_eq_drawdown
#check PiCt.ReflectedWalk.PI_COUNTER_FLOOR_IDENTITY
#print axioms PiCt.ReflectedWalk.PI_COUNTER_FLOOR_IDENTITY
#check PiCt.ReflectedWalk.bounded_counter_iff
#print axioms PiCt.ReflectedWalk.bounded_counter_iff
#check PiCt.ReflectedWalk.bounded_counter_iff_boundary
#print axioms PiCt.ReflectedWalk.bounded_counter_iff_boundary
#check PiCt.ReflectedWalk.not_normal_of_bounded_counter
#print axioms PiCt.ReflectedWalk.not_normal_of_bounded_counter
#check PiCt.ReflectedWalk.PI_NOT_NORMAL_OF_COUNTER_BARRIER
#print axioms PiCt.ReflectedWalk.PI_NOT_NORMAL_OF_COUNTER_BARRIER
#check PiCt.ReflectedWalk.PI_NOT_NORMAL_OF_BOUNDARY_INVARIANT
#print axioms PiCt.ReflectedWalk.PI_NOT_NORMAL_OF_BOUNDARY_INVARIANT

#check PiCt.OrbitPotential.phase_succ
#print axioms PiCt.OrbitPotential.phase_succ
#check PiCt.OrbitPotential.pairDifference_eq_observable
#print axioms PiCt.OrbitPotential.pairDifference_eq_observable
#check PiCt.OrbitPotential.phaseMap_one_third
#print axioms PiCt.OrbitPotential.phaseMap_one_third
#check PiCt.OrbitPotential.observable_one_third
#print axioms PiCt.OrbitPotential.observable_one_third
#check PiCt.OrbitPotential.no_global_subaction
#print axioms PiCt.OrbitPotential.no_global_subaction
#check PiCt.OrbitPotential.not_normal_of_potential_sequence
#print axioms PiCt.OrbitPotential.not_normal_of_potential_sequence
#check PiCt.OrbitPotential.not_normal_of_orbit_potential
#print axioms PiCt.OrbitPotential.not_normal_of_orbit_potential
#check PiCt.OrbitPotential.real_not_normal_of_orbit_potential
#print axioms PiCt.OrbitPotential.real_not_normal_of_orbit_potential

-- Long alternating-word frequencies: finite bounds and explicit conditional closures.
#check PiCt.CoefficientAccumulation.C_adjacent_cancel
#print axioms PiCt.CoefficientAccumulation.C_adjacent_cancel
#check PiCt.CoefficientAccumulation.C_prefix_sum
#print axioms PiCt.CoefficientAccumulation.C_prefix_sum
#check PiCt.CoefficientAccumulation.C_even_prefix_sum
#print axioms PiCt.CoefficientAccumulation.C_even_prefix_sum
#check PiCt.CoefficientAccumulation.C_aligned
#print axioms PiCt.CoefficientAccumulation.C_aligned
#check PiCt.CoefficientAccumulation.C_aligned_prefix_sum
#print axioms PiCt.CoefficientAccumulation.C_aligned_prefix_sum
#check PiCt.CoefficientAccumulation.blockMass_bounds
#print axioms PiCt.CoefficientAccumulation.blockMass_bounds
#check PiCt.CoefficientAccumulation.fixed_length_mass_tendsto_zero
#print axioms PiCt.CoefficientAccumulation.fixed_length_mass_tendsto_zero
#check PiCt.AnalyticWordProduct.wordProduct_eq_prod
#print axioms PiCt.AnalyticWordProduct.wordProduct_eq_prod
#check PiCt.AnalyticWordProduct.offset_delta_bounds
#print axioms PiCt.AnalyticWordProduct.offset_delta_bounds
#check PiCt.AnalyticWordProduct.factor_bounds
#print axioms PiCt.AnalyticWordProduct.factor_bounds
#check PiCt.AnalyticWordProduct.factor_error
#print axioms PiCt.AnalyticWordProduct.factor_error
#check PiCt.AnalyticWordProduct.wordProduct_nonneg
#print axioms PiCt.AnalyticWordProduct.wordProduct_nonneg
#check PiCt.AnalyticWordProduct.wordProduct_error
#print axioms PiCt.AnalyticWordProduct.wordProduct_error
#check PiCt.AnalyticWordProduct.wordProduct_fixed_length_limit
#print axioms PiCt.AnalyticWordProduct.wordProduct_fixed_length_limit
#check PiCt.AnalyticWordProduct.wordProduct_average_limit
#print axioms PiCt.AnalyticWordProduct.wordProduct_average_limit
#check PiCt.AnalyticWordProduct.suppressedProduct_le
#print axioms PiCt.AnalyticWordProduct.suppressedProduct_le
#check PiCt.AnalyticWordProduct.suppressedProduct_error
#print axioms PiCt.AnalyticWordProduct.suppressedProduct_error
#check PiCt.AnalyticWordProduct.minusProduct_le_plusProduct
#print axioms PiCt.AnalyticWordProduct.minusProduct_le_plusProduct
#check PiCt.AnalyticWordProduct.combinedProduct_ge_uniform
#print axioms PiCt.AnalyticWordProduct.combinedProduct_ge_uniform
#check PiCt.AlternatingFrequency.alternating_zero
#print axioms PiCt.AlternatingFrequency.alternating_zero
#check PiCt.AlternatingFrequency.alternating_even
#print axioms PiCt.AlternatingFrequency.alternating_even
#check PiCt.AlternatingFrequency.alternating_odd
#print axioms PiCt.AlternatingFrequency.alternating_odd
#check PiCt.AlternatingFrequency.code_occurrence_even_pairs
#print axioms PiCt.AlternatingFrequency.code_occurrence_even_pairs
#check PiCt.AlternatingFrequency.code_occurrence_odd_pairs
#print axioms PiCt.AlternatingFrequency.code_occurrence_odd_pairs
#check PiCt.AlternatingFrequency.alternating_codes_ne
#print axioms PiCt.AlternatingFrequency.alternating_codes_ne
#check PiCt.AlternatingFrequency.normal_wordFreq
#print axioms PiCt.AlternatingFrequency.normal_wordFreq
#check PiCt.AlternatingFrequency.normal_totalFreq
#print axioms PiCt.AlternatingFrequency.normal_totalFreq
#check PiCt.AlternatingFrequency.normal_deficit_zero
#print axioms PiCt.AlternatingFrequency.normal_deficit_zero
#check PiCt.AlternatingFrequency.deficit_ge_iff
#print axioms PiCt.AlternatingFrequency.deficit_ge_iff
#check PiCt.AlternatingFrequency.not_normal_of_persistent_deficit
#print axioms PiCt.AlternatingFrequency.not_normal_of_persistent_deficit
#check PiCt.AlternatingFrequency.normal_dyadic_deficit_zero
#print axioms PiCt.AlternatingFrequency.normal_dyadic_deficit_zero
#check PiCt.AlternatingFrequency.not_normal_of_persistent_dyadic_deficit
#print axioms PiCt.AlternatingFrequency.not_normal_of_persistent_dyadic_deficit
#check PiCt.AlternatingFrequency.PI_NOT_NORMAL_OF_ALTERNATING_SUPPRESSION
#print axioms PiCt.AlternatingFrequency.PI_NOT_NORMAL_OF_ALTERNATING_SUPPRESSION
#check PiCt.AlternatingFrequency.PI_NOT_NORMAL_OF_DYADIC_ALTERNATING_SUPPRESSION
#print axioms PiCt.AlternatingFrequency.PI_NOT_NORMAL_OF_DYADIC_ALTERNATING_SUPPRESSION
#check PiCt.AlternatingExcursions.paritySum_sub_of_alternating10
#print axioms PiCt.AlternatingExcursions.paritySum_sub_of_alternating10
#check PiCt.AlternatingExcursions.accumulated_block_bounds
#print axioms PiCt.AlternatingExcursions.accumulated_block_bounds
#check PiCt.AlternatingExcursions.residual_excursion
#print axioms PiCt.AlternatingExcursions.residual_excursion
#check PiCt.AlternatingExcursions.alternating_endpoint_tail
#print axioms PiCt.AlternatingExcursions.alternating_endpoint_tail
#check PiCt.AlternatingExcursions.indicator_bounds
#print axioms PiCt.AlternatingExcursions.indicator_bounds
#check PiCt.AlternatingExcursions.indicator_le_add_of_or
#print axioms PiCt.AlternatingExcursions.indicator_le_add_of_or
#check PiCt.AlternatingExcursions.shifted_sum_le
#print axioms PiCt.AlternatingExcursions.shifted_sum_le
#check PiCt.AlternatingExcursions.aligned_count_le_tail
#print axioms PiCt.AlternatingExcursions.aligned_count_le_tail
#check PiCt.AlternatingExcursions.aligned_frequency_le_tail
#print axioms PiCt.AlternatingExcursions.aligned_frequency_le_tail
#check PiCt.AlternatingExcursions.analyticStep_bounds
#print axioms PiCt.AlternatingExcursions.analyticStep_bounds
#check PiCt.AlternatingExcursions.residual_analyticStep
#print axioms PiCt.AlternatingExcursions.residual_analyticStep
#check PiCt.AlternatingExcursions.PI_ALIGNED_ALTERNATING_FREQUENCY_BOUND
#print axioms PiCt.AlternatingExcursions.PI_ALIGNED_ALTERNATING_FREQUENCY_BOUND
#check PiCt.AlternatingTailClosure.wordIndicator_even_le
#print axioms PiCt.AlternatingTailClosure.wordIndicator_even_le
#check PiCt.AlternatingTailClosure.wordIndicator_odd_le
#print axioms PiCt.AlternatingTailClosure.wordIndicator_odd_le
#check PiCt.AlternatingTailClosure.totalFreq_eq_indicator_sum
#print axioms PiCt.AlternatingTailClosure.totalFreq_eq_indicator_sum
#check PiCt.AlternatingTailClosure.ordinary_count_le_aligned
#print axioms PiCt.AlternatingTailClosure.ordinary_count_le_aligned
#check PiCt.AlternatingTailClosure.totalFreq_le_residual_tail
#print axioms PiCt.AlternatingTailClosure.totalFreq_le_residual_tail
#check PiCt.AlternatingTailClosure.normal_odd_alternating_target
#print axioms PiCt.AlternatingTailClosure.normal_odd_alternating_target
#check PiCt.AlternatingTailClosure.not_normal_of_eventually_small_residual_tail
#print axioms PiCt.AlternatingTailClosure.not_normal_of_eventually_small_residual_tail
#check PiCt.AlternatingTailClosure.PI_NOT_NORMAL_OF_SMALL_RESIDUAL_TAIL
#print axioms PiCt.AlternatingTailClosure.PI_NOT_NORMAL_OF_SMALL_RESIDUAL_TAIL
#check PiCt.AlternatingTailClosure.PI_ALTERNATING_FREQUENCY_TAIL_BOUND
#print axioms PiCt.AlternatingTailClosure.PI_ALTERNATING_FREQUENCY_TAIL_BOUND
#check PiCt.AlternatingTailClosure.PI_NOT_NORMAL_OF_SMALL_ANALYTIC_RESIDUAL_TAIL
#print axioms PiCt.AlternatingTailClosure.PI_NOT_NORMAL_OF_SMALL_ANALYTIC_RESIDUAL_TAIL
