import PiCt.Instance

/-!
# Scope of the analytic readout

A nonzero real rescaling changes the representative's anchor but cancels out
of the two-ray ratio. Consequently the same dyadic coefficient is obtained
at every nonzero real anchor. This theorem concerns analytic readouts; it
asserts no fact about the digit frequencies of any anchor.
-/

namespace PiCt
namespace ReadoutInvariant

open Filter
open scoped Topology

/-- The two-ray imaginary-part ratio of an arbitrary complex function. -/
noncomputable def rawSplit (f : ℂ → ℂ) (M : ℝ) : ℝ :=
  (f (Complex.I * (ComplexRepresentative.ray M 1 : ℂ))).im /
  (f (Complex.I * (ComplexRepresentative.ray M 2 : ℂ))).im

/-- No denominator nonvanishing assumption is needed for scale invariance. -/
theorem rawSplit_real_scale (f : ℂ → ℂ) (M : ℝ) {c : ℝ} (hc : c ≠ 0) :
    rawSplit (fun z => (c : ℂ) * f z) M = rawSplit f M := by
  simp only [rawSplit, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  exact mul_div_mul_left _ _ hc

/-- The same arctangent representative rescaled to an arbitrary real anchor. -/
noncomputable def scaledPrimitive (α : ℝ) (z : ℂ) : ℂ :=
  ((α / Real.pi : ℝ) : ℂ) * ComplexRepresentative.primitive z

theorem scaledPrimitive_anchor (α : ℝ) :
    scaledPrimitive α 1 = (α : ℂ) := by
  unfold scaledPrimitive
  rw [ComplexRepresentative.primitive_one, ← Complex.ofReal_mul,
    div_mul_cancel₀ _ Real.pi_ne_zero]

theorem rawSplit_scaledPrimitive (α : ℝ) (hα : α ≠ 0) (M : ℝ) :
    rawSplit (scaledPrimitive α) M =
      ComplexRepresentative.splitReadout M := by
  unfold scaledPrimitive
  rw [rawSplit_real_scale _ _ (div_ne_zero hα Real.pi_ne_zero)]
  rfl

theorem rawSplit_scaledPrimitive_eq_split (α : ℝ) (hα : α ≠ 0)
    {M : ℝ} (hM : 0 < M) :
    rawSplit (scaledPrimitive α) M = PiCt.split M := by
  rw [rawSplit_scaledPrimitive α hα,
    ComplexRepresentative.splitReadout_eq_split hM]

/-- The frozen parity convention, applied to a function's own raw split. -/
noncomputable def rawReadout (f : ℂ → ℂ) (a t : ℕ) : ℝ :=
  1 / 2 + (-1 : ℝ) ^ t * (rawSplit f (scale a + t) - 1 / 2)

noncomputable def rawScaled (f : ℂ → ℂ) (a t : ℕ) : ℝ :=
  scale a * (rawReadout f a t - 1 / 2)

theorem rawReadout_scaledPrimitive (α : ℝ) (hα : α ≠ 0) (a t : ℕ) :
    rawReadout (scaledPrimitive α) a t = Pi.readout a t := by
  unfold rawReadout
  rw [rawSplit_scaledPrimitive α hα]
  rfl

theorem rawScaled_scaledPrimitive (α : ℝ) (hα : α ≠ 0) (a t : ℕ) :
    rawScaled (scaledPrimitive α) a t = Pi.scaled a t := by
  unfold rawScaled
  rw [rawReadout_scaledPrimitive α hα]
  rfl

/-- Every nonzero real anchor has the same limit for this analytic readout. -/
theorem scaledPrimitive_coefficient_limit (α : ℝ) (hα : α ≠ 0) (t : ℕ) :
    Tendsto (fun a => rawScaled (scaledPrimitive α) a t)
      atTop (𝓝 (Pi.C_T t)) := by
  simpa only [rawScaled_scaledPrimitive α hα] using Pi.C_T_spec t

/-- The frozen value is independent of the nonzero anchor rescaling. -/
theorem scaledPrimitive_frozen_limit (α : ℝ) (hα : α ≠ 0) (t : ℕ) :
    Tendsto (fun a => rawScaled (scaledPrimitive α) a t)
      atTop (𝓝 ((-1 : ℝ) ^ t / 4)) := by
  simpa only [PI_CT_VALUE] using scaledPrimitive_coefficient_limit α hα t

end ReadoutInvariant
end PiCt
