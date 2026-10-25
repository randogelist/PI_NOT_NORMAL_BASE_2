import PiCt.Instance

/-! Downstream use: no assumed analytic laws or coefficient instances. -/

noncomputable section

open Filter
open scoped Topology
open PiCt

#synth PiRepresentative.HasDyadicCoefficients Pi

example : Pi.toFun 1 = (Real.pi : ℂ) := Pi.anchor

example (t : ℕ) : PiRepresentative.DyadicCoefficient Pi t := Pi.coefficient t

example (t : ℕ) :
    Tendsto (fun a : ℕ => Pi.scaled a t) atTop (𝓝 (Pi.C_T t)) :=
  (Pi.coefficient t).converges

example (t : ℕ) : Pi.C_T t = (-1 : ℝ) ^ t / 4 := PI_CT_VALUE t

example (t : ℕ) : Pi.C_T t = C t := PI_CT_EQ_FROZEN t

example (t : ℕ) : Pi.C_T t ≠ 0 := PI_CT_NE_ZERO t

example : Pi.C_T 0 = (1 : ℝ) / 4 := by
  rw [PI_CT_VALUE]
  norm_num

example : Pi.C_T 1 = -(1 : ℝ) / 4 := by
  rw [PI_CT_VALUE]
  norm_num

example (a t : ℕ) :
    |Pi.readout a t - 1 / 2 - Pi.C_T t / scale a| ≤
      ((t : ℝ) + 2) / (4 * scale a ^ 2) :=
  PI_CT_REMAINDER a t

example (t : ℕ) : ∃ c : PiRepresentative.DyadicCoefficient Pi t,
    c.value = (-1 : ℝ) ^ t / 4 :=
  ⟨Pi.coefficient t, PI_COEFFICIENT_VALUE t⟩

example (t : ℕ) (c : PiRepresentative.DyadicCoefficient Pi t) :
    c.value = Pi.C_T t :=
  c.value_unique (Pi.coefficient t)

end
