import PiCt.Endpoints

/-!
# A coefficient instantiated inside the genuine pi representative

The readout is calculated from the representative's function field. The
coefficient is extracted from a proved unique limit, then evaluated by a
theorem. The concrete `Pi` instance has no unproved analytic input.
-/

open Filter
open scoped Topology

namespace PiCt

/-- A function representative with a checked anchor at the genuine pi. -/
structure PiRepresentative where
  toFun : ℂ → ℂ
  anchor : toFun 1 = (Real.pi : ℂ)

namespace PiRepresentative

/-- The readout is computed from the object's own function field. -/
noncomputable def split (R : PiRepresentative) (M : ℝ) : ℝ :=
  (R.toFun (Complex.I * (ComplexRepresentative.ray M 1 : ℂ))).im /
  (R.toFun (Complex.I * (ComplexRepresentative.ray M 2 : ℂ))).im

/-- Retains the previously frozen parity convention and dyadic scale. -/
noncomputable def readout (R : PiRepresentative) (a t : ℕ) : ℝ :=
  1 / 2 + (-1 : ℝ) ^ t * (R.split (scale a + t) - 1 / 2)

noncomputable def scaled (R : PiRepresentative) (a t : ℕ) : ℝ :=
  scale a * (R.readout a t - 1 / 2)

/-- A proof interface, instantiated below for the concrete pi representative. -/
class HasDyadicCoefficients (R : PiRepresentative) : Prop where
  exists_unique : ∀ t : ℕ,
    ∃! c : ℝ, Tendsto (fun a : ℕ => R.scaled a t) atTop (𝓝 c)

/-- A first-class coefficient object, carrying its own limit certificate. -/
structure DyadicCoefficient (R : PiRepresentative) (t : ℕ) where
  value : ℝ
  converges : Tendsto (fun a : ℕ => R.scaled a t) atTop (𝓝 value)

/-- Construct the object from proved existence, without prescribing its value. -/
noncomputable def coefficient (R : PiRepresentative) [HasDyadicCoefficients R]
    (t : ℕ) : DyadicCoefficient R t where
  value := Classical.choose ((HasDyadicCoefficients.exists_unique (R := R) t).exists)
  converges := Classical.choose_spec
    ((HasDyadicCoefficients.exists_unique (R := R) t).exists)

/-- The scalar is a projection of the internally constructed coefficient object. -/
noncomputable def C_T (R : PiRepresentative) [HasDyadicCoefficients R] (t : ℕ) : ℝ :=
  (R.coefficient t).value

theorem C_T_spec (R : PiRepresentative) [HasDyadicCoefficients R] (t : ℕ) :
    Tendsto (fun a : ℕ => R.scaled a t) atTop (𝓝 (R.C_T t)) :=
  (R.coefficient t).converges

theorem C_T_eq_of_tendsto (R : PiRepresentative) [HasDyadicCoefficients R]
    (t : ℕ) {c : ℝ} (hc : Tendsto (fun a : ℕ => R.scaled a t) atTop (𝓝 c)) :
    R.C_T t = c :=
  tendsto_nhds_unique (R.C_T_spec t) hc

@[simp] theorem coefficient_value (R : PiRepresentative) [HasDyadicCoefficients R]
    (t : ℕ) : (R.coefficient t).value = R.C_T t := rfl

theorem DyadicCoefficient.value_unique {R : PiRepresentative} {t : ℕ}
    (x y : DyadicCoefficient R t) : x.value = y.value :=
  tendsto_nhds_unique x.converges y.converges

end PiRepresentative

/-- The actual arctangent representative, anchored at `Real.pi`. -/
noncomputable def Pi : PiRepresentative where
  toFun := ComplexRepresentative.primitive
  anchor := ComplexRepresentative.primitive_one

theorem PI_ANCHOR : Pi.toFun 1 = (Real.pi : ℂ) := Pi.anchor

theorem PI_POWER_SERIES {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 4 * ((-1 : ℂ) ^ n * z ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℂ))) (Pi.toFun z) :=
  ComplexRepresentative.primitive_hasSum hz

theorem PI_SPLIT_EQ (M : ℝ) :
    Pi.split M = ComplexRepresentative.splitReadout M := rfl

theorem PI_READOUT_EQ (a t : ℕ) : Pi.readout a t = piReadout a t := rfl

theorem PI_INTERNAL_LOG_READOUT {M : ℝ} (hM : 0 < M) :
    Pi.split M = 1 / 2 + delta M :=
  ComplexRepresentative.splitReadout_eq_half_add_delta hM

/-- Concrete discharge of the entire coefficient-existence interface. -/
instance piHasDyadicCoefficients : PiRepresentative.HasDyadicCoefficients Pi where
  exists_unique t := PI_REPRESENTATIVE_CT_UNIQUE t

/-- No class hypothesis remains: the instance is constructed above. -/
theorem PI_CT_INSTANTIATED (t : ℕ) :
    Tendsto (fun a : ℕ => Pi.scaled a t) atTop (𝓝 (Pi.C_T t)) :=
  Pi.C_T_spec t

/-- Evaluation of the internally instantiated coefficient, proved after construction. -/
theorem PI_CT_VALUE (t : ℕ) : Pi.C_T t = (-1 : ℝ) ^ t / 4 := by
  apply Pi.C_T_eq_of_tendsto t
  exact PI_REPRESENTATIVE_CT t

theorem PI_CT_EQ_FROZEN (t : ℕ) : Pi.C_T t = C t := PI_CT_VALUE t

theorem PI_CT_NE_ZERO (t : ℕ) : Pi.C_T t ≠ 0 := by
  rw [PI_CT_EQ_FROZEN]
  exact C_ne_zero t

theorem PI_CT_REMAINDER (a t : ℕ) :
    |Pi.readout a t - 1 / 2 - Pi.C_T t / scale a| ≤
      ((t : ℝ) + 2) / (4 * scale a ^ 2) := by
  rw [PI_READOUT_EQ, PI_CT_EQ_FROZEN]
  exact PI_REPRESENTATIVE_REMAINDER a t

theorem PI_CT_CAUCHY {a b : ℕ} (hab : a ≤ b) (t : ℕ) :
    |Pi.scaled b t - Pi.scaled a t| ≤ ((t : ℝ) + 2) / (4 * scale a) :=
  PI_REPRESENTATIVE_CAUCHY hab t

theorem PI_CT_UNIQUE (t : ℕ) {c : ℝ}
    (hc : Tendsto (fun a : ℕ => Pi.scaled a t) atTop (𝓝 c)) : c = Pi.C_T t :=
  (Pi.C_T_eq_of_tendsto t hc).symm

theorem PI_COEFFICIENT_VALUE (t : ℕ) :
    (Pi.coefficient t).value = (-1 : ℝ) ^ t / 4 := PI_CT_VALUE t

theorem PI_CT_UNSCALED_LIMIT (t : ℕ) :
    Tendsto (fun a : ℕ => Pi.readout a t) atTop (𝓝 (1 / 2)) :=
  PI_REPRESENTATIVE_UNSCALED_LIMIT t

end PiCt
