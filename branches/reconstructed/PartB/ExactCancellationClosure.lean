import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import PartA.PiRadixReadout
import PartA.CtAnalytic
import AWPI.VanishingCoefficientsAnchor

namespace ANCHOPI.PartB.ExactCancellation

open Filter Topology
open ANCHOPI.PartA
open AWPI.VanishingCoefficientsAnchor

/-- The actual floor-parity binary stream of π, expressed in the `Digits` type
    used by the migrated ordinary-normality development. -/
noncomputable def actualPiDigits : Digits := fun n =>
  if binaryDigit Real.pi n = 1 then true else false

@[simp] theorem actualPiDigits_eq_true_iff (n : ℕ) :
    actualPiDigits n = true ↔ binaryDigit Real.pi n = 1 := by
  unfold actualPiDigits
  by_cases h : binaryDigit Real.pi n = 1 <;> simp [h]

/-- The limiting analytic shell mass occurring in the reconstructed source chain. -/
noncomputable def analyticTarget : ℝ := Real.log 2 / 4

/-- The canonical signed remainder is not existentially chosen: it is the exact
    difference between the actual shell statistic and the analytic shell mass. -/
noncomputable def concreteRemainder
    (actualShell analyticShell : ℕ → ℝ) (a : ℕ) : ℝ :=
  actualShell a - analyticShell a

/-- Exact decomposition `A_a = H_a + R_a`. -/
theorem concrete_remainder_identity
    (actualShell analyticShell : ℕ → ℝ) (a : ℕ) :
    actualShell a = analyticShell a + concreteRemainder actualShell analyticShell a := by
  unfold concreteRemainder
  ring

/-- The two source-derived facts which sit strictly before the final
    non-cancellation frontier in the later merged proof:

    * ordinary binary normality kills the concrete actual shell statistic;
    * the positive logarithmic shell mass tends to `log 2 / 4`.

    The later Rocq merge proves both for its concrete definitions.  This Lean
    structure is deliberately an interface until those two substantial source
    proofs are ported line-for-line. -/
structure ActualPiCancellationData where
  actualShell : ℕ → ℝ
  analyticShell : ℕ → ℝ
  normal_kills_actual :
    BinaryNormal actualPiDigits → Tendsto actualShell atTop (𝓝 0)
  analytic_shell_limit :
    Tendsto analyticShell atTop (𝓝 analyticTarget)

/-- The concrete remainder attached to one source-chain realization. -/
noncomputable def sourceRemainder (h : ActualPiCancellationData) : ℕ → ℝ :=
  concreteRemainder h.actualShell h.analyticShell

/-- Pointwise exact source identity. -/
theorem source_remainder_identity (h : ActualPiCancellationData) (a : ℕ) :
    h.actualShell a = h.analyticShell a + sourceRemainder h a := by
  exact concrete_remainder_identity h.actualShell h.analyticShell a

/-- Ordinary normality forces the exact cancellation limit
    `R_a → -log 2 / 4`.  This is the algebraic heart of the later merged
    cancellation frontier. -/
theorem normal_pi_forces_exact_cancellation
    (h : ActualPiCancellationData)
    (hnormal : BinaryNormal actualPiDigits) :
    Tendsto (sourceRemainder h) atTop (𝓝 (-analyticTarget)) := by
  have hactual : Tendsto h.actualShell atTop (𝓝 0) :=
    h.normal_kills_actual hnormal
  show Tendsto (fun a => h.actualShell a - h.analyticShell a) atTop (𝓝 (-analyticTarget))
  simpa using hactual.sub h.analytic_shell_limit

/-- The reconstructed final frontier: failure of exact cancellation directly
    refutes ordinary binary normality of the actual floor-defined π digits. -/
theorem failure_of_cancellation_refutes_normal_pi
    (h : ActualPiCancellationData)
    (hfailure : ¬ Tendsto (sourceRemainder h) atTop (𝓝 (-analyticTarget))) :
    ¬ BinaryNormal actualPiDigits := by
  intro hnormal
  exact hfailure (normal_pi_forces_exact_cancellation h hnormal)

/-- Same closure in implication form, useful as the final theorem-chain node. -/
theorem PART_B_EXACT_CANCELLATION_CLOSURE
    (h : ActualPiCancellationData) :
    (¬ Tendsto (sourceRemainder h) atTop (𝓝 (-analyticTarget))) →
      ¬ BinaryNormal actualPiDigits := by
  exact failure_of_cancellation_refutes_normal_pi h

/-- The positive logarithmic coefficient magnitude proved in Part A is
    available without any statistical hypothesis.  This theorem is included
    to make the source-chain separation explicit: positivity is analytic;
    non-cancellation of the *actual* remainder is the remaining frontier. -/
theorem partA_positive_coefficient_available (a t : ℕ) :
    0 < shellCtMagnitude a t :=
  shellCtMagnitude_pos a t

/-- The historical Lean obstruction is also retained: nonnegative critical
    drift plus a uniformly bounded *actual* remainder forbids ordinary binary
    normality. -/
theorem bounded_actual_remainder_route
    (d : Digits) (C : ℕ → ℝ)
    (plane offset : ℕ → ℕ) (B J : ℕ)
    (hC : ∀ t, 0 ≤ C t)
    (hbound : CriticalRemainderBound d C plane offset B J) :
    ¬ BinaryNormal d := by
  exact critical_bounded_remainder_not_normal d C plane offset B J hC hbound

end ANCHOPI.PartB.ExactCancellation
