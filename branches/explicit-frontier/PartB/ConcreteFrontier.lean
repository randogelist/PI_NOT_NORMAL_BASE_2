import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import PartA.CtMagnitude
import AWPI.VanishingCoefficientsAnchor

namespace ANCHOPI.PartB.ConcreteFrontier

open Filter Topology
open ANCHOPI.PartA
open AWPI.VanishingCoefficientsAnchor

/-- One-based floor-parity digit with the same dummy-zero convention as the
    source Rocq development. -/
noncomputable def actualPiDigits : Digits
  | 0 => false
  | n + 1 => Int.floor ((2 : ℝ) ^ (n + 1) * Real.pi) % 2 = 1

/-- Half the binary shell depth: these aligned pair indices fill digit
    positions [N_a,2N_a). -/
def halfShellN (a : ℕ) : ℕ := 2 ^ (9 + a)

lemma halfShellN_pos (a : ℕ) : 0 < halfShellN a := by
  unfold halfShellN
  positivity

/-- 10 and 01 indicators on the disjoint aligned pair starting at 2j. -/
def pair10Indicator (d : Digits) (j : ℕ) : ℝ :=
  if d (2 * j) = true ∧ d (2 * j + 1) = false then 1 else 0

def pair01Indicator (d : Digits) (j : ℕ) : ℝ :=
  if d (2 * j) = false ∧ d (2 * j + 1) = true then 1 else 0

/-- Actual aligned 10-minus-01 shell statistic. -/
noncomputable def actualShellGap (d : Digits) (a : ℕ) : ℝ :=
  let N := halfShellN a
  (∑ j ∈ Finset.Ico N (2 * N),
      (pair10Indicator d j - pair01Indicator d j)) / (N : ℝ)

/-- The analytic shell mass produced by the positive logarithmic C_t
    magnitudes: C_(a,t)/N_a = ctMagnitude(N_a+t). -/
noncomputable def analyticShellMass (a : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (shellN a), ctMagnitude (shellX a t)

noncomputable def analyticTarget : ℝ := Real.log 2 / 4

/-- The concrete actual-pi remainder.  No existential choice is involved. -/
noncomputable def concretePiRemainder (a : ℕ) : ℝ :=
  actualShellGap actualPiDigits a - analyticShellMass a

/-- Exact identity A_a = H_a + R_a. -/
theorem concrete_pi_remainder_identity (a : ℕ) :
    actualShellGap actualPiDigits a =
      analyticShellMass a + concretePiRemainder a := by
  unfold concretePiRemainder
  ring

/-- Lean-port obligation #1.  The later Rocq merge proves the corresponding
    theorem as P2O26_LogShellLimit.g1_log_gap_limit and
    P2O32_G1Base2Cross.g1_base2_coefficient_pair_mass_limit. -/
def AnalyticShellLimit : Prop :=
  Tendsto analyticShellMass atTop (𝓝 analyticTarget)

/-- Lean-port obligation #2.  The later Rocq merge proves the corresponding
    ordinary-normality transfer through Merge01_Parity and P2O19_PairShell. -/
def NormalityKillsActualShell : Prop :=
  BinaryNormal actualPiDigits →
    Tendsto (actualShellGap actualPiDigits) atTop (𝓝 0)

/-- The genuine mathematical frontier after the two already-proved Rocq
    inputs are ported: actual pi does not exactly cancel the analytic mass. -/
def ActualPiNonCancellation : Prop :=
  ¬ Tendsto concretePiRemainder atTop (𝓝 (-analyticTarget))

/-- No bundled structure: the two formal-port inputs are visible separately. -/
theorem normal_pi_forces_exact_cancellation
    (hanalytic : AnalyticShellLimit)
    (hnormality : NormalityKillsActualShell)
    (hnormal : BinaryNormal actualPiDigits) :
    Tendsto concretePiRemainder atTop (𝓝 (-analyticTarget)) := by
  have hactual := hnormality hnormal
  show Tendsto
    (fun a => actualShellGap actualPiDigits a - analyticShellMass a)
    atTop (𝓝 (-analyticTarget))
  simpa [AnalyticShellLimit, analyticTarget] using hactual.sub hanalytic

/-- Exact final closure with all remaining inputs exposed in the theorem type. -/
theorem pi_nonnormal_of_noncancellation
    (hanalytic : AnalyticShellLimit)
    (hnormality : NormalityKillsActualShell)
    (hnoncancel : ActualPiNonCancellation) :
    ¬ BinaryNormal actualPiDigits := by
  intro hnormal
  exact hnoncancel (normal_pi_forces_exact_cancellation hanalytic hnormality hnormal)

/-- The status theorem: after the two source-theorem ports, the only remaining
    mathematical premise is ActualPiNonCancellation. -/
theorem A_TIER_CANDIDATE_CLOSURE
    (hanalytic : AnalyticShellLimit)
    (hnormality : NormalityKillsActualShell) :
    ActualPiNonCancellation → ¬ BinaryNormal actualPiDigits := by
  exact pi_nonnormal_of_noncancellation hanalytic hnormality

/-- Historical stronger sufficient route retained from the old Lean anchor. -/
theorem historical_bounded_remainder_route
    (d : Digits) (C : ℕ → ℝ) (plane offset : ℕ → ℕ) (B J : ℕ)
    (hC : ∀ t, 0 ≤ C t)
    (hbound : CriticalRemainderBound d C plane offset B J) :
    ¬ BinaryNormal d := by
  exact critical_bounded_remainder_not_normal d C plane offset B J hC hbound

end ANCHOPI.PartB.ConcreteFrontier
