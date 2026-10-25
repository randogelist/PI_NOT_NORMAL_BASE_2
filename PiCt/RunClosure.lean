import PiCt.RunFrequency
import PiCt.ReadoutInvariant

/-!
# Conditional closure of the 0000/1111 route

The actual pi digit sequence is used throughout. `CtRunBridge` is an explicit
UNPROVED sufficient hypothesis. No instance or theorem asserting it is provided.
-/

open Filter
open scoped Topology

namespace PiCt
namespace RunClosure

open BinaryWords RunFrequency

/-- One sufficient bridge to the frozen coefficient. It is not yet established for pi. -/
def CtRunBridge (t : ℕ) : Prop :=
  Tendsto (fun a : ℕ => dyadicDefect piBits a - Pi.scaled a t) atTop (𝓝 0)

theorem PI_RUN_DEFECT_OF_CT_BRIDGE (t : ℕ) (hbridge : CtRunBridge t) :
    Tendsto (dyadicDefect piBits) atTop (𝓝 (Pi.C_T t)) := by
  have h := hbridge.add (PI_CT_INSTANTIATED t)
  simpa using h

/-- At least one of the two actual word frequencies fails the normal target. -/
theorem PI_EXTREME_WORD_FAILURE_OF_CT_BRIDGE (t : ℕ) (hbridge : CtRunBridge t) :
    ¬ ExtremeWordsBalanced piBits :=
  not_balanced_of_defect_limit (PI_CT_NE_ZERO t) (PI_RUN_DEFECT_OF_CT_BRIDGE t hbridge)

/-- Conditional only: the displayed bridge is an essential unresolved premise. -/
theorem PI_NOT_NORMAL_OF_CT_RUN_BRIDGE (t : ℕ) (hbridge : CtRunBridge t) :
    ¬ BinaryNormal piBits :=
  not_normal_of_defect_limit (PI_CT_NE_ZERO t) (PI_RUN_DEFECT_OF_CT_BRIDGE t hbridge)

/-- The endpoint explicitly concerns bits extracted from `Real.pi`. -/
theorem REAL_PI_NOT_NORMAL_OF_CT_RUN_BRIDGE (t : ℕ) (hbridge : CtRunBridge t) :
    ¬ BinaryNormal (bit Real.pi) := by
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact PI_NOT_NORMAL_OF_CT_RUN_BRIDGE t hbridge

theorem PI_PAIR_FREQUENCY_OF_CT_BRIDGE (t : ℕ) (hbridge : CtRunBridge t) :
    Tendsto (fun a : ℕ => zeroRun piBits (dyadicLength a) +
      oneRun piBits (dyadicLength a)) atTop (𝓝 (1 / 8 + Pi.C_T t / 8)) := by
  have hd := PI_RUN_DEFECT_OF_CT_BRIDGE t hbridge
  have h := (hd.div_const 8).const_add (1 / 8 : ℝ)
  have heq (a : ℕ) : zeroRun piBits (dyadicLength a) + oneRun piBits (dyadicLength a) =
      1 / 8 + dyadicDefect piBits a / 8 :=
    pair_frequency_identity piBits (dyadicLength a) (dyadicLength_pos a)
  simp only [heq]
  exact h

/-- The numerical target 5/32 follows IF the t=0 bridge is proved. -/
theorem PI_PAIR_LIMIT_FIVE_THIRTYTWO_OF_BRIDGE (hbridge : CtRunBridge 0) :
    Tendsto (fun a : ℕ => zeroRun piBits (dyadicLength a) +
      oneRun piBits (dyadicLength a)) atTop (𝓝 (5 / 32)) := by
  have h := PI_PAIR_FREQUENCY_OF_CT_BRIDGE 0 hbridge
  norm_num [PI_CT_VALUE] at h
  exact h

/-- A persistent actual digit defect suffices, without assuming any coefficient bridge. -/
theorem PI_NOT_NORMAL_OF_PERSISTENT_RUN_DEFECT {ε : ℝ} (hε : 0 < ε)
    (hdefect : ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧ ε ≤ |dyadicDefect piBits a|) :
    ¬ BinaryNormal piBits :=
  not_normal_of_persistent_defect hε hdefect

/-- Under normality the proposed residual would instead tend to -C_t, not zero. -/
theorem PI_BRIDGE_RESIDUAL_UNDER_NORMALITY (hn : BinaryNormal piBits) (t : ℕ) :
    Tendsto (fun a : ℕ => dyadicDefect piBits a - Pi.scaled a t)
      atTop (𝓝 (-Pi.C_T t)) := by
  have hz := balanced_dyadicDefect_zero (normal_extremeWordsBalanced hn)
  simpa using hz.sub (PI_CT_INSTANTIATED t)

end RunClosure
end PiCt
