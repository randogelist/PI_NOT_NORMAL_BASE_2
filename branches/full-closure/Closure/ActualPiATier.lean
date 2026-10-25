import ActualPi.PiReadout
import Closure.PiCtClosure

namespace ANCHOPI.Closure

open AWPIWordAnchor
open ANCHOPI.PartA
open ANCHOPI.PartB
open ANCHOPI.ActualPi

/--
The single genuine semantic frontier after Part A and Part B are closed:
there is a finite-window observable of the actual floor-defined π stream
which converges uniformly in the tail coordinate to the analytic coefficient
`limitingCt t = paritySign t / 4`.

No theorem below assumes this as an axiom; it is an explicit proposition.
-/
def ActualPiCtTracking : Prop :=
  ∃ H : ℕ → ℕ → ℝ,
    FiniteObservations actualPiDigits H ∧
    UniformTailLimit 0 H limitingCt

/-- The tracking formulation is exactly the data carried by the rebuilt binding. -/
theorem actualPiCtTracking_iff_binding :
    ActualPiCtTracking ↔ Nonempty (ActualPiCtBinding actualPiDigits) := by
  constructor
  · rintro ⟨H, hfinite, huniform⟩
    exact ⟨⟨H, hfinite, huniform⟩⟩
  · rintro ⟨h⟩
    exact ⟨h.H, h.finite, h.uniform⟩

/--
Actual-π A-tier closure: once the one genuine semantic tracking frontier is
proved, ordinary binary normality of the canonical π stream is impossible.
-/
theorem actual_pi_nonnormal_of_ct_tracking
    (htrack : ActualPiCtTracking) :
    ¬ normal actualPiDigits := by
  rcases htrack with ⟨H, hfinite, huniform⟩
  exact uniform_strict_parity_not_normal
    actualPiDigits H limitingCt 0 0
    hfinite huniform limitingCt_strictParity

/-- Same closure routed through the previously frozen binding theorem. -/
theorem actual_pi_nonnormal_of_binding
    (hbind : ActualPiCtBinding actualPiDigits) :
    ¬ normal actualPiDigits :=
  actual_pi_ct_binding_not_normal actualPiDigits hbind

/--
Frozen A-tier endpoint.  The theorem is specialized to the exact π readout;
its only mathematical premise is `ActualPiCtTracking`.
-/
theorem ACTUAL_PI_CT_A_TIER_CLOSURE :
    ActualPiCtTracking → ¬ normal actualPiDigits :=
  actual_pi_nonnormal_of_ct_tracking

/-- A small atlas collecting the closed analytic and logical sides. -/
theorem ACTUAL_PI_CT_A_TIER_ATLAS :
    (∀ t : ℕ, limitingCt t ≠ 0) ∧
    (∀ k : ℕ, 0 < limitingCt (2 * k)) ∧
    (∀ k : ℕ, limitingCt (2 * k + 1) < 0) ∧
    (ActualPiCtTracking → ¬ normal actualPiDigits) := by
  refine ⟨limitingCt_ne_zero, limitingCt_even_pos, limitingCt_odd_neg, ?_⟩
  exact ACTUAL_PI_CT_A_TIER_CLOSURE

end ANCHOPI.Closure
