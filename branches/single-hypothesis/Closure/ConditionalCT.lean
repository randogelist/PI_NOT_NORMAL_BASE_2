import ActualPi.PiReadout

namespace ANCHOPI.CTClosure

open AWPIWordAnchor
open ANCHOPI.ActualPi

/--
A fixed finite word has a positive frequency defect arbitrarily far out.
This is attached directly to the floor-defined binary digits of pi.
-/
def PersistentWordDefect (x : bitstream) (w : word) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∀ cutoff : ℕ, ∃ N : ℕ, cutoff ≤ N ∧
      eps ≤ |frequency x w N - fair_mass w|

/--
The conditional C_t object, now defined directly on the actual pi digit stream.
There is no later tracking, remainder, GAP, or pi-binding premise.
-/
abbrev Ct (w : word) : Prop :=
  PersistentWordDefect actualPiDigits w

/-- The one explicitly permitted research input. -/
def CTπ : Prop :=
  ∃ w : word, Ct w

/-- ASCII alias for scripts that avoid Unicode identifiers. -/
abbrev CT_pi : Prop := CTπ

/-- Ordinary binary normality excludes every persistent fixed-word defect. -/
theorem normal_imp_not_persistentWordDefect
    (x : bitstream) (hnormal : normal x) (w : word) :
    ¬ PersistentWordDefect x w := by
  rintro ⟨eps, heps, hbad⟩
  have hhalf : 0 < eps / 2 := by linarith
  rcases hnormal w (eps / 2) hhalf with ⟨cutoff, hnear⟩
  rcases hbad cutoff with ⟨N, hN, hfar⟩
  have hclose : |frequency x w N - fair_mass w| < eps / 2 := by
    rw [abs_lt]
    exact hnear N hN
  linarith

/-- Under ordinary binary normality no actual-pi C_t witness can occur. -/
theorem normal_pi_imp_not_Ct
    (hnormal : normal actualPiDigits) (w : word) :
    ¬ Ct w :=
  normal_imp_not_persistentWordDefect actualPiDigits hnormal w

/-- CTπ is definitionally one persistent ordinary word-frequency defect. -/
theorem CTπ_iff_persistentWordDefect :
    CTπ ↔ ∃ w : word, PersistentWordDefect actualPiDigits w := by
  rfl

/--
FINAL CONDITIONAL CLOSURE.
The sole explicit mathematical premise is CTπ.
-/
theorem CTπ_imp_pi_not_normal
    (hCT : CTπ) :
    ¬ normal actualPiDigits := by
  intro hnormal
  rcases hCT with ⟨w, hw⟩
  exact normal_pi_imp_not_Ct hnormal w hw

/-- Frozen named endpoint. -/
theorem PI_NOT_NORMAL_BASE2_OF_CT :
    CTπ → ¬ normal actualPiDigits :=
  CTπ_imp_pi_not_normal

end ANCHOPI.CTClosure
