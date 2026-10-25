import ActualPi.PiReadout

namespace ANCHOPI.CTClosure

open AWPIWordAnchor
open ANCHOPI.ActualPi

/--
The weakest canonical C_t object: failure of the fair-frequency limit for
one fixed finite word in the actual binary digit stream of pi.

The index t is the word itself; this avoids an irrelevant Nat-enumeration layer.
-/
abbrev Ct (t : word) : Prop :=
  ¬ tends_to (frequency actualPiDigits t) (fair_mass t)

/-- The one explicitly permitted research input. -/
def CTπ : Prop :=
  ∃ t : word, Ct t

/-- ASCII alias for runners/scripts. -/
abbrev CT_pi : Prop := CTπ

/-- CTπ immediately contradicts ordinary binary normality. -/
theorem CTπ_imp_pi_not_normal
    (hCT : CTπ) :
    ¬ normal actualPiDigits := by
  intro hnormal
  rcases hCT with ⟨t, ht⟩
  exact ht (hnormal t)

/-- Failure of binary normality supplies exactly one C_t witness. -/
theorem pi_not_normal_imp_CTπ
    (hnot : ¬ normal actualPiDigits) :
    CTπ := by
  classical
  by_contra hCT
  apply hnot
  intro t
  by_contra ht
  exact hCT ⟨t, ht⟩

/--
Canonical exact characterization.  No tracking, remainder, GAP, selector,
or extra pi-binding premise occurs anywhere in the statement.
-/
theorem CTπ_iff_pi_not_normal :
    CTπ ↔ ¬ normal actualPiDigits := by
  constructor
  · exact CTπ_imp_pi_not_normal
  · exact pi_not_normal_imp_CTπ

/-- Frozen one-way endpoint. -/
theorem PI_NOT_NORMAL_BASE2_OF_CT :
    CTπ → ¬ normal actualPiDigits :=
  CTπ_imp_pi_not_normal

/-- Frozen equivalence endpoint. -/
theorem CT_EXACTLY_PI_NOT_NORMAL_BASE2 :
    CTπ ↔ ¬ normal actualPiDigits :=
  CTπ_iff_pi_not_normal

end ANCHOPI.CTClosure
