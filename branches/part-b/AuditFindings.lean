import PartB.CtContradiction

/-!
Audit addition, 2026-10-25. The original Part B source is preserved byte for byte.
Its global shell-address field is impossible at j = 0, so CtDigitBridge must
not be presented as an inhabitable route to the actual pi endpoint.
This finding does not affect the separate generic CtDriftBridge theorem.
-/
namespace ANCHOPI.PartB.Audit

theorem ctDigitBridge_impossible (x : Bitstream) (a t : ℕ → ℕ) :
    ¬ CtDigitBridge x a t := by
  intro h
  have ha := h.address 0
  have hp := ANCHOPI.PartA.shellN_pos (a 0)
  omega

#print axioms ctDigitBridge_impossible

end ANCHOPI.PartB.Audit
