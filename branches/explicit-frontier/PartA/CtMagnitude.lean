import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ANCHOPI.PartA

/-- The positive logarithmic midpoint defect.  This is the unsigned C_t
    magnitude used by the reconstructed A/B chain. -/
noncomputable def ctMagnitude (x : ℝ) : ℝ :=
  Real.log (1 + 1 / (x * (x + 2))) /
    (2 * Real.log (1 + 2 / x))

/-- Dyadic shell scale N_a = 2^(10+a). -/
def shellN (a : ℕ) : ℕ := 2 ^ (10 + a)

def shellX (a t : ℕ) : ℝ := (shellN a + t : ℕ)

lemma shellN_pos (a : ℕ) : 0 < shellN a := by
  unfold shellN
  positivity

lemma shellX_pos (a t : ℕ) : 0 < shellX a t := by
  unfold shellX
  exact_mod_cast Nat.add_pos_left (shellN_pos a) t

/-- Exact positivity of the unsigned coefficient magnitude. -/
theorem ctMagnitude_pos {x : ℝ} (hx : 0 < x) : 0 < ctMagnitude x := by
  unfold ctMagnitude
  apply div_pos
  · apply Real.log_pos
    have hx2 : 0 < x + 2 := by linarith
    have hprod : 0 < x * (x + 2) := mul_pos hx hx2
    have hfrac : 0 < 1 / (x * (x + 2)) := one_div_pos.mpr hprod
    linarith
  · have hlog : 0 < Real.log (1 + 2 / x) := by
      apply Real.log_pos
      have hdiv : 0 < 2 / x := div_pos (by norm_num) hx
      linarith
    nlinarith

/-- Positive exact coefficient on the finite (a,t)-plane. -/
noncomputable def Cmag (a t : ℕ) : ℝ :=
  (shellN a : ℝ) * ctMagnitude (shellX a t)

theorem Cmag_pos (a t : ℕ) : 0 < Cmag a t := by
  unfold Cmag
  apply mul_pos
  · exact_mod_cast shellN_pos a
  · exact ctMagnitude_pos (shellX_pos a t)

theorem Cmag_ne_zero (a t : ℕ) : Cmag a t ≠ 0 :=
  ne_of_gt (Cmag_pos a t)

end ANCHOPI.PartA
