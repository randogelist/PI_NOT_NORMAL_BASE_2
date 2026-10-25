import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import PartA.PiRadixReadout

namespace ANCHOPI.PartA

/-- Position of the midpoint N+1 inside the logarithmic interval N → N+2. -/
noncomputable def localLogRatio (x : ℝ) : ℝ :=
  Real.log (1 + 1 / x) / Real.log (1 + 2 / x)

/-- Closed positive magnitude of the logarithmic midpoint defect. -/
noncomputable def ctMagnitude (x : ℝ) : ℝ :=
  Real.log (1 + 1 / (x * (x + 2))) /
    (2 * Real.log (1 + 2 / x))

/-- Exact algebra behind the logarithmic defect. -/
lemma midpoint_rational_identity {x : ℝ} (hx : 0 < x) :
    ((1 + 1 / x) * (1 + 1 / x)) / (1 + 2 / x) =
      1 + 1 / (x * (x + 2)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx2 : x + 2 ≠ 0 := by linarith
  have hbpos : 0 < 1 + 2 / x := by
    have hdiv : 0 < 2 / x := div_pos (by norm_num) hx
    linarith
  field_simp [hx0, hx2, ne_of_gt hbpos]
  ring

/-- The local logarithmic ratio differs from 1/2 by exactly ctMagnitude. -/
theorem localLogRatio_sub_half_eq_ctMagnitude {x : ℝ} (hx : 0 < x) :
    localLogRatio x - 1 / 2 = ctMagnitude x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : 0 < 1 + 1 / x := by
    have hdiv : 0 < 1 / x := one_div_pos.mpr hx
    linarith
  have hb : 0 < 1 + 2 / x := by
    have hdiv : 0 < 2 / x := div_pos (by norm_num) hx
    linarith
  have hblog : Real.log (1 + 2 / x) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have hdiv : 0 < 2 / x := div_pos (by norm_num) hx
    linarith
  have hlog :
      2 * Real.log (1 + 1 / x) - Real.log (1 + 2 / x) =
        Real.log (1 + 1 / (x * (x + 2))) := by
    calc
      2 * Real.log (1 + 1 / x) - Real.log (1 + 2 / x)
          = Real.log ((1 + 1 / x) * (1 + 1 / x)) -
              Real.log (1 + 2 / x) := by
                rw [Real.log_mul (ne_of_gt ha) (ne_of_gt ha)]
                ring
      _ = Real.log (((1 + 1 / x) * (1 + 1 / x)) / (1 + 2 / x)) := by
            symm
            exact Real.log_div (mul_ne_zero (ne_of_gt ha) (ne_of_gt ha))
              (ne_of_gt hb)
      _ = Real.log (1 + 1 / (x * (x + 2))) := by
            rw [midpoint_rational_identity hx]
  have hratio (A B : ℝ) (hB : B ≠ 0) :
      A / B - 1 / 2 = (2 * A - B) / (2 * B) := by
    field_simp [hB]
  unfold localLogRatio ctMagnitude
  calc
    Real.log (1 + 1 / x) / Real.log (1 + 2 / x) - 1 / 2 =
        (2 * Real.log (1 + 1 / x) - Real.log (1 + 2 / x)) /
          (2 * Real.log (1 + 2 / x)) := hratio _ _ hblog
    _ = Real.log (1 + 1 / (x * (x + 2))) /
          (2 * Real.log (1 + 2 / x)) := by rw [hlog]

/-- The defect magnitude is strictly positive for every positive address. -/
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

theorem ctMagnitude_ne_zero {x : ℝ} (hx : 0 < x) : ctMagnitude x ≠ 0 :=
  ne_of_gt (ctMagnitude_pos hx)

theorem localLogRatio_gt_half {x : ℝ} (hx : 0 < x) :
    1 / 2 < localLogRatio x := by
  have h := ctMagnitude_pos hx
  rw [← localLogRatio_sub_half_eq_ctMagnitude hx] at h
  linarith

/-- Dyadic shell N_a = 2^(10+a), matching the G1 bit-address scale. -/
def shellN (a : ℕ) : ℕ := 2 ^ (10 + a)

/-- Real address N_a+t. -/
def shellX (a t : ℕ) : ℝ := (shellN a + t : ℕ)

lemma shellN_pos (a : ℕ) : 0 < shellN a := by
  unfold shellN
  positivity

lemma shellX_pos (a t : ℕ) : 0 < shellX a t := by
  unfold shellX
  exact_mod_cast Nat.add_pos_left (shellN_pos a) t

/-- Positive scaled coefficient |C_t| = N_a * defect(N_a+t). -/
noncomputable def shellCtMagnitude (a t : ℕ) : ℝ :=
  (shellN a : ℝ) * ctMagnitude (shellX a t)

theorem shellCtMagnitude_pos (a t : ℕ) : 0 < shellCtMagnitude a t := by
  unfold shellCtMagnitude
  apply mul_pos
  · exact_mod_cast shellN_pos a
  · exact ctMagnitude_pos (shellX_pos a t)

/-- Odd/even orientation: even t gets +1, odd t gets -1. -/
def paritySign (t : ℕ) : ℝ := if t % 2 = 0 then 1 else -1

theorem paritySign_even (k : ℕ) : paritySign (2 * k) = 1 := by
  unfold paritySign
  have h : (2 * k) % 2 = 0 := by omega
  simp [h]

theorem paritySign_odd (k : ℕ) : paritySign (2 * k + 1) = -1 := by
  unfold paritySign
  have h : (2 * k + 1) % 2 = 1 := by omega
  simp [h]

/-- The oriented Part-A coefficient C_t. -/
noncomputable def Ct (a t : ℕ) : ℝ := paritySign t * shellCtMagnitude a t

/-- Exact derivation of C_t from the local logarithmic midpoint defect. -/
theorem Ct_eq_oriented_log_defect (a t : ℕ) :
    Ct a t = paritySign t * (shellN a : ℝ) *
      (localLogRatio (shellX a t) - 1 / 2) := by
  unfold Ct shellCtMagnitude
  rw [localLogRatio_sub_half_eq_ctMagnitude (shellX_pos a t)]
  ring

/-- C_t is never zero. -/
theorem Ct_ne_zero (a t : ℕ) : Ct a t ≠ 0 := by
  have hm : shellCtMagnitude a t ≠ 0 := ne_of_gt (shellCtMagnitude_pos a t)
  unfold Ct paritySign
  split <;> simp_all

/-- Even coefficients are strictly positive. -/
theorem Ct_even_pos (a k : ℕ) : 0 < Ct a (2 * k) := by
  rw [Ct, paritySign_even]
  simpa using shellCtMagnitude_pos a (2 * k)

/-- Odd coefficients are strictly negative. -/
theorem Ct_odd_neg (a k : ℕ) : Ct a (2 * k + 1) < 0 := by
  rw [Ct, paritySign_odd]
  have h := shellCtMagnitude_pos a (2 * k + 1)
  linarith

/-- Complete Part-A analytic core: π is anchored by the integral, G1 reads an
    actual π bit, and every logarithmic odd/even coefficient C_t is nonzero. -/
theorem PART_A_CT :
    (∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x ^ 2)) = Real.pi / 4 ∧
    (∀ f : ℕ → ℤ, ∀ a : ℕ,
      Int.floor (4 * radixState f (carryIndex a)) % 2 = g1Bit a) ∧
    (∀ a t : ℕ,
      Ct a t = paritySign t * (shellN a : ℝ) *
        (localLogRatio (shellX a t) - 1 / 2) ∧ Ct a t ≠ 0) := by
  refine ⟨pi_integral_anchor, ?_, ?_⟩
  · intro f a
    exact g1_from_radix f a
  · intro a t
    exact ⟨Ct_eq_oriented_log_defect a t, Ct_ne_zero a t⟩

end ANCHOPI.PartA
