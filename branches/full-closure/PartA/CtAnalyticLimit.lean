import PartA.CtAnalyticKernel
import Closure.ActualPiATier

/-!
Analytic uniform-limit layer. This source was written without running a
compiler. The analytic family is not asserted to be a digit-local observable.
The final closure requires a separate finite observation H which uniformly
tracks the analytic family.
-/

namespace ANCHOPI.PartA

open ANCHOPI.PartB

def shellDepth (a : ℕ) : ℕ := 2 ^ (10 + a)

noncomputable def analyticSize (a t : ℕ) : ℝ := ((shellDepth a + t : ℕ) : ℝ)

noncomputable def analyticG (a t : ℕ) : ℝ :=
  1 / 2 + paritySign t * criticalDefect (analyticSize a t)

noncomputable def analyticRescaled (a t : ℕ) : ℝ :=
  analyticSize a t * (analyticG a t - 1 / 2)

theorem shellDepth_succ (a : ℕ) :
    shellDepth (a + 1) = shellDepth a * 2 := by
  unfold shellDepth
  calc
    (2 : ℕ) ^ (10 + (a + 1)) = 2 ^ ((10 + a) + 1) :=
      congrArg (fun n : ℕ => (2 : ℕ) ^ n) (Nat.add_assoc 10 a 1).symm
    _ = 2 ^ (10 + a) * 2 := pow_succ (2 : ℕ) (10 + a)

theorem shellDepth_lower_bound (a : ℕ) : a + 1 ≤ shellDepth a := by
  induction a with
  | zero => norm_num [shellDepth]
  | succ a ih =>
      rw [shellDepth_succ]
      omega

theorem analyticSize_lower_bound (a t : ℕ) :
    (a : ℝ) + 1 ≤ analyticSize a t := by
  have hn : a + 1 ≤ shellDepth a + t := by
    have hs := shellDepth_lower_bound a
    omega
  unfold analyticSize
  exact_mod_cast hn

theorem analyticSize_pos (a t : ℕ) : 0 < analyticSize a t := by
  have hb := analyticSize_lower_bound a t
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  linarith

theorem analyticG_pairMean (a t : ℕ) :
    analyticG a t = 1 / 2 +
      paritySign t * (pairMean (analyticSize a t) - 1 / 2) := by
  rw [pairMean_sub_half (analyticSize a t) (analyticSize_pos a t)] <;> rfl

theorem analyticRescaled_eq (a t : ℕ) :
    analyticRescaled a t = paritySign t * scaledDefect (analyticSize a t) := by
  unfold analyticRescaled analyticG scaledDefect
  ring

/-- Quantitative coefficient error, improving as either coordinate increases. -/
theorem analyticRescaled_error (a t : ℕ) :
    |analyticRescaled a t - limitingCt t| ≤ 1 / (analyticSize a t + 1) := by
  rcases scaledDefect_error (analyticSize a t) (analyticSize_pos a t) with
    ⟨hlo, hhi⟩
  have heq : analyticRescaled a t - limitingCt t =
      paritySign t * (scaledDefect (analyticSize a t) - 1 / 4) := by
    rw [analyticRescaled_eq]
    unfold limitingCt
    ring
  have hsign : |paritySign t| = 1 := by
    rcases paritySign_cases t with h | h <;> rw [h] <;> norm_num
  have hnonpos : scaledDefect (analyticSize a t) - 1 / 4 ≤ 0 := by
    linarith
  rw [heq, abs_mul, hsign, one_mul, abs_of_nonpos hnonpos]
  linarith

/-- A single shell-dependent bound controls every tail offset simultaneously. -/
theorem analyticRescaled_error_shell (a t : ℕ) :
    |analyticRescaled a t - limitingCt t| ≤
      1 / ((shellDepth a : ℝ) + 1) := by
  have hdenS : 0 < (shellDepth a : ℝ) + 1 := by positivity
  have hdenN : 0 < analyticSize a t + 1 := by
    have hp := analyticSize_pos a t
    linarith
  have hsize : (shellDepth a : ℝ) + 1 ≤ analyticSize a t + 1 := by
    unfold analyticSize
    simp only [Nat.cast_add]
    have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hbound : 1 / (analyticSize a t + 1) ≤
      1 / ((shellDepth a : ℝ) + 1) := by
    apply (div_le_div_iff₀ hdenN hdenS).mpr
    simpa only [one_mul] using hsize
  exact le_trans (analyticRescaled_error a t) hbound

/-- Explicit epsilon proof, uniformly over every tail t ≥ Q. -/
theorem analytic_scaled_uniform_limit (Q : ℕ) :
    UniformTailLimit Q analyticRescaled limitingCt := by
  intro eps heps
  obtain ⟨A, hA⟩ := exists_nat_gt (1 / eps)
  refine ⟨A, ?_⟩
  intro a ha t ht
  have hAa : (A : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsize := analyticSize_lower_bound a t
  have hden : 0 < analyticSize a t + 1 := by
    have hp := analyticSize_pos a t
    linarith
  have hinv : 1 / eps < analyticSize a t + 1 := by
    linarith
  have hmul : 1 < (analyticSize a t + 1) * eps :=
    (div_lt_iff₀ heps).mp hinv
  have hsmall : 1 / (analyticSize a t + 1) < eps := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  exact lt_of_le_of_lt (analyticRescaled_error a t) hsmall

/--
A genuine digit observable may track the analytic family. This does not
identify the analytic family itself with a finite-window observation.
-/
def UniformAnalyticTracking (Q : ℕ) (H : ℕ → ℕ → ℝ) : Prop :=
  UniformTailLimit Q (fun a t => H a t - analyticRescaled a t) (fun _ => 0)

theorem uniform_tracking_gives_coefficient_limit
    (Q : ℕ) (H : ℕ → ℕ → ℝ)
    (htracking : UniformAnalyticTracking Q H) :
    UniformTailLimit Q H limitingCt := by
  intro eps heps
  have heps2 : 0 < eps / 2 := by linarith
  rcases htracking (eps / 2) heps2 with ⟨A, hA⟩
  rcases analytic_scaled_uniform_limit Q (eps / 2) heps2 with ⟨B, hB⟩
  refine ⟨max A B, ?_⟩
  intro a ha t ht
  have hAa : A ≤ a := le_trans (le_max_left A B) ha
  have hBa : B ≤ a := le_trans (le_max_right A B) ha
  have hnear : |H a t - analyticRescaled a t| < eps / 2 := by
    simpa only [sub_zero] using hA a hAa t ht
  have hcoef := hB a hBa t ht
  calc
    |H a t - limitingCt t| =
        |(H a t - analyticRescaled a t) +
          (analyticRescaled a t - limitingCt t)| := by
            congr 1
            ring
    _ ≤ |H a t - analyticRescaled a t| +
          |analyticRescaled a t - limitingCt t| := abs_add_le _ _
    _ < eps / 2 + eps / 2 := add_lt_add hnear hcoef
    _ = eps := by ring

theorem uniform_coefficient_limit_gives_tracking
    (Q : ℕ) (H : ℕ → ℕ → ℝ)
    (hlimit : UniformTailLimit Q H limitingCt) :
    UniformAnalyticTracking Q H := by
  intro eps heps
  have heps2 : 0 < eps / 2 := by linarith
  rcases hlimit (eps / 2) heps2 with ⟨A, hA⟩
  rcases analytic_scaled_uniform_limit Q (eps / 2) heps2 with ⟨B, hB⟩
  refine ⟨max A B, ?_⟩
  intro a ha t ht
  have hAa : A ≤ a := le_trans (le_max_left A B) ha
  have hBa : B ≤ a := le_trans (le_max_right A B) ha
  have hnear := hA a hAa t ht
  have hcoef : |limitingCt t - analyticRescaled a t| < eps / 2 := by
    rw [abs_sub_comm]
    exact hB a hBa t ht
  simp only [sub_zero]
  calc
    |H a t - analyticRescaled a t| =
        |(H a t - limitingCt t) +
          (limitingCt t - analyticRescaled a t)| := by
            congr 1
            ring
    _ ≤ |H a t - limitingCt t| +
          |limitingCt t - analyticRescaled a t| := abs_add_le _ _
    _ < eps / 2 + eps / 2 := add_lt_add hnear hcoef
    _ = eps := by ring

theorem uniformAnalyticTracking_iff_coefficient_limit
    (Q : ℕ) (H : ℕ → ℕ → ℝ) :
    UniformAnalyticTracking Q H ↔ UniformTailLimit Q H limitingCt :=
  ⟨uniform_tracking_gives_coefficient_limit Q H,
    uniform_coefficient_limit_gives_tracking Q H⟩

end ANCHOPI.PartA

namespace ANCHOPI.Closure

open AWPIWordAnchor
open ANCHOPI.PartA
open ANCHOPI.PartB
open ANCHOPI.ActualPi

/-- The semantic pi frontier, expressed through the derived analytic family. -/
def ActualPiAnalyticTracking : Prop :=
  ∃ H : ℕ → ℕ → ℝ,
    FiniteObservations actualPiDigits H ∧ UniformAnalyticTracking 0 H

theorem actualPiAnalyticTracking_iff_ctTracking :
    ActualPiAnalyticTracking ↔ ActualPiCtTracking := by
  constructor
  · rintro ⟨H, hfinite, htracking⟩
    exact ⟨H, hfinite, uniform_tracking_gives_coefficient_limit 0 H htracking⟩
  · rintro ⟨H, hfinite, hlimit⟩
    exact ⟨H, hfinite, uniform_coefficient_limit_gives_tracking 0 H hlimit⟩

theorem actual_pi_nonnormal_of_analytic_tracking
    (H : ℕ → ℕ → ℝ)
    (hfinite : FiniteObservations actualPiDigits H)
    (htracking : UniformAnalyticTracking 0 H) :
    ¬ normal actualPiDigits := by
  apply ACTUAL_PI_CT_A_TIER_CLOSURE
  exact ⟨H, hfinite, uniform_tracking_gives_coefficient_limit 0 H htracking⟩

theorem ACTUAL_PI_ANALYTIC_TRACKING_CLOSURE :
    ActualPiAnalyticTracking → ¬ normal actualPiDigits := by
  intro htracking
  exact ACTUAL_PI_CT_A_TIER_CLOSURE
    (actualPiAnalyticTracking_iff_ctTracking.mp htracking)

end ANCHOPI.Closure
