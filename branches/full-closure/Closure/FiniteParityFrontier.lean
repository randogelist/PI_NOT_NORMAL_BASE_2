import Closure.ActualPiATier

/-!
Source-reviewed extension of the v0_6_0 closure. No compiler was run for this
file. The statements do not assert an inhabitant for the actual pi frontier.
-/

namespace ANCHOPI.Frontier

open AWPIWordAnchor
open ANCHOPI.PartA
open ANCHOPI.PartB
open ANCHOPI.ActualPi
open ANCHOPI.Closure

/-- The existing tracking interface, generalized to any binary stream. -/
def CtTracking (x : bitstream) : Prop :=
  ∃ H : ℕ → ℕ → ℝ,
    FiniteObservations x H ∧ UniformTailLimit 0 H limitingCt

/-- A fixed block width distinguishes the two possible starting parities. -/
def FiniteParitySeparation (x : bitstream) : Prop :=
  ∃ width : ℕ, ∀ origin dest : ℕ,
    «matches» x (List.ofFn (fun j : Fin width => x (origin + j.1))) dest = true →
      paritySign dest = paritySign origin

/-- One scale with error strictly below 1/4 already suffices. -/
def OneScaleCtApproximation (x : bitstream) : Prop :=
  ∃ H : ℕ → ℕ → ℝ,
    FiniteObservations x H ∧
    ∃ a : ℕ, ∀ t : ℕ, |H a t - limitingCt t| < (1 : ℝ) / 4

theorem oneScaleCtApproximation_of_tracking (x : bitstream)
    (htrack : CtTracking x) : OneScaleCtApproximation x := by
  rcases htrack with ⟨H, hfinite, huniform⟩
  rcases huniform ((1 : ℝ) / 4) (by norm_num) with ⟨A, hA⟩
  refine ⟨H, hfinite, A, ?_⟩
  intro t
  exact hA A (le_rfl) t (Nat.zero_le t)

theorem finiteParitySeparation_of_oneScale (x : bitstream)
    (happrox : OneScaleCtApproximation x) : FiniteParitySeparation x := by
  rcases happrox with ⟨H, hfinite, A, herr⟩
  rcases hfinite A with ⟨width, hlocal⟩
  refine ⟨width, ?_⟩
  intro origin dest hmatch
  have heq : H A dest = H A origin := hlocal origin dest hmatch
  have eo := abs_lt.mp (herr origin)
  have ed := abs_lt.mp (herr dest)
  rw [heq] at ed
  unfold limitingCt at eo ed
  rcases paritySign_cases dest with hd | hd
  · rcases paritySign_cases origin with ho | ho
    · exact hd.trans ho.symm
    · rw [hd] at ed
      rw [ho] at eo
      rcases eo with ⟨eolo, eohi⟩
      rcases ed with ⟨edlo, edhi⟩
      exfalso
      linarith
  · rcases paritySign_cases origin with ho | ho
    · rw [hd] at ed
      rw [ho] at eo
      rcases eo with ⟨eolo, eohi⟩
      rcases ed with ⟨edlo, edhi⟩
      exfalso
      linarith
    · exact hd.trans ho.symm

/--
Once parity can be read locally, the exact coefficient itself is a legitimate
finite observation; a shell limit is no longer needed to construct a witness.
-/
theorem exact_observation_of_finiteParitySeparation (x : bitstream)
    (hsep : FiniteParitySeparation x) :
    FiniteObservations x (fun _ t => limitingCt t) := by
  rcases hsep with ⟨width, hlocal⟩
  intro a
  refine ⟨width, ?_⟩
  intro origin dest hmatch
  change limitingCt dest = limitingCt origin
  unfold limitingCt
  rw [hlocal origin dest hmatch]

theorem exact_coefficient_uniform :
    UniformTailLimit 0 (fun _ t => limitingCt t) limitingCt := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro a ha t ht
  simpa using heps

theorem tracking_of_finiteParitySeparation (x : bitstream)
    (hsep : FiniteParitySeparation x) : CtTracking x := by
  exact ⟨(fun _ t => limitingCt t),
    exact_observation_of_finiteParitySeparation x hsep,
    exact_coefficient_uniform⟩

theorem ctTracking_iff_finiteParitySeparation (x : bitstream) :
    CtTracking x ↔ FiniteParitySeparation x := by
  constructor
  · intro htrack
    exact finiteParitySeparation_of_oneScale x
      (oneScaleCtApproximation_of_tracking x htrack)
  · exact tracking_of_finiteParitySeparation x

theorem oneScaleCtApproximation_iff_finiteParitySeparation (x : bitstream) :
    OneScaleCtApproximation x ↔ FiniteParitySeparation x := by
  constructor
  · exact finiteParitySeparation_of_oneScale x
  · intro hsep
    exact oneScaleCtApproximation_of_tracking x
      (tracking_of_finiteParitySeparation x hsep)

theorem ctTracking_iff_exact_observation (x : bitstream) :
    CtTracking x ↔ FiniteObservations x (fun _ t => limitingCt t) := by
  constructor
  · intro htrack
    exact exact_observation_of_finiteParitySeparation x
      ((ctTracking_iff_finiteParitySeparation x).mp htrack)
  · intro hfinite
    exact ⟨(fun _ t => limitingCt t), hfinite, exact_coefficient_uniform⟩

/-- Direct use of the previously proved opposite-parity occurrence lemma. -/
theorem not_normal_of_finiteParitySeparation (x : bitstream)
    (hsep : FiniteParitySeparation x) : ¬ normal x := by
  intro hnormal
  rcases hsep with ⟨width, hlocal⟩
  let w : word := List.ofFn (fun j : Fin width => x (0 + j.1))
  rcases normal_word_opposite_parities x w 0 0 hnormal with
    ⟨s, u, hs, hu, hopp, hms, hmu⟩
  have hsSign : paritySign s = paritySign 0 := hlocal 0 s hms
  have huSign : paritySign u = paritySign 0 := hlocal 0 u hmu
  simp only [Nat.zero_add] at hopp
  rw [hsSign, huSign] at hopp
  norm_num [paritySign] at hopp

/-- Exact specialization: the pi frontier is a finite parity decoder. -/
theorem actualPiCtTracking_iff_finiteParitySeparation :
    ActualPiCtTracking ↔ FiniteParitySeparation actualPiDigits := by
  change CtTracking actualPiDigits ↔ FiniteParitySeparation actualPiDigits
  exact ctTracking_iff_finiteParitySeparation actualPiDigits

theorem actualPiCtTracking_iff_oneScaleCtApproximation :
    ActualPiCtTracking ↔ OneScaleCtApproximation actualPiDigits := by
  rw [actualPiCtTracking_iff_finiteParitySeparation,
    oneScaleCtApproximation_iff_finiteParitySeparation]

theorem actualPiCtTracking_iff_exact_observation :
    ActualPiCtTracking ↔
      FiniteObservations actualPiDigits (fun _ t => limitingCt t) := by
  change CtTracking actualPiDigits ↔
    FiniteObservations actualPiDigits (fun _ t => limitingCt t)
  exact ctTracking_iff_exact_observation actualPiDigits

theorem ACTUAL_PI_FINITE_PARITY_CLOSURE :
    FiniteParitySeparation actualPiDigits → ¬ normal actualPiDigits :=
  not_normal_of_finiteParitySeparation actualPiDigits

theorem ACTUAL_PI_FINITE_PARITY_FRONTIER_ATLAS :
    (ActualPiCtTracking ↔ FiniteParitySeparation actualPiDigits) ∧
    (ActualPiCtTracking ↔ OneScaleCtApproximation actualPiDigits) ∧
    (ActualPiCtTracking ↔
      FiniteObservations actualPiDigits (fun _ t => limitingCt t)) ∧
    (FiniteParitySeparation actualPiDigits → ¬ normal actualPiDigits) := by
  exact ⟨actualPiCtTracking_iff_finiteParitySeparation,
    actualPiCtTracking_iff_oneScaleCtApproximation,
    actualPiCtTracking_iff_exact_observation,
    ACTUAL_PI_FINITE_PARITY_CLOSURE⟩

end ANCHOPI.Frontier
