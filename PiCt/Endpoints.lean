import PiCt.Dyadic
import PiCt.Representative

open Filter
open scoped Topology

namespace PiCt

/-- The frozen parity orientation applied to the actual analytic readout. -/
noncomputable def piReadout (a t : ℕ) : ℝ :=
  1 / 2 + (-1 : ℝ) ^ t *
    (ComplexRepresentative.splitReadout (scale a + t) - 1 / 2)

theorem piReadout_eq_G (a t : ℕ) : piReadout a t = G a t := by
  have hn := scale_pos a
  have hm : 0 < scale a + (t : ℝ) := by positivity
  unfold piReadout G
  rw [ComplexRepresentative.splitReadout_eq_half_add_delta hm]
  ring

/-- The coefficient limit obtained from the genuine pi-anchored representative. -/
theorem PI_REPRESENTATIVE_CT (t : ℕ) :
    Tendsto (fun a : ℕ => scale a * (piReadout a t - 1 / 2))
      atTop (𝓝 ((-1 : ℝ) ^ t / 4)) := by
  simp only [piReadout_eq_G]
  exact C_tendsto t

theorem PI_REPRESENTATIVE_CT_UNIQUE (t : ℕ) :
    ∃! c : ℝ, Tendsto (fun a : ℕ => scale a * (piReadout a t - 1 / 2))
      atTop (𝓝 c) := by
  simpa only [piReadout_eq_G] using C_exists_unique t

theorem PI_REPRESENTATIVE_REMAINDER (a t : ℕ) :
    |piReadout a t - 1 / 2 - C t / scale a| ≤
      ((t : ℝ) + 2) / (4 * scale a ^ 2) := by
  rw [piReadout_eq_G]
  exact G_remainder a t

theorem PI_REPRESENTATIVE_CAUCHY {a b : ℕ} (hab : a ≤ b) (t : ℕ) :
    |scale b * (piReadout b t - 1 / 2) - scale a * (piReadout a t - 1 / 2)| ≤
      ((t : ℝ) + 2) / (4 * scale a) := by
  simp only [piReadout_eq_G]
  exact coefficient_cauchy hab t

/-- A nonzero scaled coefficient coexists with an unscaled limit of one half. -/
theorem PI_REPRESENTATIVE_UNSCALED_LIMIT (t : ℕ) :
    Tendsto (fun a : ℕ => piReadout a t) atTop (𝓝 (1 / 2)) := by
  simpa only [piReadout_eq_G] using G_tendsto_half t

end PiCt
