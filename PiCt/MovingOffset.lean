import PiCt.Instance

/-! The coefficient profile when the offset grows with the dyadic scale.
The frozen fixed-offset coefficient remains unchanged. -/

open Filter
open scoped Topology

namespace PiCt.MovingOffset

theorem profile_bounds {N t : ℝ} (hN : 0 < N) (ht : 0 ≤ t) :
    0 ≤ N / (4 * (N + t)) - N * delta (N + t) ∧
      N / (4 * (N + t)) - N * delta (N + t) ≤ 1 / (2 * N) := by
  have hM : 0 < N + t := by linarith
  have he := scaled_bounds hM (le_refl (0 : ℝ))
  simp only [add_zero] at he
  have hf0 : 0 ≤ N / (N + t) := le_of_lt (div_pos hN hM)
  have hf1 : N / (N + t) ≤ 1 := (div_le_one hM).2 (by linarith)
  have hrecip : 1 / (2 * (N + t)) ≤ 1 / (2 * N) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have heq : N / (4 * (N + t)) - N * delta (N + t) =
      (N / (N + t)) * (1 / 4 - (N + t) * delta (N + t)) := by
    field_simp
  rw [heq]
  constructor
  · exact mul_nonneg hf0 he.1
  · calc
      (N / (N + t)) * (1 / 4 - (N + t) * delta (N + t))
          ≤ 1 * (1 / 4 - (N + t) * delta (N + t)) :=
        mul_le_mul_of_nonneg_right hf1 he.1
      _ ≤ 1 / (2 * (N + t)) := by
        simp only [one_mul]
        calc
          1 / 4 - (N + t) * delta (N + t) ≤ (0 + 2) / (4 * (N + t)) := he.2
          _ = 1 / (2 * (N + t)) := by
            field_simp
            norm_num
      _ ≤ 1 / (2 * N) := hrecip

theorem relative_offset_limit {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun a : ℕ => scale a * delta (scale a + u * scale a))
      atTop (𝓝 (1 / (4 * (1 + u)))) := by
  have hc (a : ℕ) : scale a / (4 * (scale a + u * scale a)) =
      1 / (4 * (1 + u)) := by
    have hN := scale_pos a
    have hu1 : 0 < 1 + u := by linarith
    field_simp
  have hb (a : ℕ) := profile_bounds (scale_pos a) (mul_nonneg hu (le_of_lt (scale_pos a)))
  have herr : Tendsto (fun a : ℕ => 1 / (2 * scale a)) atTop (𝓝 (0 : ℝ)) := by
    have h := inverse_scale_tendsto.div_const 2
    convert h using 1 <;> simp [div_mul_eq_div_div]
    ext a
    ring
  have hgap : Tendsto
      (fun a : ℕ => 1 / (4 * (1 + u)) - scale a * delta (scale a + u * scale a))
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero
    · intro a
      simpa only [hc a] using (hb a).1
    · intro a
      simpa only [hc a] using (hb a).2
    · exact herr
  have hcst : Tendsto (fun _a : ℕ => 1 / (4 * (1 + u)))
      atTop (𝓝 (1 / (4 * (1 + u)))) := tendsto_const_nhds
  simpa using hcst.sub hgap

/-- An offset halfway across the growing shell gives 1/6, not 1/4. -/
theorem half_shell_limit :
    Tendsto (fun a : ℕ => scale a * delta (scale a + (1 / 2 : ℝ) * scale a))
      atTop (𝓝 (1 / 6 : ℝ)) := by
  have h := relative_offset_limit (u := (1 / 2 : ℝ)) (by norm_num)
  norm_num at h
  exact h

end PiCt.MovingOffset
