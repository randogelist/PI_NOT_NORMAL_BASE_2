import AWPIWordAnchor.CW01_Words

namespace AWPIWordAnchor

noncomputable def average_on (sample : ℕ → ℕ) (f : ℕ → ℝ) (M : ℕ) : ℝ :=
  rsum (fun j => f (sample j)) M / (M : ℝ)

noncomputable def frequency_on (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (M : ℕ) : ℝ :=
  average_on sample (fun n => bitR («matches» x w n)) M

def ordinary_starts (j : ℕ) : ℕ := j

def even_starts (j : ℕ) : ℕ := 2 * j

noncomputable def frequency := frequency_on ordinary_starts

def next_match (x : bitstream) (w : word) (b : Bool) (n : ℕ) : Bool :=
  x (n + w.length) == b

noncomputable def next_frequency_on (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) : ℝ :=
  average_on sample (fun n => bitR (next_match x w b n)) M

noncomputable def joint_frequency_on (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) : ℝ :=
  average_on sample
    (fun n => bitR («matches» x w n) * bitR (next_match x w b n)) M

noncomputable def extension_defect_on (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) : ℝ :=
  frequency_on sample x (w ++ [b]) M - frequency_on sample x w M / 2

noncomputable def marginal_defect_on (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) : ℝ :=
  1 / 2 - next_frequency_on sample x w b M

noncomputable def covariance_on (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) : ℝ :=
  joint_frequency_on sample x w b M -
    frequency_on sample x w M * next_frequency_on sample x w b M

theorem occurrence_product (x : bitstream) (w : word) (b : Bool) (n : ℕ) :
    bitR («matches» x (w ++ [b]) n) =
      bitR («matches» x w n) * bitR (next_match x w b n) := by
  rw [matches_append]
  have hsingle : «matches» x [b] (n + w.length) = next_match x w b n := by
    simp [«matches», next_match]
  rw [hsingle]
  cases h₁ : «matches» x w n <;>
    cases h₂ : next_match x w b n <;>
      simp [bitR, h₁, h₂]

theorem joint_is_extension (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) :
    joint_frequency_on sample x w b M =
      frequency_on sample x (w ++ [b]) M := by
  unfold joint_frequency_on frequency_on average_on
  have hsum :
      rsum (fun j => bitR («matches» x w (sample j)) *
        bitR (next_match x w b (sample j))) M =
      rsum (fun j => bitR («matches» x (w ++ [b]) (sample j))) M := by
    apply rsum_ext
    intro j
    exact (occurrence_product x w b (sample j)).symm
  rw [hsum]

theorem extension_covariance_identity (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (M : ℕ) :
    extension_defect_on sample x w b M =
      covariance_on sample x w b M -
        marginal_defect_on sample x w b M * frequency_on sample x w M := by
  unfold extension_defect_on covariance_on marginal_defect_on
  rw [joint_is_extension]
  ring

theorem frequency_on_bounds (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (M : ℕ) (hM : 0 < M) :
    0 ≤ frequency_on sample x w M ∧ frequency_on sample x w M ≤ 1 := by
  have hsum := rsum_bit_bounds (fun j => «matches» x w (sample j)) M
  have hden : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  unfold frequency_on average_on
  constructor
  · exact div_nonneg hsum.1 (le_of_lt hden)
  · apply (div_le_iff₀ hden).2
    simpa using hsum.2

def normal_on (sample : ℕ → ℕ) (x : bitstream) : Prop :=
  ∀ w : word, tends_to (frequency_on sample x w) (fair_mass w)

/-- The empty word is included; its frequency is identically 1 for M > 0. -/
def normal (x : bitstream) : Prop := normal_on ordinary_starts x

theorem empty_word_frequency (sample : ℕ → ℕ) (x : bitstream)
    (M : ℕ) (hM : 0 < M) : frequency_on sample x [] M = 1 := by
  unfold frequency_on average_on
  have hsum : rsum (fun j => bitR («matches» x [] (sample j))) M = (M : ℝ) := by
    simpa [«matches», bitR] using rsum_one M
  rw [hsum]
  have hne : (M : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hM)
  field_simp

theorem empty_word_limit (sample : ℕ → ℕ) (x : bitstream) :
    tends_to (frequency_on sample x []) (fair_mass []) := by
  intro eps heps
  refine ⟨1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  rw [empty_word_frequency sample x n hnpos]
  simp [fair_mass]
  exact heps

theorem normal_nonempty_equivalence (x : bitstream) :
    normal x ↔
      (∀ w : word, w ≠ [] → tends_to (frequency x w) (fair_mass w)) := by
  constructor
  · intro h w hw
    exact h w
  · intro h w
    cases w with
    | nil => exact empty_word_limit ordinary_starts x
    | cons b rest =>
        apply h
        simp

theorem normal_on_extension_vanishes (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool) (hnormal : normal_on sample x) :
    tends_to (extension_defect_on sample x w b) 0 := by
  have hprefix := hnormal w
  have hextension := hnormal (w ++ [b])
  rw [fair_mass_append_bit] at hextension
  unfold extension_defect_on
  exact tends_to_extension_difference hprefix hextension

theorem normal_on_extension_anchor (sample : ℕ → ℕ) (x : bitstream)
    (w : word) (b : Bool)
    (hbad : negative_often (extension_defect_on sample x w b)) :
    ¬ normal_on sample x := by
  intro hnormal
  exact zero_limit_excludes_negative_often
    (normal_on_extension_vanishes sample x w b hnormal) hbad

/-- Supplied theorem interface, not an axiom and not proved in this package. -/
def EvenStartBridge : Prop :=
  ∀ x, normal x → normal_on even_starts x

theorem even_start_anchor_with_bridge (hbridge : EvenStartBridge)
    (x : bitstream) (w : word) (b : Bool)
    (hbad : negative_often (extension_defect_on even_starts x w b)) :
    ¬ normal x := by
  intro hnormal
  exact normal_on_extension_anchor even_starts x w b hbad (hbridge x hnormal)

end AWPIWordAnchor
