import PiCt.BinaryWords

/-! Exact four-bit frequency identities for actual binary sequences. -/

open Filter
open scoped Topology

namespace PiCt
namespace RunFrequency

open BinaryWords

/-- Difference of the two child-word frequencies at a node of the digit tree. -/
noncomputable def haar (b : ℕ → Bool) (N len j : ℕ) : ℝ :=
  freq b N (len + 1) (2 * j) - freq b N (len + 1) (2 * j + 1)

noncomputable def zeroRun (b : ℕ → Bool) (N : ℕ) : ℝ := freq b N 4 0
noncomputable def oneRun (b : ℕ → Bool) (N : ℕ) : ℝ := freq b N 4 15

/-- The six actual digit-tree imbalances controlling the combined run excess. -/
noncomputable def runDefect (b : ℕ → Bool) (N : ℕ) : ℝ :=
  haar b N 1 0 - haar b N 1 1 +
    2 * (haar b N 2 0 - haar b N 2 3) +
    4 * (haar b N 3 0 - haar b N 3 7)

noncomputable def pairExcess (b : ℕ → Bool) (N : ℕ) : ℝ :=
  zeroRun b N + oneRun b N - 1 / 8

theorem zeroRun_identity (b : ℕ → Bool) (N : ℕ) (hN : 0 < N) :
    zeroRun b N - 1 / 16 =
      haar b N 0 0 / 16 + haar b N 1 0 / 8 +
      haar b N 2 0 / 4 + haar b N 3 0 / 2 := by
  have h0 := root_freq b N hN
  have h1 := split_freq b N 0 0
  have h2 := split_freq b N 1 0
  have h3 := split_freq b N 2 0
  have h4 := split_freq b N 3 0
  norm_num at h1 h2 h3 h4
  unfold zeroRun haar
  norm_num
  linarith

theorem oneRun_identity (b : ℕ → Bool) (N : ℕ) (hN : 0 < N) :
    oneRun b N - 1 / 16 =
      -(haar b N 0 0 / 16) - haar b N 1 1 / 8 -
      haar b N 2 3 / 4 - haar b N 3 7 / 2 := by
  have h0 := root_freq b N hN
  have h1 := split_freq b N 0 0
  have h2 := split_freq b N 1 1
  have h3 := split_freq b N 2 3
  have h4 := split_freq b N 3 7
  norm_num at h1 h2 h3 h4
  unfold oneRun haar
  norm_num
  linarith

/-- Root single-bit imbalance cancels exactly from the combined frequency. -/
theorem runDefect_identity (b : ℕ → Bool) (N : ℕ) (hN : 0 < N) :
    runDefect b N = 8 * pairExcess b N := by
  have h0 := zeroRun_identity b N hN
  have h1 := oneRun_identity b N hN
  unfold runDefect pairExcess
  linarith

theorem pair_frequency_identity (b : ℕ → Bool) (N : ℕ) (hN : 0 < N) :
    zeroRun b N + oneRun b N = 1 / 8 + runDefect b N / 8 := by
  have h := runDefect_identity b N hN
  unfold pairExcess at h
  linarith

def dyadicLength (a : ℕ) : ℕ := 2 ^ (10 + a)

theorem dyadicLength_pos (a : ℕ) : 0 < dyadicLength a := by
  unfold dyadicLength
  positivity

theorem dyadicLength_cast (a : ℕ) : (dyadicLength a : ℝ) = scale a := by
  simp [dyadicLength, scale]

theorem dyadicLength_tendsto : Tendsto dyadicLength atTop atTop := by
  have h : Tendsto (fun a : ℕ => (2 : ℕ) ^ a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hh := (tendsto_add_atTop_iff_nat 10).mpr h
  change Tendsto (fun a : ℕ => (2 : ℕ) ^ (10 + a)) atTop atTop
  simpa [Nat.add_comm] using hh

noncomputable def dyadicDefect (b : ℕ → Bool) (a : ℕ) : ℝ :=
  runDefect b (dyadicLength a)

/-- This names only the two necessary word-frequency conditions. -/
def ExtremeWordsBalanced (b : ℕ → Bool) : Prop :=
  Tendsto (zeroRun b) atTop (𝓝 (1 / 16)) ∧
  Tendsto (oneRun b) atTop (𝓝 (1 / 16))

theorem normal_extremeWordsBalanced {b : ℕ → Bool} (hn : BinaryNormal b) :
    ExtremeWordsBalanced b := by
  constructor
  · have h := hn 4 0 (by norm_num)
    norm_num at h
    exact h
  · have h := hn 4 15 (by norm_num)
    norm_num at h
    exact h

theorem balanced_dyadicDefect_zero {b : ℕ → Bool} (hb : ExtremeWordsBalanced b) :
    Tendsto (dyadicDefect b) atTop (𝓝 0) := by
  have hz := hb.1.comp dyadicLength_tendsto
  have ho := hb.2.comp dyadicLength_tendsto
  have h := ((hz.add ho).sub_const (1 / 8 : ℝ)).const_mul 8
  have heq (a : ℕ) : dyadicDefect b a =
      8 * (zeroRun b (dyadicLength a) + oneRun b (dyadicLength a) - 1 / 8) :=
    runDefect_identity b (dyadicLength a) (dyadicLength_pos a)
  convert h using 1
  · exact funext heq
  · norm_num

theorem not_balanced_of_defect_limit {b : ℕ → Bool} {d : ℝ} (hd : d ≠ 0)
    (hlim : Tendsto (dyadicDefect b) atTop (𝓝 d)) : ¬ ExtremeWordsBalanced b := by
  intro hb
  exact hd (tendsto_nhds_unique hlim (balanced_dyadicDefect_zero hb))

theorem not_normal_of_defect_limit {b : ℕ → Bool} {d : ℝ} (hd : d ≠ 0)
    (hlim : Tendsto (dyadicDefect b) atTop (𝓝 d)) : ¬ BinaryNormal b := by
  intro hn
  exact not_balanced_of_defect_limit hd hlim (normal_extremeWordsBalanced hn)

/-- No limit existence is needed if a nonzero defect persists at arbitrarily large scales. -/
theorem not_balanced_of_persistent_defect {b : ℕ → Bool} {ε : ℝ} (hε : 0 < ε)
    (hp : ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧ ε ≤ |dyadicDefect b a|) :
    ¬ ExtremeWordsBalanced b := by
  intro hb
  have hzero := balanced_dyadicDefect_zero hb
  have habs : Tendsto (fun a => |dyadicDefect b a|) atTop (𝓝 (0 : ℝ)) := by
    simpa using hzero.abs
  have he := (tendsto_order.mp habs).2 ε hε
  have hf : ∃ᶠ a in atTop, ε ≤ |dyadicDefect b a| := frequently_atTop.mpr hp
  obtain ⟨a, ha, hlt⟩ := (hf.and_eventually he).exists
  linarith

theorem not_normal_of_persistent_defect {b : ℕ → Bool} {ε : ℝ} (hε : 0 < ε)
    (hp : ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧ ε ≤ |dyadicDefect b a|) :
    ¬ BinaryNormal b := by
  intro hn
  exact not_balanced_of_persistent_defect hε hp (normal_extremeWordsBalanced hn)

end RunFrequency
end PiCt
