import PiCt.Instance

/-!
Actual binary words and their exact finite frequencies.
The pi sequence is read from the anchored representative at 1. No
normality or frequency identification is assumed.
-/

open Filter
open scoped Topology

namespace PiCt.BinaryWords

noncomputable def bit (x : ℝ) (n : ℕ) : Bool := by
  classical
  exact decide ((1 / 2 : ℝ) ≤ Int.fract ((2 : ℝ) ^ n * x))

noncomputable def piBits (n : ℕ) : Bool := bit ((Pi.toFun 1).re) n

theorem piBits_eq (n : ℕ) : piBits n = bit Real.pi n := by
  unfold piBits
  rw [PI_ANCHOR]
  simp

def blockCode (b : ℕ → Bool) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * blockCode b n k + if b (n + k) then 1 else 0

noncomputable def freq (b : ℕ → Bool) (N len j : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, if blockCode b n len = j then (1 : ℝ) else 0) / (N : ℝ)

theorem root_freq (b : ℕ → Bool) (N : ℕ) (hN : 0 < N) :
    freq b N 0 0 = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [freq, blockCode, hn]

private theorem indicator_split (k j : ℕ) (v : Bool) :
    (if k = j then (1 : ℝ) else 0) =
      (if 2 * k + (if v then 1 else 0) = 2 * j then (1 : ℝ) else 0) +
      (if 2 * k + (if v then 1 else 0) = 2 * j + 1 then (1 : ℝ) else 0) := by
  cases v <;> simp <;> omega

theorem split_freq (b : ℕ → Bool) (N len j : ℕ) :
    freq b N len j =
      freq b N (len + 1) (2 * j) + freq b N (len + 1) (2 * j + 1) := by
  unfold freq
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact indicator_split (blockCode b n len) j (b (n + len))

theorem blockCode4_zero_iff (b : ℕ → Bool) (n : ℕ) :
    blockCode b n 4 = 0 ↔
      b n = false ∧ b (n + 1) = false ∧ b (n + 2) = false ∧ b (n + 3) = false := by
  cases h0 : b n <;> cases h1 : b (n + 1) <;>
    cases h2 : b (n + 2) <;> cases h3 : b (n + 3) <;>
    simp [blockCode, h0, h1, h2, h3]

theorem blockCode4_fifteen_iff (b : ℕ → Bool) (n : ℕ) :
    blockCode b n 4 = 15 ↔
      b n = true ∧ b (n + 1) = true ∧ b (n + 2) = true ∧ b (n + 3) = true := by
  cases h0 : b n <;> cases h1 : b (n + 1) <;>
    cases h2 : b (n + 2) <;> cases h3 : b (n + 3) <;>
    simp [blockCode, h0, h1, h2, h3]

theorem freq_nonneg (b : ℕ → Bool) (N len j : ℕ) : 0 ≤ freq b N len j := by
  unfold freq
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro n hn
    split_ifs <;> norm_num
  · exact Nat.cast_nonneg N

theorem freq_le_one (b : ℕ → Bool) (N len j : ℕ) : freq b N len j ≤ 1 := by
  by_cases hN : N = 0
  · simp [freq, hN]
  have hp : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  unfold freq
  apply (div_le_one hp).2
  calc
    (∑ n ∈ Finset.range N, if blockCode b n len = j then (1 : ℝ) else 0)
        ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs <;> norm_num
    _ = (N : ℝ) := by simp

def BinaryNormal (b : ℕ → Bool) : Prop :=
  ∀ len j : ℕ, j < 2 ^ len →
    Tendsto (fun N : ℕ => freq b N len j) atTop (𝓝 (1 / (2 : ℝ) ^ len))

end PiCt.BinaryWords
