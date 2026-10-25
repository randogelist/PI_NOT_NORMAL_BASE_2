import PiCt.BinaryWords

/-! Normal sequences contain every finite word, including arbitrarily long
even-aligned alternating runs. Alignment is obtained with a finite trap word,
without assuming a separate normality theorem for arithmetic subsequences. -/

open Filter
open scoped Topology

namespace PiCt.WordOccurrence

open BinaryWords

theorem blockCode_lt (b : ℕ → Bool) (n len : ℕ) :
    blockCode b n len < 2 ^ len := by
  induction len with
  | zero => simp [blockCode]
  | succ len ih =>
      cases hb : b (n + len) <;> simp [blockCode, hb, pow_succ] <;> omega

theorem blockCode_eq_imp_bits (b c : ℕ → Bool) (n m len : ℕ) :
    blockCode b n len = blockCode c m len →
      ∀ k < len, b (n + k) = c (m + k) := by
  induction len with
  | zero => intro h k hk; omega
  | succ len ih =>
      intro h
      have hp : blockCode b n len = blockCode c m len := by
        cases hb : b (n + len) <;> cases hc : c (m + len) <;>
          simp [blockCode, hb, hc] at h <;> omega
      have hl : b (n + len) = c (m + len) := by
        cases hb : b (n + len) <;> cases hc : c (m + len) <;>
          simp_all [blockCode]
      intro k hk
      by_cases hkl : k < len
      · exact ih hp k hkl
      · have he : k = len := by omega
        simpa only [he] using hl

theorem normal_code_occurs {b : ℕ → Bool} (hn : BinaryNormal b)
    (len j : ℕ) (hj : j < 2 ^ len) : ∃ n, blockCode b n len = j := by
  by_contra h
  push Not at h
  have hz (N : ℕ) : freq b N len j = 0 := by simp [freq, h]
  have ht : Tendsto (fun N : ℕ => freq b N len j) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have he := tendsto_nhds_unique (hn len j hj) ht
  have hp : (0 : ℝ) < 1 / (2 : ℝ) ^ len := by positivity
  linarith

theorem normal_word_occurs {b : ℕ → Bool} (hn : BinaryNormal b)
    (w : ℕ → Bool) (len : ℕ) : ∃ n, ∀ k < len, b (n + k) = w k := by
  obtain ⟨n, h⟩ := normal_code_occurs hn len (blockCode w 0 len) (blockCode_lt w 0 len)
  refine ⟨n, ?_⟩
  simpa only [Nat.zero_add] using blockCode_eq_imp_bits b w n 0 len h

/-- The finite word `(01)^r 0 (01)^r` has copies starting at opposite parities. -/
def trapWord (r k : ℕ) : Bool :=
  if k < 2 * r + 1 then decide (k % 2 = 1)
  else decide ((k - (2 * r + 1)) % 2 = 1)

theorem trapWord_first_zero (r k : ℕ) (hk : k < r) : trapWord r (2 * k) = false := by
  simp [trapWord, show 2 * k < 2 * r + 1 by omega]

theorem trapWord_first_one (r k : ℕ) (hk : k < r) : trapWord r (2 * k + 1) = true := by
  simp [trapWord, show 2 * k + 1 < 2 * r + 1 by omega, Nat.add_mod]

theorem trapWord_second_zero (r k : ℕ) : trapWord r (2 * r + 1 + 2 * k) = false := by
  simp [trapWord, show ¬ 2 * r + 1 + 2 * k < 2 * r + 1 by omega]

theorem trapWord_second_one (r k : ℕ) : trapWord r (2 * r + 1 + (2 * k + 1)) = true := by
  simp [trapWord, show ¬ 2 * r + 1 + (2 * k + 1) < 2 * r + 1 by omega,
    Nat.add_mod]

theorem normal_even_alternating {b : ℕ → Bool} (hn : BinaryNormal b) (r : ℕ) :
    ∃ j, ∀ k < r, b (2 * (j + k)) = false ∧ b (2 * (j + k) + 1) = true := by
  obtain ⟨n, hw⟩ := normal_word_occurs hn (trapWord r) (4 * r + 1)
  by_cases heven : n % 2 = 0
  · have halign : 2 * (n / 2) = n := by omega
    refine ⟨n / 2, ?_⟩
    intro k hk
    constructor
    · rw [show 2 * (n / 2 + k) = n + 2 * k by omega]
      exact (hw (2 * k) (by omega)).trans (trapWord_first_zero r k hk)
    · rw [show 2 * (n / 2 + k) + 1 = n + (2 * k + 1) by omega]
      exact (hw (2 * k + 1) (by omega)).trans (trapWord_first_one r k hk)
  · have halign : 2 * ((n + 2 * r + 1) / 2) = n + 2 * r + 1 := by omega
    refine ⟨(n + 2 * r + 1) / 2, ?_⟩
    intro k hk
    constructor
    · rw [show 2 * ((n + 2 * r + 1) / 2 + k) = n + (2 * r + 1 + 2 * k) by omega]
      exact (hw (2 * r + 1 + 2 * k) (by omega)).trans (trapWord_second_zero r k)
    · rw [show 2 * ((n + 2 * r + 1) / 2 + k) + 1 =
          n + (2 * r + 1 + (2 * k + 1)) by omega]
      exact (hw (2 * r + 1 + (2 * k + 1)) (by omega)).trans (trapWord_second_one r k)

end PiCt.WordOccurrence
