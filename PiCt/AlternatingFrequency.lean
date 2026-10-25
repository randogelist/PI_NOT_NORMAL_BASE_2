import PiCt.WordOccurrence
import PiCt.RunFrequency

/-!
Actual frequencies of the two alternating words of each fixed length.
The asymptotic deficit hypotheses below are not asserted for pi. In every
closure statement the word length is fixed before the sample size grows.
-/

open Filter
open scoped Topology

namespace PiCt.AlternatingFrequency

open BinaryWords

/-- `false` gives `010101...`; `true` gives `101010...`. -/
def alternating (startsOne : Bool) (k : ℕ) : Bool :=
  if startsOne then decide (k % 2 = 0) else decide (k % 2 = 1)

@[simp] theorem alternating_zero (startsOne : Bool) :
    alternating startsOne 0 = startsOne := by
  cases startsOne <;> simp [alternating]

@[simp] theorem alternating_even (startsOne : Bool) (k : ℕ) :
    alternating startsOne (2 * k) = startsOne := by
  cases startsOne <;> simp [alternating]

@[simp] theorem alternating_odd (startsOne : Bool) (k : ℕ) :
    alternating startsOne (2 * k + 1) = !startsOne := by
  cases startsOne <;> simp [alternating, Nat.add_mod]

/-- A word of length `2*r+1` at an even start contains `r` aligned pairs. -/
theorem code_occurrence_even_pairs (b : ℕ → Bool) (j r : ℕ) (startsOne : Bool)
    (hc : blockCode b (2 * j) (2 * r + 1) =
      blockCode (alternating startsOne) 0 (2 * r + 1)) :
    ∀ k < r, b (2 * (j + k)) = startsOne ∧
      b (2 * (j + k) + 1) = !startsOne := by
  have hw := WordOccurrence.blockCode_eq_imp_bits b
    (alternating startsOne) (2 * j) 0 (2 * r + 1) hc
  intro k hk
  constructor
  · rw [show 2 * (j + k) = 2 * j + 2 * k by omega]
    simpa only [Nat.zero_add, alternating_even] using hw (2 * k) (by omega)
  · rw [show 2 * (j + k) + 1 = 2 * j + (2 * k + 1) by omega]
    simpa only [Nat.zero_add, alternating_odd] using hw (2 * k + 1) (by omega)

/-- At an odd start, the complete even-aligned pairs begin one bit later. -/
theorem code_occurrence_odd_pairs (b : ℕ → Bool) (j r : ℕ) (startsOne : Bool)
    (hc : blockCode b (2 * j + 1) (2 * r + 1) =
      blockCode (alternating startsOne) 0 (2 * r + 1)) :
    ∀ k < r, b (2 * (j + 1 + k)) = !startsOne ∧
      b (2 * (j + 1 + k) + 1) = startsOne := by
  have hw := WordOccurrence.blockCode_eq_imp_bits b
    (alternating startsOne) (2 * j + 1) 0 (2 * r + 1) hc
  intro k hk
  constructor
  · rw [show 2 * (j + 1 + k) = 2 * j + 1 + (2 * k + 1) by omega]
    simpa only [Nat.zero_add, alternating_odd] using hw (2 * k + 1) (by omega)
  · rw [show 2 * (j + 1 + k) + 1 = 2 * j + 1 + 2 * (k + 1) by omega]
    simpa only [Nat.zero_add, alternating_even] using hw (2 * (k + 1)) (by omega)

/-- The two nonempty alternating words have different codes. -/
theorem alternating_codes_ne (len : ℕ) (hlen : 0 < len) :
    blockCode (alternating false) 0 len ≠ blockCode (alternating true) 0 len := by
  intro he
  have h := WordOccurrence.blockCode_eq_imp_bits
    (alternating false) (alternating true) 0 0 len he 0 hlen
  simp at h

noncomputable def wordFreq (b : ℕ → Bool) (N len : ℕ) (startsOne : Bool) : ℝ :=
  freq b N len (blockCode (alternating startsOne) 0 len)

/-- Combined frequency of `0101...` and `1010...`, each of length `len`. -/
noncomputable def totalFreq (b : ℕ → Bool) (N len : ℕ) : ℝ :=
  wordFreq b N len false + wordFreq b N len true

/-- Relative suppression against the normal target `2/2^len`. -/
noncomputable def deficit (b : ℕ → Bool) (N len : ℕ) : ℝ :=
  1 - ((2 : ℝ) ^ len / 2) * totalFreq b N len

theorem normal_wordFreq {b : ℕ → Bool} (hn : BinaryNormal b)
    (len : ℕ) (startsOne : Bool) :
    Tendsto (fun N => wordFreq b N len startsOne) atTop (𝓝 (1 / (2 : ℝ) ^ len)) :=
  hn len (blockCode (alternating startsOne) 0 len)
    (WordOccurrence.blockCode_lt (alternating startsOne) 0 len)

/-- Normality fixes the combined frequency for every individual length. -/
theorem normal_totalFreq {b : ℕ → Bool} (hn : BinaryNormal b) (len : ℕ) :
    Tendsto (fun N => totalFreq b N len) atTop (𝓝 (2 / (2 : ℝ) ^ len)) := by
  have h := (normal_wordFreq hn len false).add (normal_wordFreq hn len true)
  have he : 1 / (2 : ℝ) ^ len + 1 / (2 : ℝ) ^ len = 2 / (2 : ℝ) ^ len := by ring
  simpa only [totalFreq, he] using h

theorem normal_deficit_zero {b : ℕ → Bool} (hn : BinaryNormal b) (len : ℕ) :
    Tendsto (fun N => deficit b N len) atTop (𝓝 0) := by
  have h := (normal_totalFreq hn len).const_mul ((2 : ℝ) ^ len / 2)
  have hsub := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub h
  have hp : (2 : ℝ) ^ len ≠ 0 := by positivity
  have he : 1 - ((2 : ℝ) ^ len / 2) * (2 / (2 : ℝ) ^ len) = 0 := by
    field_simp
    norm_num
  simpa only [deficit, he] using hsub

/-- An exact rewriting of an actual relative-frequency deficit. -/
theorem deficit_ge_iff (b : ℕ → Bool) (N len : ℕ) (ε : ℝ) :
    ε ≤ deficit b N len ↔ totalFreq b N len ≤ (1 - ε) * (2 / (2 : ℝ) ^ len) := by
  have hp : 0 < (2 : ℝ) ^ len := by positivity
  have hfactor : 0 < (2 : ℝ) ^ len / 2 := by positivity
  have he : ((2 : ℝ) ^ len / 2) * ((1 - ε) * (2 / (2 : ℝ) ^ len)) = 1 - ε := by
    field_simp
  constructor
  · intro h
    apply (mul_le_mul_iff_right₀ hfactor).mp
    rw [he]
    unfold deficit at h
    linarith
  · intro h
    have hh := mul_le_mul_of_nonneg_left h hfactor.le
    rw [he] at hh
    unfold deficit
    linarith

/-- A persistent positive deficit for one fixed word length contradicts
normality. Existence of such a deficit is an explicit hypothesis. -/
theorem not_normal_of_persistent_deficit {b : ℕ → Bool}
    (len : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hp : ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ ε ≤ deficit b N len) :
    ¬ BinaryNormal b := by
  intro hn
  have he := (tendsto_order.mp (normal_deficit_zero hn len)).2 ε hε
  have hf : ∃ᶠ N in atTop, ε ≤ deficit b N len := frequently_atTop.mpr hp
  obtain ⟨N, hN, hlt⟩ := (hf.and_eventually he).exists
  linarith

theorem normal_dyadic_deficit_zero {b : ℕ → Bool} (hn : BinaryNormal b) (len : ℕ) :
    Tendsto (fun a => deficit b (RunFrequency.dyadicLength a) len) atTop (𝓝 0) :=
  (normal_deficit_zero hn len).comp RunFrequency.dyadicLength_tendsto

/-- Dyadic sample sizes are allowed, but the word length remains fixed. -/
theorem not_normal_of_persistent_dyadic_deficit {b : ℕ → Bool}
    (len : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hp : ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧
      ε ≤ deficit b (RunFrequency.dyadicLength a) len) : ¬ BinaryNormal b := by
  intro hn
  have he := (tendsto_order.mp (normal_dyadic_deficit_zero hn len)).2 ε hε
  have hf : ∃ᶠ a in atTop, ε ≤ deficit b (RunFrequency.dyadicLength a) len :=
    frequently_atTop.mpr hp
  obtain ⟨a, ha, hlt⟩ := (hf.and_eventually he).exists
  linarith

/-- A pi-specific sufficient target; no coefficient-to-frequency bridge is
assumed silently. The quantified length must be chosen once and for all. -/
theorem PI_NOT_NORMAL_OF_ALTERNATING_SUPPRESSION
    (hp : ∃ len : ℕ, 0 < len ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ ε ≤ deficit piBits N len) :
    ¬ BinaryNormal (bit Real.pi) := by
  obtain ⟨len, _hlen, ε, hε, hp⟩ := hp
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact not_normal_of_persistent_deficit len hε hp

theorem PI_NOT_NORMAL_OF_DYADIC_ALTERNATING_SUPPRESSION
    (hp : ∃ len : ℕ, 0 < len ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧
        ε ≤ deficit piBits (RunFrequency.dyadicLength a) len) :
    ¬ BinaryNormal (bit Real.pi) := by
  obtain ⟨len, _hlen, ε, hε, hp⟩ := hp
  have heq : piBits = bit Real.pi := funext piBits_eq
  rw [← heq]
  exact not_normal_of_persistent_dyadic_deficit len hε hp

end PiCt.AlternatingFrequency
