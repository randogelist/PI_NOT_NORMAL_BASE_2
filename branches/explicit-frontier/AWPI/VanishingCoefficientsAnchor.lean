import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace AWPI.VanishingCoefficientsAnchor

open scoped BigOperators

/-- Zero-based binary digits. -/
abbrev Digits := Nat → Bool

/-- Boolean block occurrence, matching the Rocq definition. -/
def occursb (d : Digits) (w : List Bool) (s : Nat) : Bool :=
  match w with
  | [] => true
  | b :: rest => decide (d s = b) && occursb d rest (s + 1)

/-- A finite word occurs at zero-based start `s`. -/
def Occurs (d : Digits) (w : List Bool) (s : Nat) : Prop :=
  occursb d w s = true

/-- Count word starts `0, ..., n-1`; the word may extend beyond `n-1`. -/
def blockCount (d : Digits) (w : List Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => blockCount d w n + if occursb d w n then 1 else 0

@[simp] theorem occurs_nil (d : Digits) (s : Nat) : Occurs d [] s := by
  simp [Occurs, occursb]

@[simp] theorem occurs_cons (d : Digits) (b : Bool) (w : List Bool) (s : Nat) :
    Occurs d (b :: w) s ↔ d s = b ∧ Occurs d w (s + 1) := by
  simp [Occurs, occursb]

/-- Appending words shifts the second occurrence by the first word's length. -/
theorem occurs_append (d : Digits) (u v : List Bool) (s : Nat) :
    Occurs d (u ++ v) s ↔
      Occurs d u s ∧ Occurs d v (s + u.length) := by
  induction u generalizing s with
  | nil => simp
  | cons b u ih =>
      rw [List.cons_append]
      simp only [occurs_cons]
      rw [ih]
      constructor
      · rintro ⟨h0, hu, hv⟩
        refine ⟨⟨h0, hu⟩, ?_⟩
        convert hv using 1 <;> simp only [List.length_cons] <;> omega
      · rintro ⟨⟨h0, hu⟩, hv⟩
        refine ⟨h0, hu, ?_⟩
        convert hv using 1 <;> simp only [List.length_cons] <;> omega

/-- At most one occurrence is added at each start. -/
theorem blockCount_le (d : Digits) (w : List Bool) (n : Nat) :
    blockCount d w n ≤ n := by
  induction n with
  | zero => simp [blockCount]
  | succ n ih =>
      simp only [blockCount]
      split <;> omega

/-- If a word never occurs from start `B` onward, its total prefix count is at most `B`. -/
theorem blockCount_bounded_when_absent
    (d : Digits) (w : List Bool) (B : Nat)
    (habs : ∀ s, B ≤ s → ¬ Occurs d w s) :
    ∀ n, blockCount d w n ≤ B := by
  intro n
  induction n with
  | zero => simp [blockCount]
  | succ n ih =>
      simp only [blockCount]
      by_cases hlate : B ≤ n
      · have hfalse : occursb d w n = false := by
          by_contra hne
          have htrue : occursb d w n = true := by
            cases h : occursb d w n <;> simp_all
          exact habs n hlate htrue
        simp [hfalse, ih]
      · have hnB : n < B := Nat.lt_of_not_ge hlate
        have hbase := blockCount_le d w n
        split <;> omega

/-- Exact integer-tolerance version of ordinary binary block normality, matching Rocq. -/
def frequencyBound (d : Digits) (w : List Bool) (q n : Nat) : Prop :=
  q * (2 ^ w.length * blockCount d w n) ≤ q * n + n ∧
  q * n ≤ q * (2 ^ w.length * blockCount d w n) + n

/-- Ordinary base-2 block normality in the exact Rocq formulation. -/
def BinaryNormal (d : Digits) : Prop :=
  ∀ w : List Bool, w ≠ [] →
    ∀ q : Nat, 0 < q →
      ∃ B : Nat, ∀ n : Nat, B ≤ n → frequencyBound d w q n

/-- Normality forces every nonempty word to occur arbitrarily late. -/
theorem normal_has_word_after
    (d : Digits) (hnormal : BinaryNormal d)
    (w : List Bool) (hw : w ≠ []) (B : Nat) :
    ∃ s, B ≤ s ∧ Occurs d w s := by
  obtain ⟨N0, hN0⟩ := hnormal w hw 2 (by omega)
  let K : Nat := 2 ^ w.length
  let n : Nat := N0 + 2 * K * B + 1
  have hN0n : N0 ≤ n := by
    dsimp [n]
    omega
  have hfreq := hN0 n hN0n
  have hcount : B < blockCount d w n := by
    by_contra hnot
    have hle : blockCount d w n ≤ B := Nat.le_of_not_gt hnot
    have hmul :
        2 * (K * blockCount d w n) ≤ 2 * (K * B) := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left K hle)
    have hlower :
        2 * n ≤ 2 * (K * blockCount d w n) + n := by
      simpa [frequencyBound, K] using hfreq.2
    have hnle : n ≤ 2 * (K * B) := by omega
    have hngt : 2 * (K * B) < n := by
      dsimp [n]
      rw [Nat.mul_assoc]
      omega
    omega
  by_contra hnone
  have habs : ∀ s, B ≤ s → ¬ Occurs d w s := by
    intro s hs hocc
    exact hnone ⟨s, hs, hocc⟩
  have hbounded := blockCount_bounded_when_absent d w B habs n
  omega

/-- Every integer lies at distance at most one below some even integer. -/
theorem even_start_within_one (s : Nat) :
    ∃ j, s ≤ 2 * j ∧ 2 * j ≤ s + 1 := by
  induction s with
  | zero => exact ⟨0, by omega⟩
  | succ s ih =>
      obtain ⟨j, hlo, hhi⟩ := ih
      by_cases h : 2 * j = s
      · exact ⟨j + 1, by omega⟩
      · exact ⟨j, by omega⟩

/-- Convert a Boolean digit to the real values 0 and 1. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

/-- Fixed aligned even/odd pair score `x_(2j) - x_(2j+1)`. -/
def pairScore (d : Digits) (j : Nat) : ℝ :=
  bitValue (d (2 * j)) - bitValue (d (2 * j + 1))

/-- Prefix sum of a real sequence. -/
def prefixSum (f : Nat → ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => prefixSum f n + f n

/-- Interval sum of length `n` beginning at `j`. -/
def intervalSum (f : Nat → ℝ) (j : Nat) : Nat → ℝ
  | 0 => 0
  | n + 1 => f j + intervalSum f (j + 1) n

/-- Pair-score prefix sum. -/
def pairPrefix (d : Digits) (n : Nat) : ℝ := prefixSum (pairScore d) n

/-- Pair-score interval sum. -/
def pairInterval (d : Digits) (j n : Nat) : ℝ := intervalSum (pairScore d) j n

/-- Prefix differences equal interval sums. -/
theorem prefix_interval_identity (f : Nat → ℝ) (n j : Nat) :
    prefixSum f (j + n) - prefixSum f j = intervalSum f j n := by
  induction n generalizing j with
  | zero => simp [prefixSum, intervalSum]
  | succ n ih =>
      rw [show j + (n + 1) = (j + 1) + n by omega]
      have htail := ih (j := j + 1)
      simp only [prefixSum] at htail
      simp only [intervalSum]
      linarith

/-- Pair prefix differences equal pair interval sums. -/
theorem pair_prefix_interval (d : Digits) (j n : Nat) :
    pairPrefix d (j + n) - pairPrefix d j = pairInterval d j n := by
  exact prefix_interval_identity (pairScore d) n j

/-- A nonnegative pointwise drift has nonnegative interval sums. -/
theorem intervalSum_nonnegative
    (f : Nat → ℝ) (J : Nat)
    (h : ∀ j, J ≤ j → 0 ≤ f j) :
    ∀ n j, J ≤ j → 0 ≤ intervalSum f j n := by
  intro n
  induction n with
  | zero => intro j hj; simp [intervalSum]
  | succ n ih =>
      intro j hj
      simp only [intervalSum]
      have h0 := h j hj
      have htail := ih (j + 1) (by omega)
      linarith

/-- `(01)^r`, written in zero/one Bool order. -/
def opposingWord : Nat → List Bool
  | 0 => []
  | r + 1 => false :: true :: opposingWord r

@[simp] theorem opposingWord_length (r : Nat) :
    (opposingWord r).length = 2 * r := by
  induction r with
  | zero => simp [opposingWord]
  | succ r ih => simp [opposingWord, ih]; omega

/-- One leading `01` pair has score exactly `-1`. -/
theorem opposingWord_step
    (d : Digits) (r j : Nat)
    (hocc : Occurs d (opposingWord (r + 1)) (2 * j)) :
    pairScore d j = -1 ∧
      Occurs d (opposingWord r) (2 * (j + 1)) := by
  change Occurs d (false :: true :: opposingWord r) (2 * j) at hocc
  rw [occurs_cons] at hocc
  obtain ⟨h0, htail⟩ := hocc
  rw [occurs_cons] at htail
  obtain ⟨h1, hrest⟩ := htail
  constructor
  · unfold pairScore bitValue
    have hidx : 2 * j + 1 = 2 * j + 1 := rfl
    simp [h0, h1]
  · convert hrest using 1 <;> omega

/-- An aligned `(01)^r` word lowers the pair walk by exactly `r`. -/
theorem opposingWord_exact_drop
    (d : Digits) (r j : Nat)
    (hocc : Occurs d (opposingWord r) (2 * j)) :
    pairInterval d j r = -(r : ℝ) := by
  induction r generalizing j with
  | zero => simp [pairInterval, intervalSum]
  | succ r ih =>
      obtain ⟨hhead, htail⟩ := opposingWord_step d r j hocc
      simp only [pairInterval, intervalSum]
      have htaildrop := ih (j := j + 1) htail
      unfold pairInterval at htaildrop
      rw [hhead, htaildrop]
      norm_num

/-- Ordinary-word parity cover `(01)^r 0 (01)^r`. -/
def opposingCover (r : Nat) : List Bool :=
  opposingWord r ++ (false :: opposingWord r)

@[simp] theorem opposingCover_length (r : Nat) :
    (opposingCover r).length = 4 * r + 1 := by
  simp [opposingCover]
  omega

theorem opposingCover_nonempty (r : Nat) : opposingCover r ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [opposingCover_length] at hlen
  simp at hlen

/-- An occurrence of the parity cover contains one copy of `(01)^r` at an even start. -/
theorem opposingCover_has_even_copy
    (d : Digits) (r s : Nat)
    (hocc : Occurs d (opposingCover r) s) :
    ∃ j, s ≤ 2 * j ∧ Occurs d (opposingWord r) (2 * j) := by
  have hc :
      Occurs d (opposingWord r) s ∧
      Occurs d (opposingWord r) (s + (2 * r + 1)) := by
    unfold opposingCover at hocc
    rw [occurs_append] at hocc
    obtain ⟨hfirst, hrest⟩ := hocc
    rw [occurs_cons] at hrest
    obtain ⟨_, hsecond⟩ := hrest
    constructor
    · exact hfirst
    · convert hsecond using 1 <;> simp <;> omega
  obtain ⟨hfirst, hsecond⟩ := hc
  obtain ⟨j, hlo, hhi⟩ := even_start_within_one s
  by_cases heq : 2 * j = s
  · exact ⟨j, hlo, by simpa [heq] using hfirst⟩
  · refine ⟨j + r, ?_, ?_⟩
    · omega
    · have hodd : 2 * j = s + 1 := by omega
      convert hsecond using 1 <;> omega

/-- A uniform lower bound on all sufficiently late pair-walk drops. -/
def EventualDropBound (d : Digits) (B J : Nat) : Prop :=
  ∀ j n, J ≤ j → -(B : ℝ) ≤ pairInterval d j n

/-- Such a bound excludes normality by forbidding one fixed finite word. -/
theorem bounded_drop_not_normal
    (d : Digits) (B J : Nat)
    (hbound : EventualDropBound d B J) :
    ¬ BinaryNormal d := by
  intro hnormal
  let r := B + 1
  let w := opposingCover r
  obtain ⟨s, hs, hocc⟩ := normal_has_word_after d hnormal w
    (by exact opposingCover_nonempty r) (2 * J)
  obtain ⟨j, hj, hword⟩ := opposingCover_has_even_copy d r s hocc
  have hjJ : J ≤ j := by omega
  have hfloor := hbound j r hjJ
  have hdrop := opposingWord_exact_drop d r j hword
  rw [hdrop] at hfloor
  dsimp [r] at hfloor
  norm_num at hfloor

/-- Dyadic plane width `2^(10+a)`. -/
def planeWidth (a : Nat) : Nat := 2 ^ (10 + a)

/-- Real-valued dyadic scale. -/
def planeScale (a : Nat) : ℝ := planeWidth a

theorem planeScale_positive (a : Nat) : 0 < planeScale a := by
  unfold planeScale planeWidth
  positivity

/-- Genuine dyadic pair-coordinate obligations. This is an interface, not an inhabitant for π. -/
structure DyadicPairCoordinates (plane offset : Nat → Nat) (J : Nat) : Prop where
  coordinate_address : ∀ j, J ≤ j → 2 * j = planeWidth (plane j) + offset j
  coordinate_inside : ∀ j, J ≤ j → offset j + 1 < planeWidth (plane j)
  coordinate_even : ∀ j, J ≤ j → ∃ k, offset j = 2 * k

/-- Candidate critical pair drift from opposite coefficient corrections. -/
noncomputable def criticalPairDrift
    (C : Nat → ℝ) (plane offset : Nat → Nat) (j : Nat) : ℝ :=
  (C (offset j) + C (offset j + 1)) / planeScale (plane j)

theorem criticalPairDrift_nonnegative
    (C : Nat → ℝ) (plane offset : Nat → Nat)
    (hC : ∀ t, 0 ≤ C t) (j : Nat) :
    0 ≤ criticalPairDrift C plane offset j := by
  unfold criticalPairDrift
  have h0 : 0 ≤ C (offset j) := hC (offset j)
  have h1 : 0 ≤ C (offset j + 1) := hC (offset j + 1)
  have hnum : 0 ≤ C (offset j) + C (offset j + 1) := add_nonneg h0 h1
  have hden : 0 < planeScale (plane j) := planeScale_positive _
  exact div_nonneg hnum (le_of_lt hden)

/-- Exact remainder defined from actual digits and the candidate drift. -/
noncomputable def criticalRemainder
    (d : Digits) (C : Nat → ℝ)
    (plane offset : Nat → Nat) (m : Nat) : ℝ :=
  pairPrefix d m - prefixSum (criticalPairDrift C plane offset) m

/-- Exact one-step telescoping identity. -/
theorem criticalRemainder_step
    (d : Digits) (C : Nat → ℝ)
    (plane offset : Nat → Nat) (j : Nat) :
    pairScore d j = criticalPairDrift C plane offset j +
      criticalRemainder d C plane offset (j + 1) -
      criticalRemainder d C plane offset j := by
  unfold criticalRemainder pairPrefix
  simp only [prefixSum]
  ring

/-- Exact interval identity for the critical remainder. -/
theorem critical_interval_identity
    (d : Digits) (C : Nat → ℝ)
    (plane offset : Nat → Nat) (j n : Nat) :
    pairInterval d j n =
      intervalSum (criticalPairDrift C plane offset) j n +
      criticalRemainder d C plane offset (j + n) -
      criticalRemainder d C plane offset j := by
  unfold criticalRemainder
  rw [← pair_prefix_interval]
  rw [← prefix_interval_identity]
  ring

/-- Uniform two-sided bound on the actual critical remainder. -/
def CriticalRemainderBound
    (d : Digits) (C : Nat → ℝ)
    (plane offset : Nat → Nat) (B J : Nat) : Prop :=
  ∀ m, J ≤ m →
    -(B : ℝ) ≤ criticalRemainder d C plane offset m ∧
      criticalRemainder d C plane offset m ≤ (B : ℝ)

/-- Checked stronger anchor: nonnegative critical drift plus bounded actual remainder excludes normality. -/
theorem critical_bounded_remainder_not_normal
    (d : Digits) (C : Nat → ℝ)
    (plane offset : Nat → Nat) (B J : Nat)
    (hC : ∀ t, 0 ≤ C t)
    (hbound : CriticalRemainderBound d C plane offset B J) :
    ¬ BinaryNormal d := by
  apply bounded_drop_not_normal d (2 * B) J
  intro j n hj
  have hid := critical_interval_identity d C plane offset j n
  have hsum : 0 ≤ intervalSum (criticalPairDrift C plane offset) j n := by
    apply intervalSum_nonnegative (criticalPairDrift C plane offset) 0
    · intro k hk
      exact criticalPairDrift_nonnegative C plane offset hC k
    · omega
  obtain ⟨hjlo, hjhi⟩ := hbound j hj
  obtain ⟨hendlo, hendhi⟩ := hbound (j + n) (by omega)
  have hcast : ((2 * B : Nat) : ℝ) = (B : ℝ) + (B : ℝ) := by
    push_cast
    ring
  rw [hcast]
  linarith

/-- Ordinary convergence `C_t → 0`, written exactly as in the Rocq package. -/
def CoefficientVanishes (C : Nat → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : Nat,
    ∀ t : Nat, T ≤ t → -ε ≤ C t ∧ C t ≤ ε

/-- Every coefficient is strictly positive. -/
def PositiveCoefficients (C : Nat → ℝ) : Prop := ∀ t, 0 < C t

/-- No positive common lower bound survives on any tail. -/
def NoPositiveTailLowerBound (C : Nat → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ T : Nat,
    ∃ t : Nat, T ≤ t ∧ C t < c

theorem vanishing_has_no_positive_tail_lower_bound
    (C : Nat → ℝ) (hzero : CoefficientVanishes C) :
    NoPositiveTailLowerBound C := by
  intro c hc T
  obtain ⟨K, hK⟩ := hzero (c / 2) (by linarith)
  refine ⟨T + K, by omega, ?_⟩
  obtain ⟨_, hhi⟩ := hK (T + K) (by omega)
  linarith

/-- Main migrated theorem: positivity + vanishing + bounded actual remainder imply nonnormality.

The convergence hypothesis is intentionally not needed by the proof term: the stronger theorem
already holds for all nonnegative coefficient sequences. -/
theorem vanishing_coefficients_bounded_remainder_not_normal
    (d : Digits) (C : Nat → ℝ)
    (plane offset : Nat → Nat) (B J : Nat)
    (hpos : PositiveCoefficients C)
    (_hzero : CoefficientVanishes C)
    (hbound : CriticalRemainderBound d C plane offset B J) :
    ¬ BinaryNormal d := by
  apply critical_bounded_remainder_not_normal d C plane offset B J
  · intro t
    exact le_of_lt (hpos t)
  · exact hbound

/-- Application interface. No inhabitant for the binary digits of π is declared here. -/
structure VanishingCriticalDigitAnchor (d : Digits) where
  C : Nat → ℝ
  plane : Nat → Nat
  offset : Nat → Nat
  B : Nat
  J : Nat
  coordinates : DyadicPairCoordinates plane offset J
  positive : PositiveCoefficients C
  vanishes : CoefficientVanishes C
  remainder : CriticalRemainderBound d C plane offset B J

theorem vanishing_critical_digit_anchor_not_normal
    (d : Digits) (h : VanishingCriticalDigitAnchor d) :
    ¬ BinaryNormal d := by
  exact vanishing_coefficients_bounded_remainder_not_normal
    d h.C h.plane h.offset h.B h.J h.positive h.vanishes h.remainder

end AWPI.VanishingCoefficientsAnchor
