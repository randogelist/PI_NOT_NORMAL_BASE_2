import Mathlib.Tactic
import PartA.CtAnalytic

namespace ANCHOPI.PartB

open ANCHOPI.PartA

abbrev Bitstream := ℕ → Bool

/-- Boolean digit interpreted as an integer. -/
def bitVal : Bool → ℤ
  | false => 0
  | true => 1

/-- Difference of the even/odd pair x(2j)-x(2j+1). -/
def pairDiff (x : Bitstream) (j : ℕ) : ℤ :=
  bitVal (x (2 * j)) - bitVal (x (2 * j + 1))

/-- Sum of pair differences on j,...,j+r-1. -/
def pairInterval (x : Bitstream) : ℕ → ℕ → ℤ
  | _, 0 => 0
  | j, r + 1 => pairDiff x j + pairInterval x (j + 1) r

/-- Pair-difference prefix sum. -/
def pairPrefix (x : Bitstream) (m : ℕ) : ℤ := pairInterval x 0 m

/-- Sum of a real drift on j,...,j+r-1. -/
def driftInterval (h : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | j, r + 1 => h j + driftInterval h (j + 1) r

/-- Drift prefix sum. -/
def driftPrefix (h : ℕ → ℝ) (m : ℕ) : ℝ := driftInterval h 0 m

/-- Digit remainder after subtracting the C_t drift. -/
def ctRemainder (x : Bitstream) (h : ℕ → ℝ) (m : ℕ) : ℝ :=
  (pairPrefix x m : ℝ) - driftPrefix h m

lemma pairInterval_add (x : Bitstream) (j r s : ℕ) :
    pairInterval x j (r + s) =
      pairInterval x j r + pairInterval x (j + r) s := by
  induction r generalizing j with
  | zero => simp [pairInterval]
  | succ r ih =>
      rw [Nat.succ_add]
      simp only [pairInterval]
      rw [ih]
      have hidx : j + 1 + r = j + (r + 1) := by omega
      rw [hidx]
      ring

lemma driftInterval_add (h : ℕ → ℝ) (j r s : ℕ) :
    driftInterval h j (r + s) =
      driftInterval h j r + driftInterval h (j + r) s := by
  induction r generalizing j with
  | zero => simp [driftInterval]
  | succ r ih =>
      rw [Nat.succ_add]
      simp only [driftInterval]
      rw [ih]
      have hidx : j + 1 + r = j + (r + 1) := by omega
      rw [hidx]
      ring

lemma pairPrefix_add (x : Bitstream) (j r : ℕ) :
    pairPrefix x (j + r) = pairPrefix x j + pairInterval x j r := by
  unfold pairPrefix
  simpa using pairInterval_add x 0 j r

lemma driftPrefix_add (h : ℕ → ℝ) (j r : ℕ) :
    driftPrefix h (j + r) = driftPrefix h j + driftInterval h j r := by
  unfold driftPrefix
  simpa using driftInterval_add h 0 j r

lemma driftInterval_nonneg {h : ℕ → ℝ} (hpos : ∀ j, 0 < h j) :
    ∀ j r, 0 ≤ driftInterval h j r := by
  intro j r
  induction r generalizing j with
  | zero => simp [driftInterval]
  | succ r ih =>
      simp only [driftInterval]
      have hp : 0 ≤ h j := le_of_lt (hpos j)
      have hr : 0 ≤ driftInterval h (j + 1) r := ih (j + 1)
      linarith

lemma pairInterval_remainder_identity (x : Bitstream) (h : ℕ → ℝ)
    (j r : ℕ) :
    (pairInterval x j r : ℝ) =
      driftInterval h j r + ctRemainder x h (j + r) - ctRemainder x h j := by
  have hp := pairPrefix_add x j r
  have hd := driftPrefix_add h j r
  have hpR : (pairPrefix x (j + r) : ℝ) =
      (pairPrefix x j : ℝ) + (pairInterval x j r : ℝ) := by
    exact_mod_cast hp
  unfold ctRemainder
  rw [hd]
  linarith

/-- The one substantive Part-B bridge: actual odd/even digit sums follow the
    positive C_t drift up to one eventual uniformly bounded remainder. -/
structure CtDriftBridge (x : Bitstream) (h : ℕ → ℝ) : Prop where
  positive : ∀ j, 0 < h j
  bounded : ∃ B J : ℕ, ∀ m, J ≤ m → |ctRemainder x h m| ≤ (B : ℝ)

lemma pairInterval_lower_of_bound {x : Bitstream} {h : ℕ → ℝ}
    (hpos : ∀ j, 0 < h j) {B J j r : ℕ}
    (hbound : ∀ m, J ≤ m → |ctRemainder x h m| ≤ (B : ℝ))
    (hj : J ≤ j) :
    -(2 * (B : ℝ)) ≤ (pairInterval x j r : ℝ) := by
  have hnonneg : 0 ≤ driftInterval h j r := driftInterval_nonneg hpos j r
  have hb0 := hbound j hj
  have hb1 := hbound (j + r) (by omega)
  have hb0' := abs_le.mp hb0
  have hb1' := abs_le.mp hb1
  have hid := pairInterval_remainder_identity x h j r
  linarith

/-- Finite word matching at a starting position. -/
def matchesAt (x : Bitstream) : List Bool → ℕ → Prop
  | [], _ => True
  | b :: w, n => x n = b ∧ matchesAt x w (n + 1)

lemma matchesAt_append (x : Bitstream) (u v : List Bool) (n : ℕ) :
    matchesAt x (u ++ v) n ↔
      matchesAt x u n ∧ matchesAt x v (n + u.length) := by
  induction u generalizing n with
  | nil => simp [matchesAt]
  | cons b u ih =>
      simp only [List.cons_append, matchesAt, List.length_cons]
      rw [ih]
      constructor
      · rintro ⟨hb, hu, hv⟩
        refine ⟨⟨hb, hu⟩, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
      · rintro ⟨⟨hb, hu⟩, hv⟩
        refine ⟨hb, hu, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv

/-- The alternating word (01)^r. -/
def alt01 : ℕ → List Bool
  | 0 => []
  | r + 1 => false :: true :: alt01 r

lemma alt01_length (r : ℕ) : (alt01 r).length = 2 * r := by
  induction r with
  | zero => simp [alt01]
  | succ r ih => simp [alt01, ih]; omega

/-- The fixed forbidden word used in the contradiction: (01)^r 0 (01)^r. -/
def criticalWord (r : ℕ) : List Bool :=
  alt01 r ++ (false :: alt01 r)

lemma criticalWord_ne_nil (r : ℕ) : criticalWord r ≠ [] := by
  simp [criticalWord]

lemma alt01_match_pairInterval (x : Bitstream) :
    ∀ r j, matchesAt x (alt01 r) (2 * j) →
      pairInterval x j r = -(r : ℤ) := by
  intro r
  induction r with
  | zero =>
      intro j h
      simp [alt01, pairInterval]
  | succ r ih =>
      intro j h
      simp [alt01, matchesAt] at h
      rcases h with ⟨h0, h1, hrest⟩
      have hrest' : matchesAt x (alt01 r) (2 * (j + 1)) := by
        convert hrest using 1 <;> omega
      have hi := ih (j + 1) hrest'
      simp [pairInterval, pairDiff, bitVal, h0, h1, hi]

lemma critical_match_sides (x : Bitstream) (r n : ℕ)
    (h : matchesAt x (criticalWord r) n) :
    matchesAt x (alt01 r) n ∧
      matchesAt x (alt01 r) (n + (2 * r + 1)) := by
  unfold criticalWord at h
  rw [matchesAt_append] at h
  rcases h with ⟨hleft, hright0⟩
  rw [alt01_length] at hright0
  simp [matchesAt] at hright0
  rcases hright0 with ⟨_, hright⟩
  refine ⟨hleft, ?_⟩
  convert hright using 1 <;> omega

lemma even_or_odd_repr (n : ℕ) :
    (∃ j, n = 2 * j) ∨ (∃ j, n = 2 * j + 1) := by
  induction n with
  | zero =>
      exact Or.inl ⟨0, by simp⟩
  | succ n ih =>
      rcases ih with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact Or.inr ⟨j, by omega⟩
      · exact Or.inl ⟨j + 1, by omega⟩

/-- Necessary recurrence property of ordinary normality: every fixed nonempty
    finite word occurs arbitrarily late.  Part B contradicts this property. -/
def EveryWordRecurrent (x : Bitstream) : Prop :=
  ∀ w : List Bool, w ≠ [] → ∀ J : ℕ, ∃ n : ℕ, J ≤ n ∧ matchesAt x w n

/-- Positive C_t drift plus bounded digit remainder eventually forbids one
    explicit finite word. -/
theorem criticalWord_eventually_absent {x : Bitstream} {h : ℕ → ℝ}
    (hb : CtDriftBridge x h) :
    ∃ r J0 : ℕ, ∀ n : ℕ, J0 ≤ n → ¬ matchesAt x (criticalWord r) n := by
  rcases hb.bounded with ⟨B, J, hbound⟩
  let r : ℕ := 2 * B + 1
  refine ⟨r, 2 * J, ?_⟩
  intro n hn hmatch
  rcases critical_match_sides x r n hmatch with ⟨hleft, hright⟩
  rcases even_or_odd_repr n with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst n
    have hJ : J ≤ j := by omega
    have hsum := alt01_match_pairInterval x r j hleft
    have hlow := pairInterval_lower_of_bound hb.positive hbound hJ (r := r)
    have hsumR : (pairInterval x j r : ℝ) = -(r : ℝ) := by
      rw [hsum]
      norm_num
    rw [hsumR] at hlow
    have hr : 2 * (B : ℝ) < (r : ℝ) := by
      dsimp [r]
      norm_num
    linarith
  · subst n
    let j2 : ℕ := j + r + 1
    have hJ : J ≤ j2 := by
      dsimp [j2]
      omega
    have halt : matchesAt x (alt01 r) (2 * j2) := by
      dsimp [j2]
      convert hright using 1 <;> omega
    have hsum := alt01_match_pairInterval x r j2 halt
    have hlow := pairInterval_lower_of_bound hb.positive hbound hJ (r := r)
    have hsumR : (pairInterval x j2 r : ℝ) = -(r : ℝ) := by
      rw [hsum]
      norm_num
    rw [hsumR] at hlow
    have hr : 2 * (B : ℝ) < (r : ℝ) := by
      dsimp [r]
      norm_num
    linarith

/-- Core contradiction: the C_t drift bridge is incompatible even with the
    weakest recurrence consequence needed from ordinary binary normality. -/
theorem ctDriftBridge_not_everyWordRecurrent {x : Bitstream} {h : ℕ → ℝ}
    (hb : CtDriftBridge x h) : ¬ EveryWordRecurrent x := by
  rcases criticalWord_eventually_absent hb with ⟨r, J0, hforbid⟩
  intro hrec
  rcases hrec (criticalWord r) (criticalWord_ne_nil r) J0 with ⟨n, hn, hmatch⟩
  exact hforbid n hn hmatch

/-- C_t pair drift built directly from the positive Part-A magnitudes. -/
noncomputable def analyticCtPairDrift (a t : ℕ → ℕ) (j : ℕ) : ℝ :=
  (shellCtMagnitude (a j) (t j) + shellCtMagnitude (a j) (t j + 1)) /
    (shellN (a j) : ℝ)

theorem analyticCtPairDrift_pos (a t : ℕ → ℕ) (j : ℕ) :
    0 < analyticCtPairDrift a t j := by
  unfold analyticCtPairDrift
  apply div_pos
  · have h0 := shellCtMagnitude_pos (a j) (t j)
    have h1 := shellCtMagnitude_pos (a j) (t j + 1)
    linarith
  · exact_mod_cast shellN_pos (a j)

/-- This is the single π/digit-side bridge Part B still needs after Part A:
    the shell coordinates address the actual even/odd pairs and the resulting
    C_t drift has an eventually uniformly bounded remainder. -/
structure CtDigitBridge (x : Bitstream) (a t : ℕ → ℕ) : Prop where
  address : ∀ j, 2 * j = shellN (a j) + t j
  evenOffset : ∀ j, t j % 2 = 0
  interior : ∀ j, t j + 1 < shellN (a j)
  bounded : ∃ B J : ℕ, ∀ m, J ≤ m →
    |ctRemainder x (analyticCtPairDrift a t) m| ≤ (B : ℝ)

/-- Part B in its C_t-facing form.  All positivity/nonvanishing information is
    imported from Part A; the only substantive new hypothesis is the digit
    realization/bounded-remainder bridge above. -/
theorem PART_B_CT_CONTRADICTION {x : Bitstream} {a t : ℕ → ℕ}
    (hbridge : CtDigitBridge x a t) : ¬ EveryWordRecurrent x := by
  apply ctDriftBridge_not_everyWordRecurrent
  refine ⟨analyticCtPairDrift_pos a t, ?_⟩
  exact hbridge.bounded

/-- Abstract normality closure: for any chosen ordinary-normality predicate,
    once its standard recurrence consequence is available, the C_t bridge
    produces the outright contradiction. -/
theorem PART_B_NORMALITY_CONTRADICTION
    {Normal : Bitstream → Prop} {x : Bitstream} {a t : ℕ → ℕ}
    (normal_implies_recurrent : ∀ y, Normal y → EveryWordRecurrent y)
    (hbridge : CtDigitBridge x a t) : ¬ Normal x := by
  intro hnormal
  exact PART_B_CT_CONTRADICTION hbridge (normal_implies_recurrent x hnormal)

end ANCHOPI.PartB
