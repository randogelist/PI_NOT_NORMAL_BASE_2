import AWPIWordAnchor.CW00_Limits

namespace AWPIWordAnchor

/-- Transparent Lean alias of the Rocq `bitstream := nat -> bool`. -/
abbrev bitstream := ℕ → Bool

/-- Transparent Lean alias of the Rocq `word := list bool`. -/
abbrev word := List Bool

def bitR (b : Bool) : ℝ := if b then 1 else 0

/--
Lean reserves `matches` in its parser, so the Rocq definition is preserved
under Lean's escaped identifier spelling `«matches»`.
-/
def «matches» (x : bitstream) : word → ℕ → Bool
  | [], _ => true
  | b :: rest, start => (x start == b) && «matches» x rest (start + 1)

def rsum (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => rsum f n + f n

def tally (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => tally f n + if f n then 1 else 0

/-- Real division makes this mathematical recursion intentionally noncomputable. -/
noncomputable def fair_mass : word → ℝ
  | [] => 1
  | _ :: rest => fair_mass rest / 2

def w010 : word := [false, true, false]
def w0101 : word := [false, true, false, true]

theorem rsum_ext {f g : ℕ → ℝ} : ∀ n,
    (∀ k, f k = g k) → rsum f n = rsum g n := by
  intro n h
  induction n with
  | zero => rfl
  | succ n ih => simp [rsum, ih, h n]

theorem rsum_zero : ∀ n, rsum (fun _ => (0 : ℝ)) n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [rsum, ih]

theorem real_tally (f : ℕ → Bool) : ∀ n,
    (tally f n : ℝ) = rsum (fun k => bitR (f k)) n := by
  intro n
  induction n with
  | zero => simp [tally, rsum]
  | succ n ih =>
      cases h : f n <;> simp [tally, rsum, bitR, ih, h]

theorem rsum_one : ∀ n, rsum (fun _ => (1 : ℝ)) n = (n : ℝ) := by
  intro n
  induction n with
  | zero => simp [rsum]
  | succ n ih => simp [rsum, ih, Nat.cast_add, Nat.cast_one]

theorem rsum_bit_bounds (f : ℕ → Bool) : ∀ n,
    0 ≤ rsum (fun k => bitR (f k)) n ∧
      rsum (fun k => bitR (f k)) n ≤ (n : ℝ) := by
  intro n
  induction n with
  | zero => simp [rsum]
  | succ n ih =>
      cases h : f n <;>
        simp [rsum, bitR, h] at * <;>
        constructor <;> linarith

theorem rsum_split (f : ℕ → ℝ) (n m : ℕ) :
    rsum f (n + m) = rsum f n + rsum (fun k => f (n + k)) m := by
  induction m with
  | zero => simp [rsum]
  | succ m ih =>
      rw [Nat.add_succ, rsum, ih, rsum]
      ring

theorem matches_append (x : bitstream) (u v : word) (start : ℕ) :
    «matches» x (u ++ v) start =
      («matches» x u start && «matches» x v (start + u.length)) := by
  induction u generalizing start with
  | nil => simp [«matches»]
  | cons b rest ih =>
      simp only [List.cons_append, «matches», List.length_cons]
      rw [ih]
      simp [Bool.and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem fair_mass_append_bit (w : word) (b : Bool) :
    fair_mass (w ++ [b]) = fair_mass w / 2 := by
  induction w with
  | nil => norm_num [fair_mass]
  | cons h rest ih =>
      simp [fair_mass, ih]

theorem fair_mass_positive (w : word) : 0 < fair_mass w := by
  induction w with
  | nil => norm_num [fair_mass]
  | cons b rest ih =>
      simp only [fair_mass]
      exact div_pos ih (by norm_num)

theorem w010_extended : w010 ++ [true] = w0101 := by
  rfl

theorem fair_mass_010 : fair_mass w010 = 1 / 8 := by
  norm_num [w010, fair_mass]

theorem fair_mass_0101 : fair_mass w0101 = 1 / 16 := by
  norm_num [w0101, fair_mass]

end AWPIWordAnchor
