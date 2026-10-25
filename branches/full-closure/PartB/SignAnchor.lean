import AWPIWordAnchor.CW02_FiniteExperiment

namespace ANCHOPI.PartB

open AWPIWordAnchor

/-- The alternating sign used by the parity coefficient. -/
def paritySign : ℕ → ℝ
  | 0 => 1
  | n + 1 => - paritySign n

@[simp] theorem paritySign_zero : paritySign 0 = 1 := rfl
@[simp] theorem paritySign_succ (n : ℕ) : paritySign (n + 1) = - paritySign n := rfl

theorem paritySign_cases (n : ℕ) : paritySign n = 1 ∨ paritySign n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rcases ih with h | h
      · right
        simp [paritySign, h]
      · left
        simp [paritySign, h]

theorem paritySign_add (s t : ℕ) :
    paritySign (s + t) = paritySign s * paritySign t := by
  induction t with
  | zero => simp [paritySign]
  | succ t ih =>
      rw [Nat.add_succ]
      simp only [paritySign]
      rw [ih]
      ring

theorem paritySign_double (t : ℕ) : paritySign (t + t) = 1 := by
  rw [paritySign_add]
  rcases paritySign_cases t with h | h <;> rw [h] <;> norm_num

/-- Uniform convergence in the shell variable `a`, uniformly over all tail offsets `t ≥ Q`. -/
def UniformTailLimit (Q : ℕ) (H : ℕ → ℕ → ℝ) (C : ℕ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a →
      ∀ t : ℕ, Q ≤ t → |H a t - C t| < eps

/--
A finite-window observation contract.  At scale `a`, the value `H a t` is
completely determined by one finite word of the digit stream beginning at `t`.
This is the no-external-parity-tag condition from the Rocq sign anchor.
-/
def FiniteObservations (x : bitstream) (H : ℕ → ℕ → ℝ) : Prop :=
  ∀ a : ℕ, ∃ width : ℕ, ∀ origin dest : ℕ,
    «matches» x (List.ofFn (fun j : Fin width => x (origin + j.1))) dest = true →
      H a dest = H a origin

/-- The limiting coefficient has the required weak alternating sign. -/
def WeakParity (phase Q : ℕ) (C : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, Q ≤ t → 0 ≤ paritySign (phase + t) * C t

/-- Strict version.  It immediately supplies a nonzero coefficient. -/
def StrictParity (phase Q : ℕ) (C : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, Q ≤ t → 0 < paritySign (phase + t) * C t

private theorem abs_lt_bounds {r eps : ℝ} (h : |r| < eps) : -eps < r ∧ r < eps := by
  constructor
  · have hneg : -|r| ≤ r := neg_abs_le r
    linarith
  · have hpos : r ≤ |r| := le_abs_self r
    linarith

/-- Ordinary normality makes every nonempty finite word occur somewhere. -/
theorem normal_word_occurs (x : bitstream) (w : word)
    (hnormal : normal x) (hw : w ≠ []) :
    ∃ start : ℕ, «matches» x w start = true := by
  have hmass : 0 < fair_mass w := fair_mass_positive w
  have heps : 0 < fair_mass w / 2 := by linarith
  rcases hnormal w (fair_mass w / 2) heps with ⟨N0, hN0⟩
  let N : ℕ := N0 + 1
  have hnear := hN0 N (by dsimp [N]; omega)
  have hfreqPos : 0 < frequency x w N := by
    rcases hnear with ⟨hlo, _hhi⟩
    change 0 < frequency_on ordinary_starts x w N
    linarith
  by_contra hnone
  push_neg at hnone
  have hallFalse : ∀ s : ℕ, «matches» x w s = false := by
    intro s
    cases hs : «matches» x w s with
    | false => rfl
    | true => exact False.elim (hnone s hs)
  have hsum :
      rsum (fun j => bitR («matches» x w j)) N = 0 := by
    rw [← rsum_zero N]
    apply rsum_ext
    intro j
    rw [hallFalse j]
    rfl
  unfold frequency frequency_on average_on ordinary_starts at hfreqPos
  rw [hsum] at hfreqPos
  simp at hfreqPos

private theorem matches_append_true (x : bitstream) (u v : word) (start : ℕ) :
    «matches» x (u ++ v) start = true ↔
      «matches» x u start = true ∧
      «matches» x v (start + u.length) = true := by
  rw [matches_append]
  simp

/--
A normal stream contains one chosen word at both parity classes.  One compound
word gives the two occurrences at an odd separation, so no arithmetic-
progression normality theorem is needed.
-/
theorem normal_word_opposite_parities (x : bitstream) (w : word)
    (phase Q : ℕ) (hnormal : normal x) :
    ∃ s u : ℕ,
      Q ≤ s ∧ Q ≤ u ∧
      paritySign (phase + u) = - paritySign (phase + s) ∧
      «matches» x w s = true ∧ «matches» x w u = true := by
  let pad : word := List.replicate Q false
  let sep : word := List.replicate (w.length + 1) false
  let v : word := pad ++ (w ++ (sep ++ w))
  have hv : v ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp [v, pad, sep] at hlen
  rcases normal_word_occurs x v hnormal hv with ⟨start, hmatch⟩
  have h0 := (matches_append_true x pad (w ++ (sep ++ w)) start).mp (by
    simpa [v] using hmatch)
  rcases h0 with ⟨_hprefix, hrest⟩
  have h1 := (matches_append_true x w (sep ++ w) (start + pad.length)).mp hrest
  rcases h1 with ⟨hleft, hrest2⟩
  have h2 := (matches_append_true x sep w (start + pad.length + w.length)).mp (by
    simpa [Nat.add_assoc] using hrest2)
  rcases h2 with ⟨_hsep, hright⟩
  let s : ℕ := start + Q
  let u : ℕ := start + Q + w.length + (w.length + 1)
  refine ⟨s, u, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [s]
    omega
  · dsimp [u]
    omega
  · have hu : phase + u = (phase + s) + (w.length + w.length + 1) := by
      dsimp [s, u]
      omega
    rw [hu]
    have hs2 : w.length + w.length + 1 = (w.length + w.length) + 1 := by omega
    rw [hs2, paritySign_add]
    simp only [paritySign]
    rw [paritySign_double]
    ring
  · simpa [s, pad] using hleft
  · simpa [u, pad, sep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hright

/--
Strong Part-B lemma: if a finite-window observable converges uniformly to a
weak parity-signed coefficient sequence, then ordinary normality forces every
coefficient on the tail to be zero.
-/
theorem normal_uniform_parity_forces_zero
    (x : bitstream) (H : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (phase Q : ℕ)
    (hnormal : normal x)
    (hfinite : FiniteObservations x H)
    (huniform : UniformTailLimit Q H C)
    (hparity : WeakParity phase Q C) :
    ∀ t : ℕ, Q ≤ t → C t = 0 := by
  intro t ht
  by_contra hnonzero
  have habsPos : 0 < |C t| := abs_pos.mpr hnonzero
  have heps : 0 < |C t| / 4 := by positivity
  rcases huniform (|C t| / 4) heps with ⟨A, hA⟩
  rcases hfinite A with ⟨width, hlocal⟩
  let w : word := List.ofFn (fun j : Fin width => x (t + j.1))
  rcases normal_word_opposite_parities x w phase Q hnormal with
    ⟨s, u, hsQ, huQ, hopen, hms, hmu⟩
  have hst : H A s = H A t := by
    exact hlocal t s (by simpa [w])
  have hut : H A u = H A t := by
    exact hlocal t u (by simpa [w])
  have e0 := hA A (le_rfl) t ht
  have e1 := hA A (le_rfl) s hsQ
  have e2 := hA A (le_rfl) u huQ
  rw [hst] at e1
  rw [hut] at e2
  rcases abs_lt_bounds e0 with ⟨e0lo, e0hi⟩
  rcases abs_lt_bounds e1 with ⟨e1lo, e1hi⟩
  rcases abs_lt_bounds e2 with ⟨e2lo, e2hi⟩
  have s1 := hparity s hsQ
  have s2 := hparity u huQ
  rw [hopen] at s2
  have hsmall : |C t| < |C t| / 2 := by
    rcases lt_or_gt_of_ne hnonzero with hctneg | hctpos
    · rw [abs_of_neg hctneg] at e0lo e0hi e1lo e1hi e2lo e2hi ⊢
      rcases paritySign_cases (phase + s) with hsgn | hsgn
      · rw [hsgn] at s1 s2
        norm_num at s1 s2
        linarith
      · rw [hsgn] at s1 s2
        norm_num at s1 s2
        linarith
    · rw [abs_of_pos hctpos] at e0lo e0hi e1lo e1hi e2lo e2hi ⊢
      rcases paritySign_cases (phase + s) with hsgn | hsgn
      · rw [hsgn] at s1 s2
        norm_num at s1 s2
        linarith
      · rw [hsgn] at s1 s2
        norm_num at s1 s2
        linarith
  linarith

/-- The exact Part-B contradiction: one nonzero parity coefficient excludes normality. -/
theorem uniform_nonzero_parity_not_normal
    (x : bitstream) (H : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (phase Q : ℕ)
    (hfinite : FiniteObservations x H)
    (huniform : UniformTailLimit Q H C)
    (hparity : WeakParity phase Q C)
    (hnonzero : ∃ t : ℕ, Q ≤ t ∧ C t ≠ 0) :
    ¬ normal x := by
  intro hnormal
  rcases hnonzero with ⟨t, ht, hct⟩
  exact hct (normal_uniform_parity_forces_zero x H C phase Q
    hnormal hfinite huniform hparity t ht)

/-- Preferred strict-sign wrapper. -/
theorem uniform_strict_parity_not_normal
    (x : bitstream) (H : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (phase Q : ℕ)
    (hfinite : FiniteObservations x H)
    (huniform : UniformTailLimit Q H C)
    (hstrict : StrictParity phase Q C) :
    ¬ normal x := by
  apply uniform_nonzero_parity_not_normal x H C phase Q hfinite huniform
  · intro t ht
    exact le_of_lt (hstrict t ht)
  · refine ⟨Q, le_rfl, ?_⟩
    intro hz
    have hq := hstrict Q le_rfl
    rw [hz] at hq
    simp at hq

end ANCHOPI.PartB
