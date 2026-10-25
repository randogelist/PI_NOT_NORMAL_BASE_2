import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace AWPIWordAnchor

/-- Ordinary epsilon convergence, written with two strict inequalities. -/
def tends_to (f : ℕ → ℝ) (ell : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ cutoff : ℕ, ∀ n : ℕ, cutoff ≤ n →
      -eps < f n - ell ∧ f n - ell < eps

/-- A fixed negative gap occurs arbitrarily far out. -/
def negative_often (f : ℕ → ℝ) : Prop :=
  ∃ eta : ℝ, 0 < eta ∧
    ∀ cutoff : ℕ, ∃ n : ℕ, cutoff ≤ n ∧ f n ≤ -eta

theorem tends_to_ext {f g : ℕ → ℝ} {ell : ℝ}
    (hfg : ∀ n, f n = g n) (hf : tends_to f ell) : tends_to g ell := by
  intro eps heps
  rcases hf eps heps with ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, ?_⟩
  intro n hn
  simpa [← hfg n] using hcutoff n hn

theorem tends_to_zero_sum {f g : ℕ → ℝ}
    (hf : tends_to f 0) (hg : tends_to g 0) :
    tends_to (fun n => f n + g n) 0 := by
  intro eps heps
  have he : 0 < eps / 2 := by linarith
  rcases hf (eps / 2) he with ⟨nf, hnf⟩
  rcases hg (eps / 2) he with ⟨ng, hng⟩
  refine ⟨nf + ng, ?_⟩
  intro n hn
  have hfn := hnf n (by omega)
  have hgn := hng n (by omega)
  constructor <;> linarith

theorem tends_to_extension_difference {f g : ℕ → ℝ} {p : ℝ}
    (hf : tends_to f p) (hg : tends_to g (p / 2)) :
    tends_to (fun n => g n - f n / 2) 0 := by
  intro eps heps
  have he : 0 < eps / 4 := by linarith
  rcases hf (eps / 4) he with ⟨nf, hnf⟩
  rcases hg (eps / 4) he with ⟨ng, hng⟩
  refine ⟨nf + ng, ?_⟩
  intro n hn
  have hfn := hnf n (by omega)
  have hgn := hng n (by omega)
  constructor <;> linarith

theorem bounded_product_zero {f p : ℕ → ℝ}
    (hf : tends_to f 0)
    (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1) :
    tends_to (fun n => f n * p n) 0 := by
  intro eps heps
  rcases hf eps heps with ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, ?_⟩
  intro n hn
  have hfn := hcutoff n hn
  have hpn := hp n
  by_cases hpos : 0 ≤ f n
  · constructor <;> nlinarith
  · have hneg : f n < 0 := lt_of_not_ge hpos
    constructor <;> nlinarith

theorem zero_limit_excludes_negative_often {f : ℕ → ℝ}
    (hlim : tends_to f 0) : ¬ negative_often f := by
  rintro ⟨eta, heta, hbad⟩
  have he : 0 < eta / 2 := by linarith
  rcases hlim (eta / 2) he with ⟨cutoff, hcutoff⟩
  rcases hbad cutoff with ⟨n, hn, hnegative⟩
  have hnear := hcutoff n hn
  linarith

theorem covariance_limit_transfer
    {defect covariance delta p : ℕ → ℝ}
    (hid : ∀ n, defect n = covariance n - delta n * p n)
    (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hdelta : tends_to delta 0)
    (hdefect : tends_to defect 0) :
    tends_to covariance 0 := by
  have hproduct : tends_to (fun n => delta n * p n) 0 :=
    bounded_product_zero hdelta hp
  have hsum : tends_to (fun n => defect n + delta n * p n) 0 :=
    tends_to_zero_sum hdefect hproduct
  apply tends_to_ext (ell := 0) (f := fun n => defect n + delta n * p n)
      (g := covariance)
  · intro n
    have h := hid n
    linarith
  · exact hsum

end AWPIWordAnchor
