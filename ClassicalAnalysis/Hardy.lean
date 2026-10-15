import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Hardy's inequality

This file proves Hardy's inequality for sequences: if `p > 1` and `a₀, a₁, …` are nonnegative real
numbers, then the averages `αₙ = (a₀ + ⋯ + aₙ) / (n + 1)` satisfy
`∑ₙ αₙ ^ p ≤ (p / (p - 1)) ^ p * ∑ₙ aₙ ^ p`.

Sequences are indexed from `0`, so `a 0` plays the role of the first term `a₁` in the classical
statement, and `x ^ p` denotes the real power `Real.rpow`.

## Main results

* `ClassicalAnalysis.hardy_sum_le`: Hardy's inequality for the partial sums up to any `N`.
* `ClassicalAnalysis.hardy`: Hardy's inequality for series: if `∑ aₙ ^ p` converges, then so
  does `∑ αₙ ^ p`, and its sum is at most `(p / (p - 1)) ^ p * ∑ aₙ ^ p`.

## Implementation notes

We follow Elliott's proof. In the `1`-indexed notation `Aₙ = a₁ + ⋯ + aₙ`, `αₙ = Aₙ / n`, we have
`aₙ = n αₙ - (n - 1) αₙ₋₁`, and Young's inequality applied to `αₙ₋₁ αₙ ^ (p - 1)` gives

`αₙ ^ p - p / (p - 1) * aₙ * αₙ ^ (p - 1) ≤ ((n - 1) * αₙ₋₁ ^ p - n * αₙ ^ p) / (p - 1)`.

The right-hand side telescopes, so `∑ αₙ ^ p ≤ p / (p - 1) * ∑ aₙ αₙ ^ (p - 1)`, and Hölder's
inequality bounds the last sum by `(∑ aₙ ^ p) ^ (1 / p) * (∑ αₙ ^ p) ^ (1 - 1 / p)`.

The constant `(p / (p - 1)) ^ p` is known to be optimal; this is not proved here.

## References

* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press,
  1952, Theorem 326.
* E. B. Elliott, *A simple exposition of some recently proved facts as to convergency*,
  J. London Math. Soc. 1 (1926), 93–96.
-/

open Finset Real

namespace ClassicalAnalysis

/-- The pointwise estimate behind Elliott's proof. In the `1`-indexed notation of the module
docstring, it is applied with `x = αₙ` and `y = αₙ₊₁`, so that `(n + 1) * y - n * x = aₙ₊₁`. -/
private lemma elliott_step {p : ℝ} (hp : 1 < p) {x y n : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : 0 ≤ n) :
    y ^ p - p / (p - 1) * (((n + 1) * y - n * x) * y ^ (p - 1)) ≤
      (n * x ^ p - (n + 1) * y ^ p) / (p - 1) := by
  have hpq : p.HolderConjugate (p / (p - 1)) := (holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hp₀ : p ≠ 0 := hpq.ne_zero
  have hp₁ : p - 1 ≠ 0 := hpq.sub_one_ne_zero
  have hy' : y * y ^ (p - 1) = y ^ p := by
    rw [← rpow_one_add' hy (by simpa using hp₀), add_sub_cancel]
  have young : x * y ^ (p - 1) ≤ x ^ p / p + y ^ p / (p / (p - 1)) := by
    simpa only [← rpow_mul hy, hpq.sub_one_mul_conj] using
      young_inequality_of_nonneg hx (rpow_nonneg hy (p - 1)) hpq
  calc y ^ p - p / (p - 1) * (((n + 1) * y - n * x) * y ^ (p - 1))
      = y ^ p - p / (p - 1) * (n + 1) * (y * y ^ (p - 1)) +
          p / (p - 1) * n * (x * y ^ (p - 1)) := by ring
    _ ≤ y ^ p - p / (p - 1) * (n + 1) * y ^ p +
          p / (p - 1) * n * (x ^ p / p + y ^ p / (p / (p - 1))) := by
        rw [hy']
        exact add_le_add le_rfl <|
          mul_le_mul_of_nonneg_left young (mul_nonneg (div_pos hpq.pos hpq.sub_one_pos).le hn)
    _ = (n * x ^ p - (n + 1) * y ^ p) / (p - 1) := by
        field_simp
        ring

/-- The averages of a nonnegative sequence are nonnegative. -/
private lemma avg_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ (∑ k ∈ range (n + 1), a k) / (n + 1) :=
  div_nonneg (sum_nonneg fun k _ => ha k) n.cast_add_one_pos.le

/-- Elliott's telescoping estimate: `∑ αₙ ^ p ≤ p / (p - 1) * ∑ aₙ αₙ ^ (p - 1)`. -/
private lemma sum_rpow_avg_le {p : ℝ} (hp : 1 < p) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    ∑ n ∈ range N, ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p ≤
      p / (p - 1) * ∑ n ∈ range N, a n * ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ (p - 1) := by
  -- `f n = n * αₙ ^ p` in the `1`-indexed notation of the module docstring
  let f : ℕ → ℝ := fun n => n * ((∑ k ∈ range n, a k) / n) ^ p
  have hf₀ : f 0 = 0 := by simp [f]
  have hf : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg n.cast_nonneg <|
      rpow_nonneg (div_nonneg (sum_nonneg fun k _ => ha k) n.cast_nonneg) p
  have key : ∀ n, ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p -
      p / (p - 1) * (a n * ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ (p - 1)) ≤
        (f n - f (n + 1)) / (p - 1) := by
    intro n
    have han : a n = (n + 1) * ((∑ k ∈ range (n + 1), a k) / (n + 1)) -
        n * ((∑ k ∈ range n, a k) / n) := by
      rw [mul_div_cancel₀ _ n.cast_add_one_pos.ne', sum_range_succ]
      rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · rw [mul_div_cancel₀ _ (Nat.cast_pos.2 hn).ne']
        ring
    have hfn : f n - f (n + 1) =
        n * ((∑ k ∈ range n, a k) / n) ^ p -
          (n + 1) * ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p := by
      simp only [f, Nat.cast_add, Nat.cast_one]
    rw [hfn, han]
    exact elliott_step hp (div_nonneg (sum_nonneg fun k _ => ha k) n.cast_nonneg)
      (avg_nonneg ha n) n.cast_nonneg
  have hsum := sum_le_sum fun n (_ : n ∈ range N) => key n
  rw [sum_sub_distrib, ← mul_sum, ← sum_div, sum_range_sub' f N, hf₀] at hsum
  have : (0 - f N) / (p - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [hf N]) (sub_pos.2 hp).le
  linarith

/-- If `S ≤ c * (T ^ (1 / p) * S ^ (1 / q))` for conjugate exponents `p` and `q`, then
`S ≤ c ^ p * T`. -/
private lemma le_mul_of_le_mul_rpow {p q S T c : ℝ} (hpq : p.HolderConjugate q) (hS : 0 ≤ S)
    (hT : 0 ≤ T) (hc : 0 ≤ c) (h : S ≤ c * (T ^ (1 / p) * S ^ (1 / q))) : S ≤ c ^ p * T := by
  rcases hS.eq_or_lt with rfl | hS
  · exact mul_nonneg (rpow_nonneg hc p) hT
  have key : S ^ (1 / p) ≤ c * T ^ (1 / p) := by
    refine le_of_mul_le_mul_right ?_ (rpow_pos_of_pos hS (1 / q))
    rwa [← rpow_add hS, hpq.one_div_add_one_div, div_one, rpow_one, mul_assoc]
  calc S = (S ^ (1 / p)) ^ p := by rw [one_div, rpow_inv_rpow hS.le hpq.ne_zero]
    _ ≤ (c * T ^ (1 / p)) ^ p := rpow_le_rpow (rpow_nonneg hS.le _) key hpq.nonneg
    _ = c ^ p * T := by
        rw [mul_rpow hc (rpow_nonneg hT _), one_div, rpow_inv_rpow hT hpq.ne_zero]

/-- **Hardy's inequality**, finite form. -/
theorem hardy_sum_le {p : ℝ} (hp : 1 < p) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    ∑ n ∈ range N, ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p ≤
      (p / (p - 1)) ^ p * ∑ n ∈ range N, a n ^ p := by
  have hpq : p.HolderConjugate (p / (p - 1)) := (holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hq : 0 ≤ p / (p - 1) := (div_pos hpq.pos hpq.sub_one_pos).le
  refine le_mul_of_le_mul_rpow hpq (sum_nonneg fun n _ => rpow_nonneg (avg_nonneg ha n) p)
    (sum_nonneg fun n _ => rpow_nonneg (ha n) p) hq ?_
  refine (sum_rpow_avg_le hp a ha N).trans (mul_le_mul_of_nonneg_left ?_ hq)
  have holder := inner_le_Lp_mul_Lq_of_nonneg (range N) hpq (fun n _ => ha n)
    (fun n _ => rpow_nonneg (avg_nonneg ha n) (p - 1))
  have hα : ∑ n ∈ range N, (((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ (p - 1)) ^ (p / (p - 1)) =
      ∑ n ∈ range N, ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p :=
    sum_congr rfl fun n _ => by rw [← rpow_mul (avg_nonneg ha n), hpq.sub_one_mul_conj]
  rwa [hα] at holder

/-- **Hardy's inequality**: if `∑ aₙ ^ p` converges then so does the series of `p`-th powers
of the averages, with sum at most `(p / (p - 1)) ^ p` times as large. -/
theorem hardy {p : ℝ} (hp : 1 < p) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : Summable fun n => a n ^ p) :
    Summable (fun n : ℕ => ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p) ∧
      ∑' n, ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p ≤ (p / (p - 1)) ^ p * ∑' n, a n ^ p := by
  have h₀ (n : ℕ) : 0 ≤ ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p :=
    rpow_nonneg (avg_nonneg ha n) p
  have hle (N : ℕ) : ∑ n ∈ range N, ((∑ k ∈ range (n + 1), a k) / (n + 1)) ^ p ≤
      (p / (p - 1)) ^ p * ∑' n, a n ^ p :=
    (hardy_sum_le hp a ha N).trans <| mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ fun n _ => rpow_nonneg (ha n) p)
      (rpow_nonneg (div_pos (zero_lt_one.trans hp) (sub_pos.2 hp)).le p)
  exact ⟨summable_of_sum_range_le h₀ hle, Real.tsum_le_of_sum_range_le h₀ hle⟩

end ClassicalAnalysis
