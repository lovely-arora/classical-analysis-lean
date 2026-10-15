import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Carleman's inequality

For a sequence of nonnegative reals `a₁, a₂, …`, **Carleman's inequality** states that
`∑ₙ (a₁ ⋯ aₙ) ^ (1 / n) ≤ e * ∑ₙ aₙ`.

We follow Pólya's proof. With the weights `cₖ = (k + 1) ^ k / k ^ (k - 1)`, whose partial products
telescope to `c₁ ⋯ cₙ = (n + 1) ^ n`, the AM–GM inequality gives
`(a₁ ⋯ aₙ) ^ (1 / n) = (a₁c₁ ⋯ aₙcₙ) ^ (1 / n) / (n + 1) ≤ (∑_{k ≤ n} aₖcₖ) / (n (n + 1))`.
Summing over `n` and exchanging the order of summation (an Abel summation, using
`∑_{n ≥ k} 1 / (n (n + 1)) = 1 / k`) bounds the left-hand side by
`∑ₖ aₖcₖ / k = ∑ₖ aₖ (1 + 1 / k) ^ k ≤ e * ∑ₖ aₖ`.

In this file sequences are indexed from `0`, so `a 0` plays the role of `a₁`.

## Main results

* `ClassicalAnalysis.carleman_sum_le`: the finite form of Carleman's inequality,
  `∑_{n < N} (a 0 ⋯ a n) ^ (1 / (n + 1)) ≤ e * ∑_{n < N} a n`.
* `ClassicalAnalysis.carleman`: for a summable sequence of nonnegative reals, the series of
  geometric means is summable and its sum is at most `e * ∑' n, a n`.

## References

* T. Carleman, *Sur les fonctions quasi-analytiques*, Conférences faites au cinquième congrès des
  mathématiciens scandinaves, Helsingfors (1923), 181–196.
* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, Cambridge University Press, 1934,
  §9.12.
-/

open Finset

namespace ClassicalAnalysis

/-- The weights `(k + 2) ^ (k + 1) / (k + 1) ^ k` of Pólya's proof of Carleman's inequality
(indexed from `0`). Their partial products telescope, see `prod_range_carlemanWeight`. -/
private noncomputable def carlemanWeight (k : ℕ) : ℝ :=
  (k + 2 : ℝ) ^ (k + 1) / (k + 1) ^ k

/-- The weights of Pólya's proof are nonnegative. -/
private lemma carlemanWeight_nonneg (k : ℕ) : 0 ≤ carlemanWeight k := by
  unfold carlemanWeight
  positivity

/-- The partial products of the weights telescope: `c 0 ⋯ c (m - 1) = (m + 1) ^ m`. -/
private lemma prod_range_carlemanWeight (m : ℕ) :
    ∏ k ∈ range m, carlemanWeight k = (m + 1 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ih, carlemanWeight]
    push_cast
    field_simp
    ring

/-- Dividing the `k`-th weight by `k + 1` gives `(1 + 1 / (k + 1)) ^ (k + 1)`, which is at
most `e`. -/
private lemma carlemanWeight_div (k : ℕ) :
    carlemanWeight k / (k + 1) = (1 + ((k + 1 : ℕ) : ℝ)⁻¹) ^ (k + 1) := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  rw [carlemanWeight, div_div, ← pow_succ, ← div_pow]
  congr 1
  push_cast
  field_simp
  ring

/-- The AM–GM step: the geometric mean of `a 0, …, a n` is bounded by a weighted arithmetic
mean. -/
private lemma geom_mean_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ)) ≤
      (∑ k ∈ range (n + 1), a k * carlemanWeight k) / ((n + 1) * (n + 2)) := by
  have hP : 0 ≤ ∏ k ∈ range (n + 1), a k := prod_nonneg fun k _ => ha k
  have amgm := Real.geom_mean_le_arith_mean (range (n + 1)) (fun _ => 1)
    (fun k => a k * carlemanWeight k) (fun _ _ => zero_le_one)
    (by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]; positivity)
    (fun k _ => mul_nonneg (ha k) (carlemanWeight_nonneg k))
  simp only [Real.rpow_one, one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at amgm
  rw [prod_mul_distrib, prod_range_carlemanWeight, Real.mul_rpow hP (by positivity),
    Real.pow_rpow_inv_natCast (by positivity) n.succ_ne_zero,
    le_div_iff₀ (by positivity)] at amgm
  have hexp : (1 / (n + 1 : ℝ)) = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    push_cast
    exact one_div _
  rw [hexp, le_div_iff₀ (by positivity)]
  convert amgm using 1
  push_cast
  ring

/-- Abel summation for the weights `1 / ((n + 1) * (n + 2))`, whose tails telescope. -/
private lemma sum_range_partial_sum_div (x : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, (∑ k ∈ range (n + 1), x k) / ((n + 1) * (n + 2)) +
        (∑ k ∈ range N, x k) / (N + 1) =
      ∑ k ∈ range N, x k / (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun n => (∑ k ∈ range (n + 1), x k) / ((n + 1) * (n + 2))),
      sum_range_succ (fun k => x k / (k + 1)), ← ih, sum_range_succ x]
    push_cast
    field_simp
    ring

/-- **Carleman's inequality**, finite form. -/
theorem carleman_sum_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    ∑ n ∈ range N, (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ)) ≤
      Real.exp 1 * ∑ n ∈ range N, a n := by
  have hx : ∀ k, 0 ≤ a k * carlemanWeight k := fun k =>
    mul_nonneg (ha k) (carlemanWeight_nonneg k)
  calc ∑ n ∈ range N, (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ))
      ≤ ∑ n ∈ range N, (∑ k ∈ range (n + 1), a k * carlemanWeight k) / ((n + 1) * (n + 2)) :=
        sum_le_sum fun n _ => geom_mean_le a ha n
    _ ≤ ∑ k ∈ range N, a k * carlemanWeight k / (k + 1) := by
        rw [← sum_range_partial_sum_div]
        have : 0 ≤ (∑ k ∈ range N, a k * carlemanWeight k) / (N + 1) :=
          div_nonneg (sum_nonneg fun k _ => hx k) (by positivity)
        linarith
    _ ≤ ∑ k ∈ range N, Real.exp 1 * a k := by
        refine sum_le_sum fun k _ => ?_
        rw [mul_div_assoc, carlemanWeight_div, mul_comm]
        exact mul_le_mul_of_nonneg_right Real.one_add_inv_pow_le_exp (ha k)
    _ = Real.exp 1 * ∑ n ∈ range N, a n := (mul_sum _ _ _).symm

/-- **Carleman's inequality**: for a summable sequence of nonnegative reals the series of
geometric means converges, and its sum is at most `e` times the sum of the sequence. -/
theorem carleman (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Summable (fun n : ℕ => (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ))) ∧
      ∑' n, (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ)) ≤ Real.exp 1 * ∑' n, a n := by
  have hg : ∀ n : ℕ, 0 ≤ (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ)) := fun n =>
    Real.rpow_nonneg (prod_nonneg fun k _ => ha k) _
  have hle : ∀ N, ∑ n ∈ range N, (∏ k ∈ range (n + 1), a k) ^ (1 / (n + 1 : ℝ)) ≤
      Real.exp 1 * ∑' n, a n := fun N =>
    (carleman_sum_le a ha N).trans <|
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun i _ => ha i) (Real.exp_pos 1).le
  exact ⟨summable_of_sum_range_le hg hle, Real.tsum_le_of_sum_range_le hg hle⟩

end ClassicalAnalysis
