import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Central

/-!
# Kummer's and Raabe's tests for series of positive terms

The ratio test says nothing when `aₙ / aₙ₊₁ → 1`. Kummer's test refines it with an auxiliary
sequence `pₙ`, and Raabe's test is the special case `pₙ = n`, which settles series such as
`∑ C(2n, n) / 4ⁿ` where the ratio test fails.

## Main results

* `ClassicalAnalysis.summable_of_kummer`, `ClassicalAnalysis.not_summable_of_kummer`:
  Kummer's test. If `pₙ > 0` and `pₙ aₙ / aₙ₊₁ - pₙ₊₁ ≥ c > 0` eventually, then `∑ aₙ`
  converges. If instead `∑ 1 / pₙ` diverges and `pₙ aₙ / aₙ₊₁ - pₙ₊₁ ≤ 0` eventually, then
  `∑ aₙ` diverges.
* `ClassicalAnalysis.summable_of_raabe`, `ClassicalAnalysis.not_summable_of_raabe`:
  Raabe's test, with eventual bounds on `n (aₙ / aₙ₊₁ - 1)`.
* `ClassicalAnalysis.summable_of_tendsto_raabe`,
  `ClassicalAnalysis.not_summable_of_tendsto_raabe`: the limit form of Raabe's test.
* `ClassicalAnalysis.not_summable_centralBinom_div_four_pow` and
  `ClassicalAnalysis.summable_centralBinom_div_four_pow_mul`: two series whose ratio tends
  to `1`, decided by Raabe's test.

## References

* K. Knopp, *Theory and Application of Infinite Series*.
* E. E. Kummer, *Über die Convergenz und Divergenz der unendlichen Reihen*, J. Reine Angew.
  Math. 13 (1835).
* J. L. Raabe, *Untersuchungen über die Convergenz und Divergenz der Reihen*, Z. Phys. Math. 10
  (1832).
-/

open Filter Finset Topology

namespace ClassicalAnalysis

variable {a p : ℕ → ℝ}

/-- **Kummer's test**, convergence half. If `pₙ > 0` and `pₙ aₙ / aₙ₊₁ - pₙ₊₁ ≥ c` for some
`c > 0` and all large `n`, then the series of positive terms `∑ aₙ` converges. -/
theorem summable_of_kummer (ha : ∀ n, 0 < a n) (hp : ∀ᶠ n in atTop, 0 < p n) {c : ℝ}
    (hc : 0 < c) (h : ∀ᶠ n in atTop, c ≤ p n * a n / a (n + 1) - p (n + 1)) :
    Summable a := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.and h)
  have key (n : ℕ) (hn : N ≤ n) : c * a (n + 1) ≤ p n * a n - p (n + 1) * a (n + 1) := by
    have h1 := (hN n hn).2
    rw [le_sub_iff_add_le, le_div_iff₀ (ha _)] at h1
    linarith
  -- Telescoping: the partial sums of the tail are bounded by `p N * a N / c`.
  have tele (m : ℕ) :
      c * ∑ i ∈ range m, a (i + (N + 1)) ≤ p N * a N - p (N + m) * a (N + m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, mul_add, show m + (N + 1) = N + m + 1 by omega,
        show N + (m + 1) = N + m + 1 by omega]
      linarith [key (N + m) (by omega)]
  have bound (m : ℕ) : ∑ i ∈ range m, a (i + (N + 1)) ≤ p N * a N / c := by
    rw [le_div_iff₀ hc]
    have := (mul_pos (hN (N + m) (by omega)).1 (ha (N + m))).le
    linarith [tele m]
  exact (summable_nat_add_iff (N + 1)).1 <|
    summable_of_sum_range_le (fun i => (ha _).le) bound

/-- **Kummer's test**, divergence half. If `pₙ > 0` eventually, `∑ 1 / pₙ` diverges and
`pₙ aₙ / aₙ₊₁ - pₙ₊₁ ≤ 0` for all large `n`, then the series of positive terms `∑ aₙ`
diverges. -/
theorem not_summable_of_kummer (ha : ∀ n, 0 < a n) (hp : ∀ᶠ n in atTop, 0 < p n)
    (hdiv : ¬Summable fun n => 1 / p n)
    (h : ∀ᶠ n in atTop, p n * a n / a (n + 1) - p (n + 1) ≤ 0) : ¬Summable a := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.and h)
  -- From `N` on, `pₙ aₙ` is nondecreasing, so `aₙ ≥ (p N * a N) / pₙ`.
  have mono (m : ℕ) : p N * a N ≤ p (m + N) * a (m + N) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := (hN (m + N) (by omega)).2
      rw [sub_nonpos, div_le_iff₀ (ha _)] at h1
      rw [show m + 1 + N = m + N + 1 by omega]
      linarith
  have hC : 0 < p N * a N := mul_pos (hN N le_rfl).1 (ha N)
  intro hs
  refine hdiv <| (summable_nat_add_iff N).1 <|
    (((summable_nat_add_iff N).2 hs).div_const (p N * a N)).of_nonneg_of_le
      (fun i => (one_div_pos.2 (hN (i + N) (by omega)).1).le) fun i => ?_
  rw [div_le_div_iff₀ (hN (i + N) (by omega)).1 hC]
  linarith [mono i]

/-- **Raabe's test**, convergence half. If `n (aₙ / aₙ₊₁ - 1) ≥ r` for some `r > 1` and all large
`n`, then the series of positive terms `∑ aₙ` converges. -/
theorem summable_of_raabe (ha : ∀ n, 0 < a n) {r : ℝ} (hr : 1 < r)
    (h : ∀ᶠ n : ℕ in atTop, r ≤ n * (a n / a (n + 1) - 1)) : Summable a := by
  refine summable_of_kummer (p := fun n => (n : ℝ)) ha ?_ (sub_pos.2 hr) ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  · filter_upwards [h] with n hn
    push_cast
    linarith [show (n : ℝ) * a n / a (n + 1) - (n + 1) = n * (a n / a (n + 1) - 1) - 1 by ring]

/-- **Raabe's test**, divergence half. If `n (aₙ / aₙ₊₁ - 1) ≤ 1` for all large `n`, then the
series of positive terms `∑ aₙ` diverges. -/
theorem not_summable_of_raabe (ha : ∀ n, 0 < a n)
    (h : ∀ᶠ n : ℕ in atTop, n * (a n / a (n + 1) - 1) ≤ 1) : ¬Summable a := by
  refine not_summable_of_kummer (p := fun n => (n : ℝ)) ha ?_ Real.not_summable_one_div_natCast ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  · filter_upwards [h] with n hn
    push_cast
    linarith [show (n : ℝ) * a n / a (n + 1) - (n + 1) = n * (a n / a (n + 1) - 1) - 1 by ring]

/-- **Raabe's test**, limit form: if `n (aₙ / aₙ₊₁ - 1) → L > 1`, then `∑ aₙ` converges. -/
theorem summable_of_tendsto_raabe (ha : ∀ n, 0 < a n) {L : ℝ} (hL : 1 < L)
    (h : Tendsto (fun n : ℕ => n * (a n / a (n + 1) - 1)) atTop (𝓝 L)) : Summable a := by
  obtain ⟨r, h1r, hrL⟩ := exists_between hL
  exact summable_of_raabe ha h1r (h.eventually_const_le hrL)

/-- **Raabe's test**, limit form: if `n (aₙ / aₙ₊₁ - 1) → L < 1`, then `∑ aₙ` diverges. -/
theorem not_summable_of_tendsto_raabe (ha : ∀ n, 0 < a n) {L : ℝ} (hL : L < 1)
    (h : Tendsto (fun n : ℕ => n * (a n / a (n + 1) - 1)) atTop (𝓝 L)) : ¬Summable a :=
  not_summable_of_raabe ha (h.eventually_le_const hL)

/-! ### Two series decided by Raabe's test -/

private lemma centralBinom_succ (n : ℕ) :
    ((n + 1).centralBinom : ℝ) = 2 * (2 * n + 1) / (n + 1) * n.centralBinom := by
  have h : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) = 2 * (2 * n + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  field_simp
  linarith

/-- The series `∑ C(2n, n) / 4ⁿ` diverges. Its ratio `aₙ₊₁ / aₙ = (2n + 1) / (2n + 2)` tends to
`1`, so the ratio test is inconclusive, but `n (aₙ / aₙ₊₁ - 1) = n / (2n + 1) ≤ 1`. -/
theorem not_summable_centralBinom_div_four_pow :
    ¬Summable fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n := by
  have hpos (n : ℕ) : 0 < (n.centralBinom : ℝ) / 4 ^ n := by
    have := n.centralBinom_pos
    positivity
  refine not_summable_of_raabe hpos (Eventually.of_forall fun n => ?_)
  have hc : (0 : ℝ) < n.centralBinom := by exact_mod_cast n.centralBinom_pos
  have : (n : ℝ) * ((n.centralBinom : ℝ) / 4 ^ n / (((n + 1).centralBinom : ℝ) / 4 ^ (n + 1)) - 1)
      = n / (2 * n + 1) := by
    rw [centralBinom_succ, pow_succ]
    field_simp
    ring
  rw [this, div_le_one (by positivity)]
  linarith

/-- The series `∑ C(2n, n) / (4ⁿ (2n + 1))` converges (its sum is `π / 2`, the value of the
arcsine series at `1`). Again the ratio tends to `1`, while `n (aₙ / aₙ₊₁ - 1) → 3 / 2`. -/
theorem summable_centralBinom_div_four_pow_mul :
    Summable fun n : ℕ => (n.centralBinom : ℝ) / (4 ^ n * (2 * n + 1)) := by
  have hpos (n : ℕ) : 0 < (n.centralBinom : ℝ) / (4 ^ n * (2 * n + 1)) := by
    have := n.centralBinom_pos
    positivity
  refine summable_of_raabe hpos (r := 5 / 4) (by norm_num) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (0 : ℝ) < n.centralBinom := by exact_mod_cast n.centralBinom_pos
  have : (n : ℝ) * ((n.centralBinom : ℝ) / (4 ^ n * (2 * n + 1)) /
      (((n + 1).centralBinom : ℝ) / (4 ^ (n + 1) * (2 * ↑(n + 1) + 1))) - 1)
      = n * (6 * n + 5) / (2 * n + 1) ^ 2 := by
    rw [centralBinom_succ, pow_succ]
    push_cast
    field_simp
    ring
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith

end ClassicalAnalysis
