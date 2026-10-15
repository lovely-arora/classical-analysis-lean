# Classical analysis in Lean 4

Formal proofs, in Lean 4 with Mathlib, of a few classical results about series and
inequalities that Mathlib does not have yet. Everything is proved from scratch: no `sorry`, and
only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Contents

| File | Result | Main declarations |
|---|---|---|
| [`SeriesTests.lean`](ClassicalAnalysis/SeriesTests.lean) | Kummer's test (both halves) | `summable_of_kummer`, `not_summable_of_kummer` |
| | Raabe's test, bound and limit forms | `summable_of_raabe`, `not_summable_of_raabe`, `summable_of_tendsto_raabe`, `not_summable_of_tendsto_raabe` |
| | Two series where the ratio test fails: `∑ C(2n,n)/4ⁿ` diverges, `∑ C(2n,n)/(4ⁿ(2n+1))` converges | `not_summable_centralBinom_div_four_pow`, `summable_centralBinom_div_four_pow_mul` |
| [`Carleman.lean`](ClassicalAnalysis/Carleman.lean) | Carleman's inequality `∑ (a₁⋯aₙ)^(1/n) ≤ e ∑ aₙ`, finite and series forms | `carleman_sum_le`, `carleman` |
| [`Hardy.lean`](ClassicalAnalysis/Hardy.lean) | Hardy's inequality `∑ ((a₁+⋯+aₙ)/n)^p ≤ (p/(p-1))^p ∑ aₙ^p` for real `p > 1`, finite and series forms | `hardy_sum_le`, `hardy` |

All declarations live in the `ClassicalAnalysis` namespace. Sequences are indexed from `0`, so
`a 0` plays the role of `a₁` in the textbook statements.

## A few notes on the proofs

* **Kummer and Raabe.** The convergence half of Kummer's test is a telescoping bound
  `c · aₙ₊₁ ≤ pₙ aₙ - pₙ₊₁ aₙ₊₁` on the tail of the series. Raabe's test is Kummer's test with
  `pₙ = n`, and the divergence half compares `aₙ` with the harmonic series.
* **Carleman.** The proof follows Pólya: rescale `aₖ` by `cₖ = (k+1)ᵏ / kᵏ⁻¹`, so that
  `c₁⋯cₙ = (n+1)ⁿ`, apply AM-GM to each geometric mean, swap the order of summation and finish
  with `(1 + 1/k)ᵏ ≤ e`.
* **Hardy.** The proof is Elliott's: Young's inequality gives a telescoping bound for
  `αₙᵖ - p/(p-1) · aₙ αₙᵖ⁻¹`, where `αₙ` is the n-th average, and Hölder's inequality closes it.

## Building

The project is pinned to Lean `v4.33.0-rc1` and Mathlib commit `9944fe2`.

```bash
lake exe cache get
lake build
```

CI runs the same build on every push.

## References

* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press,
  1952 (Theorems 326 and 334).
* K. Knopp, *Theory and Application of Infinite Series*, Blackie, 1951.
* E. B. Elliott, *A simple exposition of some recently proved facts as to convergency*,
  J. London Math. Soc. 1 (1926).
* T. Carleman, *Sur les fonctions quasi-analytiques*, 1923.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).
