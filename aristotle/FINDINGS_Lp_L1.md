# Characterizations of "good" multifunctions for the ℓᵖ and ℓ¹ metrics

This note records the answer to the follow-up question: characterize the *good*
set-valued maps `S` on the standard 2-simplex `D ⊂ ℝ³` when "nearest" and "dist" are
measured in the ℓᵖ metric (`p > 1`), and separately in the ℓ¹ metric.

Recall `S` is **good** iff for every `x ∈ D`: `[1] x ∈ S x`; and `[2]` for every `z ∈ D`,
every nearest point `y` of `z` on `S x` satisfies `dist(y,x) ≤ dist(z,x)`.

For the **Euclidean** metric (`p = 2`, the original problem, in `RequestProject/Main.lean`)
the answer is: `S` is good ⟺ each value `S x` is **star-shaped about `x`**.

## Answer for ℓ¹ — same as Euclidean: star-shapedness

For the ℓ¹ (taxicab) metric the characterization is **the same as Euclidean**:

> `S` is good for ℓ¹ ⟺ each value `S x` is star-shaped with respect to `x`.

The decisive (sufficiency) direction is fully formalized in `RequestProject/L1.lean`:
`good1_of_starConvex` — if every `S x ⊆ D` contains `x` and is star-shaped about `x`,
then `S` is good for ℓ¹. The geometric core is `l1_segment_key`: on the affine plane of the
simplex (where coordinate differences sum to zero), the ℓ¹-nearest point of `z` on a segment
emanating from `x` is never farther from `x` than `z` is. (This uses a weighted-median /
sign analysis special to mean-zero ℓ¹ geometry; it is genuinely false off the simplex
plane.) Necessity is witnessed, as in the Euclidean case, by non-star-shaped examples
failing `[2]` (`not_good1_twoPoint`).

Examples (all in `L1.lean`): `good1_const_D` (`S x = D`), `good1_singleton` (`S x = {x}`),
`good1_V` (the non-convex "V" `S x = [x,e₁] ∪ [x,e₂]`) are good; `not_good1_twoPoint`
(`S x = {x, e₁}`) is not.

## Answer for ℓᵖ, `p > 1` — star-shapedness is NOT sufficient

This is the surprising part. For the ℓᵖ metric with `p > 1` the naive expectation — that
strict convexity of the ball makes the Euclidean characterization (star-shaped) carry over —
**is false** for every `p ∉ {2}` (and, curiously, the boundary value `p = 4` also happens
to behave like `p = 2`; all other `p > 1` exhibit the failure).

> For ℓᵖ with `p > 1`, `p ≠ 2`: star-shapedness of the values is **necessary but not
> sufficient**.  Even a *convex* value — a single segment `[x, a]` — can violate `[2]`.

The correct characterization, valid for any metric, is the **projection / ball** condition,
which is exactly what `[2]` says:

> `S` is good ⟺ for every `x, z ∈ D`, every ℓᵖ-nearest point of `z` on `S x` lies in the
> closed ℓᵖ-ball `B̄_p(x, dist_p(z,x))`.

For `p = 2` (and `p = 1`) this collapses to star-shapedness; for general `p > 1` it is
*strictly stronger*.

### The formal counterexample (`RequestProject/Lp.lean`, exponent `p = 6`)

`p = 6` is chosen because the ℓ⁶-distance is a polynomial, so the witness is verified by
exact rational arithmetic. `not_good6_segment` proves that the reflexive,
star-shaped-valued (indeed convex-valued) map

  `S x = segment[x, a]`,  with fixed `a = (61/100, 17/100, 11/50) ∈ D`,

is **not** good for ℓ⁶. At `x = (9/200, 3/8, 29/50) ∈ D`, the point
`z = (59/100, 19/100, 11/50) ∈ D` — which is *closer* to `x` than `a` is — has its
unique ℓ⁶-nearest point on `[x,a]` strictly *farther* from `x` than `z` is, violating `[2]`.

The proof obtains the nearest point `y` by compactness, writes `y = x + s•(a−x)`, and uses
convexity of the distance-to-`z` function along the segment together with a rational
"bracket" (`t₀ = 967/1000`, `t₁ = 1209/1250`) to force the minimizing parameter `s > t₀`,
whence `dist(y,x) > dist(z,x)`.

`Lp.lean` also records the contrasting good examples that survive for ℓ⁶:
`good6_singleton` (`S x = {x}`) and `good6_const_D` (`S x = D`). The point is precisely that
the *intermediate* star-shaped values (segments) need not be good, while the extreme ones
still are.

## Summary table

| metric        | characterization of good `S`                          |
|---------------|-------------------------------------------------------|
| ℓ² (Euclid.)  | each `S x` star-shaped about `x`                       |
| ℓ¹            | each `S x` star-shaped about `x` (same as Euclidean)  |
| ℓᵖ, `p > 1`   | nearest points stay in `B̄_p(x, dist_p(z,x))`; strictly stronger than star-shaped for `p ≠ 2` |

All results build with no `sorry` and use only the standard axioms
`propext, Classical.choice, Quot.sound`.
