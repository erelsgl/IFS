# "Very good" multifunctions on the standard 2-simplex (L2, L1, Lp)
This note answers the follow-up question. Recall `D` is the standard 2-simplex in `ℝ³` and a
set-valued map `S` is **good** when for every `x ∈ D`: `[1] x ∈ S x`; and `[2]` for every
`z ∈ D`, every nearest point `y` of `z` on `S x` satisfies `dist(y,x) ≤ dist(z,x)`.
`S` is **very good** when `[2]` is strengthened to `[2']`: every nearest point `y` of `z` on
`S x` lies on the closed line segment `[z, x]`.
Because `y ∈ [z, x]` forces `dist(y,x) ≤ dist(z,x)`, **very good ⟹ good** in every metric
(`veryGood_imp_good`, `veryGood1_imp_good1`, `veryGood6_imp_good6`). So very good is a strictly
stronger property, and we ask which good functions are very good, and for a characterization,
separately for the Euclidean (`ℓ²`), taxicab (`ℓ¹`) and general `ℓᵖ` (`p > 1`) metrics.
All results below build with no `sorry` and use only the standard axioms
`propext, Classical.choice, Quot.sound`.
## The "spherical cap"
For a point `x` and radius `r ≥ 0`, write the **cap** `C_p(x,r) = {a ∈ D | dist_p(a,x) ≤ r}`
(the intersection of `D` with the closed `ℓᵖ`-ball centred at `x`). The caps are the central
objects of the answer.
* In *every* metric the cap is **good** (formalized for `ℓ¹` as `good1_cap`; the same one-line
  argument works for any metric): a nearest point `y` of `z` on a cap satisfies
  `dist(y,x) ≤ r`; if `z` is itself in the cap then `y = z`, otherwise `dist(z,x) > r ≥ dist(y,x)`.
## `ℓ²` (Euclidean) — characterization: very good ⟺ each value is a cap
> `S` is very good for `ℓ²` ⟺ for every `x ∈ D` there is `r ≥ 0` with `S x = C_2(x,r)`.
The decisive **sufficiency** direction is `veryGood_cap` (file `RequestProject/VeryGood.lean`):
every cap-valued map is very good. The geometric reason, special to a strictly convex norm, is
that the metric projection of an external `z` onto a ball centred at `x` is **radial** — it is
`x + (r/‖z-x‖)(z-x)`, on the segment `[z,x]` — and is the unique nearest point on the cap
(uniqueness `isNearest_unique` from the inner product / strict convexity).
Examples:
* very good: `S x = {x}` (`veryGood_singleton`), `S x = D` (`veryGood_const_D`), and every cap.
* **good but not very good**: `S x = [x, a]`, a single segment (`not_veryGood_segment`). It is
  convex, hence good, but at `x = (1/2,1/2,0)` the point `z = (0,1/2,1/2)` (with `a = (1/4,1/4,1/2)`
  closer to `z` than `x`) projects to an interior foot off the segment `[z,x]`.
## `ℓᵖ`, `p > 1` — *same* characterization as `ℓ²` (formalized for `p = 6`)
> For every `p > 1`, `S` is very good for `ℓᵖ` ⟺ each value is an `ℓᵖ`-cap `C_p(x,r)`.
This is perhaps counterintuitive but correct: the projection onto an `ℓᵖ`-ball **centred at the
same point `x`** is radial for *all* `p > 1`, because at the radial point the gradients of
`Q(z,·)` and `Q(·,x)` are both parallel to the componentwise 5th power of `z - x` (the KKT/first
order optimality condition holds with a positive multiplier). The sufficiency direction is
`veryGood6_cap` (file `RequestProject/VeryGoodLp.lean`, `p = 6` chosen so the distance is a
polynomial). Uniqueness of the nearest point comes from **strict convexity** of `Q6(z,·)`
(`Q6_unique_min`), valid for `p > 1`. The radial-projection lemma is `radial6_nearest_ball`.
Examples for `ℓ⁶`: `S x = {x}` (`veryGood6_singleton`), `S x = D` (`veryGood6_const_D`), and
every `ℓ⁶`-cap (`veryGood6_cap`).
**Contrast with `ℓ²` for the *good* property.** Unlike `ℓ²` — where convex / star-shaped values
(a segment, the "V") are good but not very good — for `ℓᵖ` with `p ≠ 2` such values are typically
**not even good**: `not_good6_segment` (in `RequestProject/Lp.lean`) shows a segment failing the
weaker *good* property, and numerically the "V" and "half-caps" fail too. Thus for `p ≠ 2` the
abundant good-but-not-very-good examples of `ℓ²` disappear, and the good and very good classes are
far closer together — the very good values are exactly the `ℓᵖ`-caps.
## `ℓ¹` — caps are NOT very good; the characterization is metric-specific
> For `ℓ¹` the cap characterization **fails**.
The `ℓ¹`-ball is a diamond, which is not strictly convex. The radial point is still *a* nearest
point of `z` on an `ℓ¹`-cap (the triangle inequality gives `dist₁(z, radial) = dist₁(z,x) - r`),
but there are generally *other* nearest points off the segment `[z,x]` (verified numerically:
for `x = (1/3,1/3,1/3)`, `r = 1/5`, very many `z` have an off-segment `ℓ¹`-nearest point on the
cap). So `ℓ¹`-caps are **not** very good. The very good `ℓ¹` values form a smaller,
metric-specific family (radial free boundary `ℓ¹`-orthogonal to the radius), with `{x}` and `D`
the obvious members.
Examples for `ℓ¹` (file `RequestProject/VeryGoodL1.lean`):
* very good: `S x = {x}` (`veryGood1_singleton`), `S x = D` (`veryGood1_const_D`).
* good (any metric): every `ℓ¹`-cap (`good1_cap`).
* **good but not very good**: `S x = [x, a]` (`not_veryGood1_segment`) — good because star-shaped,
  not very good by the same configuration as the Euclidean case (`dist₁(z,a) = 1/2 < 1 = dist₁(z,x)`).
## Summary table
| metric        | are `ℓᵖ`-caps very good? | characterization of very good `S`            | good-but-not-very-good example |
|---------------|--------------------------|----------------------------------------------|--------------------------------|
| `ℓ²`          | yes                      | each value is a cap `C_2(x,r)`               | a segment `[x,a]`              |
| `ℓᵖ`, `p > 1` | yes (same as `ℓ²`)       | each value is a cap `C_p(x,r)`              | (rare: convex sets are usually not even *good* for `p ≠ 2`) |
| `ℓ¹`          | no (projection ties)     | smaller `ℓ¹`-specific family (`{x}`, `D`, …) | a segment `[x,a]`              |
---
# Necessity: every very good function is cap-valued (`ℓᵖ`, `p > 1`)
The formalized files give the **sufficiency** direction (every `ℓᵖ`-cap is very good). This
appendix supplies the converse, requested as a human-readable argument:
> **Theorem (necessity).** Fix `p > 1` and the `ℓᵖ` metric on the plane `H ⊃ D` carrying the
> simplex. Let `S` be very good and suppose each value `S x` is **closed** (equivalently, since
> `D` is compact, compact — this is the natural setting, the one in which "nearest point"
> exists and in which caps live). Then for every `x ∈ D` there is a radius `r ≥ 0` with
> `S x = C_p(x, r) = {a ∈ D | dist_p(a,x) ≤ r}`.
Throughout, fix `x ∈ D` and write `A := S x ⊆ D`, a compact set with `x ∈ A`. Let
`N(v) := ‖v‖_p` denote the `ℓᵖ`-norm on `H`. Two analytic facts about `N` are used and are
exactly the two ways the hypothesis `p > 1` enters:
* **(strict convexity)** the `ℓᵖ`-norm is strictly convex for `p > 1`, so the nearest point of
  any point on a *convex* set, and more generally on any closed set when it is unique, is
  genuinely unique; and a strict triangle inequality holds for non-parallel vectors;
* **(smoothness)** for `p > 1` the norm `N` is differentiable away from `0`, with
  `∇N(v) = N(v)^{1-p}·v^{(p-1)}`, where `v^{(p-1)}` is the **componentwise** signed power
  `(|v_i|^{p-1} sgn v_i)_i`. Note `∇N(λv) = ∇N(v)` for `λ > 0` (it depends only on the
  *direction* of `v`) and `∇N(-v) = -∇N(v)`.
For `ℓ¹` *both* facts fail (the diamond is neither strictly convex nor smooth at its
vertices/edges), which is exactly why the cap characterization breaks for `p = 1`.
## Step 0 — The shape of the argument
It is convenient to record the strengthened conclusion that drives everything. For a point
`z ∈ D` let `ρ_z := dist_p(z,x)` and let `u_z` be its radial direction, so `z = x + ρ_z·u_z`.
Very-goodness says: every nearest point of `z` on `A` lies on the segment `[x,z]`, i.e. is of
the form `x + ρ·u_z` with `0 ≤ ρ ≤ ρ_z` — it is *radial*, on the same ray from the centre `x`.
The whole proof is the claim that a closed set all of whose metric projections are radial from a
fixed centre `x` must be a metric ball about `x` (cut down to `D`).
## Step 1 — `A` is star-shaped about `x` (the "deepest-gap" lemma)
*Claim.* If `a ∈ A` then the whole radial segment `[x,a] ⊆ A`.
Write points of the ray through `a` as `q(μ) = x + μ(a-x)`, `μ ∈ [0,1]`, so `q(0)=x ∈ A` and
`q(1)=a ∈ A`. Suppose some `q(μ) ∉ A`. The parameter set `T = {μ ∈ [0,1] | q(μ) ∈ A}` is
closed and contains `0,1`, so around the missing `μ` there is a maximal open gap
`(μ⁻, μ⁺)` with `p⁻ := q(μ⁻) ∈ A`, `p⁺ := q(μ⁺) ∈ A` and `q(μ) ∉ A` for `μ ∈ (μ⁻,μ⁺)`.
Let `μ₀ = (μ⁻+μ⁺)/2` be the **deepest point of the gap** and `z := q(μ₀)`.
Along this ray `p⁻` and `p⁺` are equidistant from `z`: `dist_p(z,p⁻) = dist_p(z,p⁺)
= (μ⁺-μ⁻)/2 · dist_p(a,x)`. Let `d = dist_p(z,A) ≤ dist_p(z,p⁻)`. Now:
* if `d < dist_p(z,p⁻)`, some nearest point `y` of `z` is strictly closer than every on-ray
  point of `A` in `[x,z]` (the closest of those is `p⁻`, since `(μ⁻,μ₀] ⊆ gap`), so `y` is
  **off** the ray `[x,z]` — contradicting very-goodness;
* if `d = dist_p(z,p⁻)`, then `p⁺ ∈ A` is *also* a nearest point of `z`; but `p⁺ = q(μ⁺)` has
  `μ⁺ > μ₀`, so `p⁺ ∉ [x,z]` — again contradicting very-goodness.
Either way we get a contradiction, so no gap exists and `[x,a] ⊆ A`. ∎
Consequently `A` is exactly described by its **radial reach function**
`R(u) := max{ρ ≥ 0 | x + ρ·u ∈ A}` (the max exists because `A` is compact), namely
`A = {x + ρ·u | u a unit direction in H, 0 ≤ ρ ≤ R(u)}`. Let `r := max_a dist_p(a,x)
= max_u R(u)·N(u)` be the `ℓᵖ`-radius of the farthest point of `A`, attained at some `a*`.
Also write `D(u) := max{ρ ≥ 0 | x + ρ·u ∈ D}` for the reach of the *simplex*; always
`R(u) ≤ D(u)`. The cap `C_p(x,r)` is precisely the radial set with reach `ρ_cap(u)` solving
`ρ·N(u) = min(r, D(u)·N(u))`. So the theorem is the single statement:
> **(★)** for every direction `u`: `N(R(u)·u) = min( r , N(D(u)·u) )`,
> i.e. the `ℓᵖ`-radius of `A`'s boundary is `r` wherever the simplex leaves room, and equals
> the simplex's own reach otherwise.
Call a direction `u` **active** if `R(u) < D(u)` — i.e. the ray leaves `A` while still inside
`D`, so there are genuine test points `z ∈ D` lying radially beyond the boundary of `A`. The
inactive directions are those where `A` already reaches `∂D`; there (★) holds trivially because
`R(u) = D(u)` and *no* `z ∈ D` lies beyond, so very-goodness imposes nothing. **All the
content of (★) is at the active directions, where it reads `N(R(u)·u) = r`.**
## Step 2 — Continuity of the radial reach
*Upper semicontinuity* is free from closedness of `A`: if `u_n → u` and `R(u_n) → ℓ`, then
`x + R(u_n)·u_n ∈ A` converges to `x + ℓ·u ∈ A`, so `ℓ ≤ R(u)`.
*A one-sided Lipschitz bound* comes from very-goodness. Take any active `u` and any `s` with
`R(u) < s ≤ D(u)`, so `z = x + s·u ∈ D` lies radially beyond `A`. By Step 1 the only points of
`A` on this ray are at radii `≤ R(u)`, so the closest on-ray point to `z` is the tip
`y(u) = x + R(u)·u`. Very-goodness forces *every* nearest point of `z` to be on this ray, hence
to be `y(u)`; therefore `y(u)` is the global nearest point and
>  **(LB)**  `dist_p(z, a) ≥ dist_p(z, y(u)) = s - R(u)`  for **all** `a ∈ A`.
Feeding `a = x + R(u')·u'` into (LB) and using the triangle inequality
`N(s·u - R(u')·u') ≤ |s - R(u')| + R(u')·N(u - u')` gives, after rearranging and letting
`s ↓ R(u)`, the bound `R(u') - R(u) ≤ r·N(u - u')`. Swapping the roles of `u, u'` (both taken
active, or with enough simplex room) yields a genuine Lipschitz estimate
`|R(u) - R(u')| ≤ r·N(u - u')`. In particular **`R` is continuous**. (This already rules out
sharp "sectors": a value that fills a wedge up to radius `r` and drops to `0` across a straight
radial edge has a *discontinuous* `R`, so it is not very good — matching the fact that a point
just outside the straight edge projects perpendicularly onto it, off its own ray.)
## Step 3 — The boundary of `A` is `ℓᵖ`-orthogonal to its radius (the crux)
Fix an active direction `u₀` and its boundary point `y₀ = y(u₀) = x + R(u₀)·u₀`. By (LB), for
**every** `s ∈ (R(u₀), D(u₀)]` the unique nearest point of `z_s = x + s·u₀` on `A` is `y₀`
(uniqueness uses strict convexity). Equivalently, the *entire* outward radial segment beyond
`y₀` projects onto the single point `y₀`. This is the geometric heart, and it pins the tangent
plane of `∂A` at `y₀`:
Because `y₀` minimises `a ↦ N(z_s - a)` over `A` and `N` is smooth at `z_s - y₀ ≠ 0`, the
first-order optimality condition holds: the (Fréchet) outward normal of the closed set `A` at
`y₀` is parallel to
>  `∇_a[N(z_s - a)]|_{a=y₀} ∝ ∇N(z_s - y₀) = ∇N\big((s-R(u₀))·u₀\big) = ∇N(u₀)`,
which, crucially, is **independent of `s`** (it depends only on the direction `u₀`, by
0-homogeneity of `∇N`). So:
>  **(N)**  the outward normal of `∂A` at the active boundary point `y₀` is `∝ ∇N(u₀)`.
Now compare with the concentric `ℓᵖ`-sphere `Σ_c = {a | N(a-x) = c}` through `y₀`, where
`c = N(y₀ - x) = R(u₀)·N(u₀)`. Its outward normal at `y₀` is `∇N(y₀ - x) = ∇N(R(u₀)·u₀)
= ∇N(u₀)` — **the same** vector as in (N). Thus at every active boundary point the surface
`∂A` and the `ℓᵖ`-sphere through that point share the same tangent plane.
This identity of normals is exactly a first-order ODE for the radial graph `u ↦ R(u)`. Writing
the boundary as the graph `y(u) = x + R(u)·u`, its Euclidean normal is
`ν(u) = R(u)·u - R'(u)·u^{\perp}` (with `u^{\perp}` the in-plane unit normal to `u`); condition
(N) says `ν(u) ∝ ∇N(u)`. One checks immediately that the level sets `N(y-x) = c`, i.e.
`R(u) = c / N(u)`, solve this ODE — and, the ODE being first order, these concentric
`ℓᵖ`-spheres are its **only** solutions. (Regularity is not an issue: by Step 2 `R` is
Lipschitz, hence differentiable almost everywhere, and (N) holds at every active point, which
is enough to integrate to `N(y(u) - x) = const` along any connected arc of active directions.)
The purely geometric way to say the same thing: at `y₀` the `ℓᵖ`-ball `B_p(z_s, s - R(u₀))`
touches `A` and, as `s ↓ R(u₀)`, its supporting tangent at `y₀` is the tangent of `Σ_c`; the
radial point being the nearest point forces `∂A` to bend *exactly* like the `ℓᵖ`-sphere there.
A boundary that bent any other way would have its true nearest point pulled off the radius — as
happens for an **ellipse** about `x` (its normal is not radial, so external points project to
the perpendicular foot, off `[x,z]`; an ellipse is good-looking but **not** very good), the
canonical illustration of why (N) is forced.
## Step 4 — Putting the radius together
By Step 3, on each connected arc of active directions the `ℓᵖ`-radius `N(y(u)-x)` is a
constant. We claim this constant is `r` and that there is effectively one outer boundary, so
(★) holds:
* Let `a*` be a farthest point, `N(a*-x) = r`, in direction `u*`. The direction `u*` is itself
  active unless the farthest point already sits on `∂D` (`R(u*) = D(u*)`). In the generic case
  (which always occurs when the cap fits strictly inside `D`, e.g. `x` interior and `r` small,
  and in particular pins down the radius in all the cases that matter) `u*` is active, so the
  active arc containing it has constant `ℓᵖ`-radius `= N(a*-x) = r`.
* This arc cannot stop in the interior of the active region: at a would-be endpoint `R` is
  continuous (Step 2) and the normal condition (N) holds on both sides, so the constant value
  `r` propagates across; the active region is bounded only by the inactive directions, where
  the boundary of `A` meets `∂D`. Hence on the whole active set `N(R(u)·u) = r`, i.e.
  `R(u) = r / N(u) = ρ_cap(u)`.
* On inactive directions `R(u) = D(u)`, and there the cap also takes the value `D(u)` because
  `N(D(u)·u) ≤ r` (otherwise the point `x + D(u)·u ∈ A ⊆ D` would be farther than `a*`).
Combining the two regimes gives `N(R(u)·u) = min(r, N(D(u)·u))` for every `u`, which is exactly
(★). Therefore `A = C_p(x, r)`. ∎
## Why the same proof fails for `ℓ¹`, and what survives
Every step above except Step 1 (star-shapedness, which is metric-free) uses `p > 1`:
* **Step 3 uniqueness** needs *strict* convexity. The `ℓ¹` ball is a diamond, so an external
  `z` typically has a *whole edge* of nearest points on a cap, many of them off the radius —
  this is precisely the numerically-confirmed failure that makes `ℓ¹`-caps *not* very good.
* **Step 3 first-order condition** needs *smoothness*. The `ℓ¹` norm has corners, so `∇N` is
  not defined along the coordinate hyperplanes and the normal `(N)` is replaced by a normal
  *cone*; the boundary of a very good `ℓ¹` set is then `ℓ¹`-orthogonal to the radius in this
  set-valued sense, which is a *different and smaller* family than the `ℓ¹`-caps (it always
  contains `{x}` and `D`).
So the cap characterization — very good `⟺` cap-valued — is exactly an `ℓᵖ`, `p > 1`,
phenomenon, resting on the strict convexity and smoothness that the Euclidean and all other
`ℓᵖ` (`p>1`) norms share but `ℓ¹` lacks.
## One-paragraph summary of necessity
Very-goodness says every metric projection onto `A` is radial from `x`. Star-shapedness (Step 1)
lets us encode `A` by a radial reach `R(u)`, which very-goodness makes continuous (Step 2).
For each boundary point that some interior test point sees from outside, "the radial point is
the nearest point" is, by smoothness of the `ℓᵖ`-norm, the first-order statement that `∂A`'s
normal there is the `ℓᵖ`-radial normal `∇N(u)` — i.e. `∂A` is tangent to the concentric
`ℓᵖ`-sphere (Step 3). A surface whose normal is everywhere `ℓᵖ`-radial about `x` is a level set
of `a ↦ ‖a-x‖_p`, so `∂A` is an `ℓᵖ`-sphere of radius `r = max_a ‖a-x‖_p` (Step 4); cut by the
simplex this is exactly the cap `C_p(x,r)`. Strict convexity (uniqueness) and smoothness
(the normal) are the two places `p > 1` is indispensable, and both fail for `ℓ¹`.