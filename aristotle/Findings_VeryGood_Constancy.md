# Formalization of the "no cavity" argument: the radial reach of a very good set is constant
This note documents the new file `RequestProject/VeryGoodConstant.lean`, which **formalizes the
argument requested in the follow-up**:
> After Step 1 we know a very good value `A` is star-shaped about its centre `x`, hence described
> by its radial reach `R(u)`.  It remains to prove `R` is constant.  Suppose not; near a minimum
> of `R` there is a "cavity" in `A`, and a point placed in that cavity close to the higher "wall"
> would have a non-radial nearest point in `A`, contradicting very-goodness.  Hence no cavity is
> possible and `R` is constant.
Everything builds with no `sorry`; the two headline theorems depend only on the standard axioms
`propext, Classical.choice, Quot.sound`.
## Setting
The argument is carried out in the plane `ℂ`, regarded as a 2-dimensional **real** inner product
space — this is exactly the affine hull of the simplex `D`, the natural arena for a radial reach.
We fix a set `A : Set ℂ` and a centre `x`, and assume:
* `hA : IsCompact A` (closed values are the natural setting — "nearest point" must exist);
* `hxA : x ∈ A`;
* `hstar : StarConvex ℝ x A` (Step 1, taken as given, as the question does);
* `hVG : VeryGoodAt A x`, i.e. `∀ z y, IsNearest A z y → y ∈ segment ℝ x z`: every nearest point
  of every test point projects **radially** onto the radius `[x, z]`.
This is the **whole-plane** form of very-goodness (test points anywhere in `ℂ`); it isolates the
geometric heart — constancy of the reach — from the simplex-truncation bookkeeping ("Step 4").
The radial reach is `reach A x u := sSup {t ≥ 0 | x + t·u ∈ A}`; for a unit `u` the supremum is
attained, so the radial tip `x + reach A x u · u` lies in `A` (`tip_mem`).
## How the "cavity" contradiction is made precise (the pumping inequality)
The cavity picture is turned into one quantitative inequality.  For a far external test point
`z_s = x + s·u` (`s > R(u)`), very-goodness forces the **only** nearest point of `z_s` on `A` to
be the radial tip `x + R(u)·u` (`tip_isNearest_of_gt`): any nearest point is radial (hypothesis)
and star-shapedness caps its radius at `R(u)`.  Hence `dist(z_s, a) ≥ s − R(u)` for every `a ∈ A`.
Squaring, expanding with the inner product, and letting `s → ∞` (a "cavity" near `u` cannot keep
the tip the closest point for all far `z_s` unless `A` does not stick out past the tip) yields the
> **pumping / support inequality** (`inner_le_reach`): for all `a ∈ A`, `⟪u, a − x⟫ ≤ R(u)`.
Geometrically: *the radial tip is the support point of `A` in direction `u`*.  This is the formal
content of "no point of the cavity wall pokes past the radial tip."
## From the support inequality to constancy
Feeding the tip of one direction as a test point for another gives the elementary comparison
(`key`):
> `R(u) · ⟪u, w⟫ ≤ R(w)`  for all unit `u, w`.
Constancy then follows by **chaining around the circle**, which is where `ℂ` makes the geometry
clean: multiplying by the unit complex number `ζ = exp(i·θ/k)` rotates a direction by `θ/k`, and
`⟪u·ζ^j, u·ζ^{j+1}⟫ = cos(θ/k)`.  Iterating `key` `k` times (`chain`) gives
`R(u) · cos(θ/k)^k ≤ R(w)` where `w = u · exp(iθ)`.  Since `cos(θ/k)^k → 1` (`cos_pow_tendsto`),
taking `k → ∞` yields `R(u) ≤ R(w)` (`reach_le`); by symmetry `R` is **constant** (`reach_const`).
## Conclusion
A very good (compact, star-shaped) set is exactly a Euclidean ball about its centre
(`eq_closedBall`):
> `A = Metric.closedBall x (reach A x 1)`.
This is the cavity-argument incarnation of the necessity direction: combined with the already
formalized sufficiency (`VeryGoodStrictConvex.veryGood_cap`, every cap/ball is very good), it
pins down the very good values as exactly the balls (caps, after simplex truncation).
## Statement map (`RequestProject/VeryGoodConstant.lean`)
| name | statement |
|------|-----------|
| `inner_le_reach` | pumping/support inequality `⟪u, a−x⟫ ≤ R(u)` |
| `key` | `R(u)·⟪u,w⟫ ≤ R(w)` |
| `chain` | per-`k` chained estimate `R(u)·cos(θ/k)^j ≤ R(u·ζ^j)` |
| `cos_pow_tendsto` | `cos(θ/k)^k → 1` |
| `reach_le` / `reach_const` | `R(u) ≤ R(w)` / `R` is constant |
| `eq_closedBall` | `A = closedBall x (R(1))` |