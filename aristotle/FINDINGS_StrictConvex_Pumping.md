# Does the "square, expand with the inner product, let `s → ∞`" step generalize?
**Question.** In the necessity proof, the *pumping/support inequality* — push a test point
`z_s = x + s·u` out along a ray, use that its nearest point on `A = S x` is the radial tip
`y(u) = x + R(u)·u`, **square** the distance inequality, **expand with the inner product**, and let
**`s → ∞`** — yields `⟪u, a − x⟫ ≤ R(u)` for every `a ∈ A` (formalized as
`VeryGoodConstant.inner_le_reach`). Does this argument hold only for the `ℓᵖ` metric, or for every
strictly-convex metric? If not, generalize it; if yes, explain exactly how.
---
## Short answer
Two different things must be separated.
1. **The literal computation is `ℓ²`-only (Hilbert), not even general `ℓᵖ`.**
   "Square the distance and expand" uses the inner-product identity
   `‖s·u − w‖² = s²‖u‖² − 2s⟪u,w⟫ + ‖w‖²`, then cancels `s²` and divides by `2s`. There is **no
   inner product** in `ℓᵖ` for `p ≠ 2`, so this exact manipulation does not even survive to a
   general `ℓᵖ`, let alone an arbitrary metric.
2. **The *idea* — extract a support inequality by letting the test point run out along the ray —
   generalizes to every normed space whose norm is differentiable at the direction `u`** (which is
   *almost every* direction for any norm). The two `ℓ²`-specific ingredients are replaced as follows:
   | Euclidean (`ℓ²`) object | general strictly-convex replacement |
   |---|---|
   | inner product `⟪u, ·⟫` | `f = D‖·‖(u)`, the **derivative of the norm at `u`** (the *supporting functional* of the unit ball at `u`; `f u = ‖u‖`, `‖f‖ = 1`) |
   | "square, expand, ÷ `2s`" | the **first-order asymptotic expansion of the norm along the ray** — exactly what `s → ∞` reads off |
   | correction term `(‖w‖² − R²)/(2s)` | the generic `o(1)` remainder of that expansion (the Euclidean term is just its closed form) |
So the answer is: **the support inequality generalizes to every strictly-convex metric**, but you
must drop the inner product and replace it by the norm's gradient, and replace squaring by the
first-order expansion.
## The generalized statement — formalized
This is made precise and machine-checked in `RequestProject/PumpingGeneral.lean`
(no `sorry`; axioms `propext, Classical.choice, Quot.sound`). For **any** real normed space `E`:
* `PumpingGeneral.tendsto_pump (u w : E) (f : E →L[ℝ] ℝ) (hf : HasFDerivAt (‖·‖) f u)` :
  ```
  Tendsto (fun s : ℝ => s * ‖u‖ - ‖s • u - w‖) atTop (𝓝 (f w)).
  ```
  This is the metric-free heart of "let `s → ∞`": the limit of `s‖u‖ − ‖s·u − w‖` is `f w`, the
  value of the norm's derivative at `u` on the displacement `w`.
* `PumpingGeneral.support_le … (hev : ∀ᶠ s in atTop, s * ‖u‖ - ‖s • u - w‖ ≤ R) : f w ≤ R` :
  the inequality actually used. Combined with the geometric fact `dist(z_s, A) = s‖u‖ − R(u)`
  (because the radial tip is the unique nearest point), this is the support inequality
  `f(a − x) ≤ R(u)` in a general normed space.
* `PumpingGeneral.tendsto_pump_inner (u w : F) (hu : ‖u‖ = 1)` (inner-product `F`) :
  ```
  Tendsto (fun s : ℝ => s - ‖s • u - w‖) atTop (𝓝 (inner ℝ u w)),
  ```
  the **Euclidean special case**: there the norm's derivative at a unit `u` is `⟪u, ·⟫`, so the
  general limit collapses to the inner product, recovering exactly the statement that the
  "square-and-divide-by-`2s`" computation proves in `VeryGoodConstant.inner_le_reach`.
### Why the limit is `f w` (the one-line derivation behind `tendsto_pump`)
Write `g(t) = ‖u − t·w‖`. The norm being differentiable at `u` with derivative `f` gives, by the
chain rule, `g'(0) = f(−w) = −f(w)` and `g(0) = ‖u‖`. For `s > 0`,
`s·u − w = s·(u − s⁻¹·w)`, so `‖s·u − w‖ = s·g(s⁻¹)` and
```
s‖u‖ − ‖s·u − w‖ = s(g(0) − g(s⁻¹)) = −(g(s⁻¹) − g(0))/s⁻¹ = −slope_g(0)(s⁻¹) ⟶ −g'(0) = f(w).
```
That single use of the *derivative of the norm* is the general-metric stand-in for the inner-product
expansion. In `ℓ²` the slope has the exact closed form with the `(‖w‖² − R²)/(2s)` correction;
in a general strictly-convex norm the same slope converges, but only the limit (not a clean
algebraic identity) is available.
## Where strict convexity is the precise dividing line
* **Existence of `f`.** A norm is differentiable at almost every direction (a convex function is
  differentiable a.e.); so `f = D‖·‖(u)` exists for a.e. `u` *for any norm*. This is automatic.
* **Uniqueness/radiality of the nearest point.** "the nearest point of `z_s` is *the* tip `y(u)`" —
  needed so that `dist(z_s, A) = s‖u‖ − R(u)` *exactly* — is where **strict convexity** enters.
  In `ℓ¹`/`ℓ^∞` the unit ball has flat faces, nearest points tie and fall off the ray, and the
  premise of the pumping step fails. (This matches `FINDINGS_StrictConvex.md`: very good ⟺
  cap-valued holds in every strictly-convex norm and fails exactly for the non-strictly-convex ones.)
* **From "support = radial in every direction" to a sphere.** The comparison step
  `R(u)·⟪u,v⟫ ≤ R(v)` becomes `R(u)·f_v(u) ≤ R(v)` (and symmetrically), with `f_v(u) → 1` as
  `u → v` by continuity of the dual map; chaining around the circle still forces `R` constant.
  Strict convexity keeps `f_v` single-valued so the support point stays radial; without it the
  support "point" is a whole face and the conclusion collapses.
**Bottom line.** Replace `⟪u,·⟫` by the norm's gradient at `u` and replace squaring by the
norm's first-order expansion, and the pumping/support inequality — hence the whole necessity
argument — holds in every strictly-convex metric, not just `ℓᵖ`. `ℓ¹`/`ℓ^∞` are excluded for the
*same* reason as everywhere else in this project: they are not strictly convex.
---
## P.S. — but `s` does **not** really go to infinity (we are bounded inside the simplex)
This is an important and correct objection. Inside the standard simplex `D`, a test point
`z_s = x + s·u` must stay in `D`, so `s` can be pushed only up to the simplex's own radial reach
`S(u)` in that direction — never to `∞`. So what is the honest status of "`s → ∞`"?
**1. A single finite `s` already gives an *approximate* support inequality; `s → ∞` only kills the
remainder.** For any `R(u) < s ≤ S(u)`, very-goodness gives `‖z_s − a‖ ≥ s‖u‖ − R(u)`, i.e. the
finite-`s` **(PUMP)** inequality
```
   f(a − x) ≤ R(u) + ε(s),     ε(s) = (‖a−x‖² − R(u)²)/(2s)   in ℓ²,   ε(s) = o(1) in general,
```
with `ε(s) = O(1/s) → 0`. Geometrically, from a finite `s` the set `A` only avoids the **open ball**
`B(z_s, s‖u‖ − R(u))`; this sphere flattens into the supporting **half-space** `{f ≤ R(u)}` only as
`s → ∞`. So the role of "`s → ∞`" is **solely to drive the `O(1/s)` residual to `0`** (equivalently
to flatten the avoided sphere into a half-plane); it is not needed for anything else.
**2. The clean limit is legitimized by reducing to the whole plane — which is exactly what the
formalization does.** `RequestProject/VeryGoodConstant.lean` proves the constant-reach / "`A` is a
ball" theorem in the **whole plane `ℂ`**, where test points may sit *anywhere* and `s` genuinely
ranges to `∞`, so the limit is exact and the support inequality `inner_le_reach` is the clean one
(no residual). The passage from the bounded simplex `D` to this whole-plane statement is the
**active/inactive truncation** ("Step 4" of `FINDINGS_VeryGood.md`):
* *Inactive directions* — where the value `S x` already reaches `∂D` — impose **no** constraint;
  the cap is simply cut off by `∂D` there, so no large `s` is needed or available.
* *Active directions* — where the cap sits **strictly inside** `D` — have genuine room
  (`S(u) > R(u)` with a uniform gap), and there the local behaviour is identical to the whole-plane
  one. The constant-reach conclusion is a statement about this interior region, where the idealized
  argument applies verbatim.
**3. If one refuses the whole-plane idealization, keep the residual.** One never has to take a true
`s → ∞`: carry the explicit `O(1/s)` term and evaluate at the largest available `s = S(u)`. The
final equality `R ≡ r` is then obtained from a *different* limit — the **angular subdivision**
`cos^k(θ/k) → 1` as the number of steps `k → ∞` (`VeryGoodConstant.cos_pow_tendsto`,
`chain`, `reach_le`) — which is internal to the comparison of nearby directions and has **nothing to
do with `s`**. So the only genuinely unbounded limit needed for constancy is `k → ∞` (fine angular
subdivision), not `s → ∞`; the bounded `s ≤ S(u)` enters only through the harmless residual `ε(s)`.
In one sentence: **`s → ∞` is an idealization whose sole job is to remove an `O(1/s)` residual; the
bounded simplex is handled either by isolating the geometric core in the whole plane (formalized) and
truncating to `D` on the active/inactive split, or by keeping the residual and finishing with the
separate `k → ∞` angular-subdivision limit.**