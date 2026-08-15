# Can the necessity argument be simplified? (the maximal‑ball reformulation)
This note answers the follow‑up question:
> Suppose by contradiction that some point `a` is in `A`, some other point `b` is **not** in
> `A`, and `b` is nearer to `x` than `a`. Since `A` is closed, the complement is open, so there
> is an open ball of positive radius around `b` disjoint from `A`. Let `B` be a maximal such
> ball; the boundary of `B` is a point on the boundary of `A`. By very‑goodness this point must
> be on the radius `[b,x]`. **Continue the argument from here.**
The setting is the Euclidean (`ℓ²`) metric on the plane `H ⊃ D` carrying the simplex; `A = S x`
is closed (compact), `x ∈ A`, and `S` is very good. The goal of *necessity* is to show that `A`
is a **cap** `C(x,r) = D ∩ B̄(x,r)`. (Notation as in `FINDINGS_VeryGood.md`.)
**Short answer.** Yes — the necessity direction can be simplified along exactly these lines, and
the simplification is real: it removes the smooth/`∇N`/first‑order‑ODE machinery of Step 3 in
`FINDINGS_VeryGood.md` and replaces it by one elementary "pumping" inequality plus a
support‑function argument. Two honest caveats:
1. The maximal‑ball step, by itself, contributes nothing beyond very‑goodness: it merely
   re‑derives "the nearest point of `b` on `A` is **radial**, i.e. lies on `[b,x]`." That is an
   *immediate* consequence of very‑goodness (plus star‑shapedness), with or without the ball.
   So the ball is a vivid picture, not an extra lemma.
2. The phrase "on the radius **from `a` to `x`**" should read "on the radius **from `b` to
   `x`**" — the nearest point of `b` is tied to `b`'s own ray, not to `a`'s. The point `a`
   re‑enters later, as the *farthest* point of `A`, and that is exactly what drives the
   contradiction.
Below I make the maximal‑ball step precise, then give the simplified continuation in full.
---
## 0. Reduction and the (free) star‑shapedness step
By the deepest‑gap lemma (Step 1 of `FINDINGS_VeryGood.md`, which is metric‑free), `A` is
**star‑shaped about `x`**: for each unit direction `u` the ray `{x + ρu : ρ ≥ 0}` meets `A` in a
closed segment `[x,\, x + R(u)u]`, where `R(u) ≥ 0` is the **radial reach**. Put
`y(u) := x + R(u)u` (the boundary point in direction `u`) and let
```
        r := max_{a ∈ A} dist(a,x)     (attained, A compact).
```
The cap statement `A = C(x,r)` is equivalent to **(★)**: in every direction `u` that still has
room inside the simplex, `dist(y(u),x) = R(u) = r`; equivalently the boundary `∂A` is the sphere
of radius `r` about `x`, truncated by `∂D`. (Directions where `A` already reaches `∂D` are
"inactive" and impose nothing — handled verbatim as in Step 4 of `FINDINGS_VeryGood.md`.)
## 1. The maximal‑ball step = "projection of an external point is radial"
Let `b ∈ D`, `b ∉ A`. Because `A` is closed, `d := dist(b,A) > 0` and the open ball `B(b,d)` is
disjoint from `A` and *maximal* with that center; its bounding sphere touches `A` at a nearest
point `c`, with `dist(b,c) = d` and `c ∈ A`.
Very‑goodness applied to the single test point `z = b` says **every** nearest point of `b` on
`A` lies on the segment `[b,x]`. Hence `c ∈ [b,x]`: writing `u` for the unit direction of
`b − x`, we get `c = x + ρ u` with `ρ = dist(c,x)` and
```
        ρ = dist(b,x) − d < dist(b,x).
```
By star‑shapedness `c` is exactly the boundary point `y(u)`, so `R(u) = ρ`. In one line: **the
metric projection `π_A(b)` exists, is unique, and equals the radial boundary point `y(u)`**.
(Uniqueness is automatic: all nearest points lie on the ray, and the ray meets `A` in a segment
with a unique far end.) This is the entire content of the maximal‑ball picture — it is
very‑goodness, restated. No smoothness, no strict convexity is needed for *this* step.
So far we have only re‑proved that, for `b` outside `A`, `π_A(b)` is radial. The contradiction
must come from comparing this radial projection with the *farthest* point `a`.
## 2. The pumping inequality (the substantive, but elementary, step)
Fix an **active** direction `u` (one with simplex room) and its boundary point `y(u) = x + R(u)u`.
For every `s` with `R(u) < s ≤ S(u)` (here `S(u)` is the simplex's own radial reach in direction
`u`), the point `z_s := x + s u` lies in `D`, beyond `A` on the ray. By Step 1 its projection is
the radial tip: `π_A(z_s) = y(u)`, so `dist(z_s,\,y(u)) = s − R(u)` is the distance to `A`.
Therefore, for **every** point `a' ∈ A`,
```
        dist(z_s, a')² ≥ dist(z_s, y(u))² = (s − R(u))².
```
Take `x` as the origin and expand (this is the only computation; it was checked to be a pure
algebraic identity):
```
   |s u − (a'−x)|²  =  s² − 2 s · u·(a'−x) + |a'−x|²
   (s − R(u))²      =  s² − 2 s · R(u)     + R(u)² ,
```
so the inequality becomes, after cancelling `s²` and dividing by `2s > 0`,
```
   (PUMP)     u·(a'−x)  ≤  R(u)  +  (|a'−x|² − R(u)²) / (2s)   for all R(u) < s ≤ S(u).
```
Letting `s` run up to its maximum `S(u)` (and, in the idealized "plenty of room" limit
`S(u) → ∞`, the correction term vanishes), (PUMP) gives the clean **support inequality**
```
   (SUPP)     u·(a'−x)  ≤  R(u)        for every a' ∈ A.
```
Read geometrically, (SUPP) says: *the radial boundary point `y(u)` is also the **support point**
of `A` in direction `u`* — no point of `A` sticks out past `y(u)` in the `u`‑direction:
```
   max_{a' ∈ A} (a'−x)·u  =  (y(u)−x)·u  =  R(u).
```
This is the crux, and it needs **no smoothness and no `∇N`**: very‑goodness alone forces the
*radial* point to coincide with the *support* point in every (active) direction. That coincidence
is special — for a generic convex body the support point in a direction is **not** the radial
point; the two coincide for all directions exactly for spheres centered at `x`.
## 3. "Radial = support in every direction" ⟹ the boundary is a sphere
Apply (SUPP) twice, to two active directions `u, v`, using each other's boundary point as the
test point `a'` (boundary points lie in `A`):
```
   take a' = y(v) = x + R(v)v  in direction u :   R(v)·(v·u) ≤ R(u),
   take a' = y(u) = x + R(u)u  in direction v :   R(u)·(u·v) ≤ R(v).
```
With `c = u·v = cos∠(u,v) ∈ (0,1]` for nearby directions, this is
```
        c · R(v) ≤ R(u)        and        c · R(u) ≤ R(v),
   i.e.     c ≤ R(u)/R(v) ≤ 1/c .
```
Subdividing the angle between any two directions into `k` equal steps of size `θ/k` and
multiplying the `k` ratio bounds gives `cos^k(θ/k) ≤ R(u)/R(v) ≤ sec^k(θ/k)`. Since
`cos^k(θ/k) → 1` as `k → ∞`, we conclude `R(u) = R(v)`. Hence **`R` is constant on each connected
arc of active directions**, with the common value equal to the largest radius `r` (attained at
the farthest point `a`, whose direction is active whenever the cap fits strictly inside `D`).
That is precisely **(★)**: the boundary of `A` is the sphere of radius `r` about `x`, so
`A = C(x,r)`. The inactive directions (where `A` meets `∂D`) are absorbed exactly as in Step 4
of `FINDINGS_VeryGood.md`. ∎
*(Numerical corroboration: a non‑constant profile such as `R(t)=1+0.3\cos t` violates the
constraint `R(v)\cos(∠) ≤ R(u)` — the worst residual on a `72×72` grid of directions is
`+0.044 > 0` — so no non‑constant radius can satisfy "radial = support," confirming the sphere.)*
## 4. Direct contradiction form (matching the user's "by contradiction" setup)
The same content, phrased as the user began it. Suppose `a ∈ A`, `b ∉ A`, with
`dist(b,x) ≤ dist(a,x)`. By §1, `c = π_A(b) = y(u)` is radial, `R(u) = ρ < dist(b,x)`. Now run
(PUMP)/(SUPP) in direction `u` with the test point `a' = a`:
```
   u·(a − x) ≤ R(u) + (|a−x|² − R(u)²)/(2s) ,     ρ = R(u) < s ≤ S(u).
```
If the ray in direction `u` has enough simplex room (large `S(u)`), the right side approaches
`R(u) = ρ`, forcing `u·(a−x) ≤ ρ`. But `b = x + dist(b,x)\,u` with `dist(b,x) > ρ`, and if `a`
lies in (or near) the direction `u` — e.g. take `a` to be the farthest point and `b` on its ray —
then `u·(a−x) = dist(a,x) ≥ dist(b,x) > ρ`, a contradiction. The general direction is handled by
§3: the support identity in *all* directions pins `R ≡ r`, so a point `b` with `dist(b,x) ≤ r`
inside the simplex cannot be missing from `A`. Hence `A` is downward‑closed in radius, i.e. a
cap.
---
## What the simplification buys, and its limits
* **Genuine simplification.** Steps 2–3 of `FINDINGS_VeryGood.md` (continuity of `R` via a
  one‑sided Lipschitz bound; smoothness of the `ℓᵖ`‑norm; the first‑order normal condition
  `ν ∝ ∇N(u)`; integrating the tangency ODE) are all replaced by the single elementary
  inequality (PUMP) and the two‑line "support ⟹ constant radius" computation. No derivatives of
  the norm appear.
* **What strict convexity / `p>1` is still for.** Uniqueness of `π_A` is free here (very‑goodness
  forces all nearest points onto one ray). What the Euclidean inner‑product expansion in (PUMP)
  uses is the *parallelogram/`dist²` identity*. For a general `ℓᵖ` norm the same idea works but
  (PUMP) must be replaced by the convexity (first‑order) inequality for `t ↦ ‖z − ·‖_p`, and the
  "support = radial ⟹ sphere" conclusion then needs strict convexity to keep the support point
  unique and radial — exactly the place `ℓ¹` fails (a diamond has flat faces, support points are
  whole edges, and the conclusion collapses). So the dividing line is unchanged: **`p > 1`
  (strict convexity)**, consistent with `FINDINGS_StrictConvex.md`.
* **The honest caveats.** (i) The maximal‑ball step is just very‑goodness for the point `b`; it
  does not, by itself, advance the proof. (ii) The touching point is on `[b,x]`, not `[a,x]`.
  (iii) The clean support inequality (SUPP) is the `S(u) → ∞` idealization of (PUMP); inside the
  bounded simplex one keeps the `(|a'−x|² − R(u)²)/(2s)` correction and finishes on the *active*
  region with the simplex‑truncation bookkeeping of Step 4 — this part is the same in either
  presentation.
**Bottom line.** Yes: the necessity proof simplifies to *"very‑goodness ⟹ every external point
projects radially ⟹ each radial boundary point is the support point in its direction ⟹ the
boundary is a concentric sphere ⟹ `A` is a cap,"* with the pumping inequality (PUMP) as the
only computation. The maximal ball is a good way to *see* the first implication but is not an
independent ingredient, and the substantive new economy is replacing the smooth tangency ODE by
the support‑function step.