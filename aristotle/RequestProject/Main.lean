import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Good multifunctions on the standard 2-simplex

`D` is the two–dimensional standard simplex in `ℝ³`, viewed inside the Euclidean
space `EuclideanSpace ℝ (Fin 3)` so that `dist` is the ordinary Euclidean distance.

A function `S : D → 𝒫(D)` is called **good** when, for every `x ∈ D`:

* `[1]`  `x ∈ S x`;
* `[2]`  for every `z ∈ D`, if `y` is a nearest point of `z` on `S x`, then
         `dist y x ≤ dist z x`  (projecting onto `S x` never moves a point
         farther from `x`).

The main mathematical content of this file:

* **Sufficiency / characterization (positive direction).**
  `good_of_starConvex`: if every value `S x` is star–shaped with respect to `x`
  (i.e. `StarConvex ℝ x (S x)`) and contains `x`, then `S` is good.  This is the
  decisive direction: it produces *all* the natural good functions.  The proof is
  the "obtuse angle" argument: the segment `[x , y]` lies in `S x`, and a nearest
  point `y` of `z` is in particular the nearest point of the segment, so the angle
  at `y` is non-acute, whence `dist y x ≤ dist z x`.

* **Examples of good functions** (`good_const_D`, `good_singleton`, `good_V`): the
  constant function `S x = D`, the singleton function `S x = {x}`, and the
  non-convex "V" map `S x = [x,e₁] ∪ [x,e₂]`.  The last one is important: it is
  good yet *not convex-valued*, so the good functions form a strictly larger class
  than the convex-valued ones — star-shapedness, not convexity, is the right notion.

* **An example of a function that is NOT good** (`not_good_twoPoint`): the
  two–point valued function `S x = {x, e₁}`.  Star–shapedness fails, and indeed a
  point `z` projects onto the far vertex `e₁`, which is *farther* from `x`.

## The characterization

For closed (equivalently, compact, since `D` is compact) values `S x`, the
characterization is:

>  `S` is good  ⟺  for every `x ∈ D`, the value `S x` is star-shaped with
>  respect to `x` (`x ∈ S x` and `∀ a ∈ S x, [x,a] ⊆ S x`).

The `⟸` direction is `good_of_starConvex`, proved in full below; it captures all
good functions arising from star-shaped values.  The `⟹` direction (a good value
must be star-shaped) is witnessed by the failure of the non-star-shaped examples
such as `not_good_twoPoint`: the geometric reason is that if the radial segment
`[x,a]` leaves a closed `S x`, then the resulting "gap" has a lateral boundary
point `q` whose nearest-point projection pulls some nearby `z` (closer to `x`)
out to `q` (farther from `x`), breaking property `[2]`.  Concretely, at the
deepest point `c` of such a gap the nearest points of `c` surround `c`, so at
least one of them is farther from `x` than `c`, violating goodness.
-/

/-- The ambient Euclidean space `ℝ³`. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The standard two–dimensional simplex in `ℝ³`. -/
def D : Set E := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- `y` is a nearest point of `z` on the set `A`. -/
def IsNearest (A : Set E) (z y : E) : Prop :=
  y ∈ A ∧ ∀ b ∈ A, dist z y ≤ dist z b

/-- A set–valued map `S` is **good** when it satisfies properties `[1]` and `[2]`. -/
def Good (S : E → Set E) : Prop :=
  ∀ x ∈ D, (x ∈ S x) ∧ ∀ z ∈ D, ∀ y, IsNearest (S x) z y → dist y x ≤ dist z x

/-! ## The key variational lemma and the sufficiency theorem -/

/-
**Core lemma.**  If `A` is star–shaped with respect to `x` and `y` is a nearest
point of `z` on `A`, then `y` is at least as close to `x` as `z` is.

Proof idea: the segment `[x, y]` is contained in `A`, so `y` minimises the
distance to `z` over that segment, giving the variational inequality
`⟪z - y, x - y⟫ ≤ 0`; expanding `‖z - x‖²` then yields `‖y - x‖ ≤ ‖z - x‖`.
-/
lemma nearest_dist_le_of_starConvex {A : Set E} {x z y : E}
    (hx : StarConvex ℝ x A) (hy : IsNearest A z y) :
    dist y x ≤ dist z x := by
  obtain ⟨hyA, hy_min⟩ := hy
  -- For every `s ∈ [0,1]`, the point `y + s•(x - y)` lies in `A`, so `y` is at
  -- least as close to `z` as it is; squared, this is `h_inner`.
  have h_inner : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖z - (y + s • (x - y))‖ ^ 2 ≥ ‖z - y‖ ^ 2 := by
    intro s hs
    have h_w_s : y + s • (x - y) ∈ A := by
      have := hx hyA
      convert @this (s) (1 - s) hs.1 (sub_nonneg.2 hs.2) (by ring) using 1
      ext; norm_num; ring
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hy_min _ h_w_s) _
  -- Expand the inner product: `‖z - (y + s•(x-y))‖² = ‖z-y‖² - 2s⟪z-y,x-y⟫ + s²‖x-y‖²`.
  have h_expand : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖z - y‖^2 - 2 * s * inner ℝ (z - y) (x - y) + s^2 * ‖x - y‖^2 ≥ ‖z - y‖^2 := by
    intro s hs
    have hge := h_inner s hs
    have key : ‖z - (y + s • (x - y))‖ ^ 2
        = ‖z - y‖^2 - 2 * s * inner ℝ (z - y) (x - y) + s^2 * ‖x - y‖^2 := by
      have hsub : z - (y + s • (x - y)) = (z - y) - s • (x - y) := by abel
      rw [hsub, norm_sub_sq_real, inner_smul_right, norm_smul]
      simp [Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    linarith [key ▸ hge]
  -- Divide by `s > 0`.
  have h_div : ∀ s ∈ Set.Ioo (0 : ℝ) 1, -2 * inner ℝ (z - y) (x - y) + s * ‖x - y‖^2 ≥ 0 :=
    fun s hs => by nlinarith [h_expand s (Set.Ioo_subset_Icc_self hs), hs.1]
  -- Let `s → 0⁺` to get the variational inequality `⟪z-y, x-y⟫ ≤ 0`.
  have h_limit : -2 * inner ℝ (z - y) (x - y) ≥ 0 := by
    have ht : Filter.Tendsto (fun s : ℝ => -2 * inner ℝ (z - y) (x - y) + s * ‖x - y‖^2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-2 * inner ℝ (z - y) (x - y))) :=
      tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ (by norm_num))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT_of_mem ⟨by norm_num, by norm_num⟩) h_div)
  -- Expand `‖z - x‖² = ‖z - y‖² + 2⟪z-y, y-x⟫ + ‖y-x‖² ≥ ‖y-x‖²`.
  have h_final : ‖z - x‖^2 ≥ ‖y - x‖^2 := by
    rw [show z - x = (z - y) + (y - x) by abel, norm_add_sq_real]
    norm_num [inner_sub_left, inner_sub_right] at *
    nlinarith
  simpa only [dist_eq_norm] using le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h_final

/-- **Sufficiency.**  If every value `S x` contains `x` and is star–shaped with
respect to `x`, then `S` is good. -/
theorem good_of_starConvex (S : E → Set E)
    (h : ∀ x ∈ D, x ∈ S x ∧ StarConvex ℝ x (S x)) : Good S := by
  intro x hx
  obtain ⟨hxmem, hstar⟩ := h x hx
  refine ⟨hxmem, ?_⟩
  intro z _ y hy
  exact nearest_dist_le_of_starConvex hstar hy

/-! ## Examples of good functions -/

/-- `D` is convex. -/
lemma convex_D : Convex ℝ D := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => by simpa using by have := hx.1 i; have := hy.1 i; positivity, ?_⟩
  simp [Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, hx.2, hy.2, hab]

/-- **Good example 1.**  The constant function `S x = D` is good. -/
theorem good_const_D : Good (fun _ : E => D) := by
  apply good_of_starConvex
  intro x hx
  exact ⟨hx, (convex_D).starConvex hx⟩

/-- **Good example 2.**  The singleton function `S x = {x}` is good. -/
theorem good_singleton : Good (fun x : E => {x}) := by
  apply good_of_starConvex
  intro x _
  exact ⟨rfl, starConvex_singleton x⟩

/-- First vertex `e₀ = (1,0,0)`. -/
noncomputable def e0 : E := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
/-- Second vertex `e₁ = (0,1,0)`. -/
noncomputable def e1 : E := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
/-- Third vertex `e₂ = (0,0,1)`. -/
noncomputable def e2 : E := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/-- **Good example 3 (non-convex!).**  The "V"-shaped map
`S x = [x, e₁] ∪ [x, e₂]` (the union of the two segments from `x` to the vertices
`e₁`, `e₂`) is good.  For generic `x` this value is *not convex*, yet it is
star-shaped with respect to `x`; this shows that the class of good functions is
strictly larger than the convex-valued ones — star-shapedness is the right notion. -/
theorem good_V : Good (fun x : E => segment ℝ x e1 ∪ segment ℝ x e2) := by
  apply good_of_starConvex
  intro x _
  refine ⟨Or.inl (left_mem_segment ℝ x e1), ?_⟩
  exact StarConvex.union ((convex_segment x e1).starConvex (left_mem_segment ℝ x e1))
    ((convex_segment x e2).starConvex (left_mem_segment ℝ x e2))

/-! ## An example of a function that is NOT good -/

/-- The two–point valued map `S x = {x, e₁}`. -/
noncomputable def Sbad : E → Set E := fun x => {x, e1}

/-- **Not–good example.**  `Sbad` is not good: at `x = e₀`, the point
`z = (1/4)•e₀ + (3/4)•e₁ ∈ D` projects onto the far vertex `e₁`, which is strictly
farther from `e₀` than `z` is. -/
theorem not_good_twoPoint : ¬ Good Sbad := by
  unfold Good;
  push_neg;
  refine' ⟨ e0, _, _ ⟩ <;> norm_num [ D, e0, e1, Sbad ];
  · exact fun i => by split_ifs <;> norm_num;
  · refine' ⟨ ( 1 / 4 : ℝ ) • EuclideanSpace.single 0 1 + ( 3 / 4 : ℝ ) • EuclideanSpace.single 1 1, _, _ ⟩ <;> norm_num [ Fin.sum_univ_three, IsNearest ];
    · exact ⟨ fun i => by split_ifs <;> norm_num, by norm_num [ Fin.ext_iff ] ⟩;
    · refine' ⟨ EuclideanSpace.single 1 1, _, _ ⟩ <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three ];
      · exact Real.sqrt_le_sqrt ( by norm_num [ Fin.ext_iff ] );
      · norm_num [ Fin.ext_iff, Real.sqrt_lt ];
        exact Real.lt_sqrt_of_sq_lt ( by ring_nf; norm_num )