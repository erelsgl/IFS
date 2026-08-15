import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000

/-!
# Good multifunctions on the standard 2-simplex for the `ℓ¹` metric

This file treats the same problem as `RequestProject/Main.lean` (good set-valued maps `S`
on the standard 2-simplex `D` in `ℝ³`), but with **distance and "nearest point" measured
in the `ℓ¹` (taxicab) metric** instead of the Euclidean one.

The `ℓ¹` distance between `a b : Fin 3 → ℝ` is `d1 a b = ∑ i, |a i - b i|`.

## Main result

`good1_of_starConvex`: if every value `S x` lies in `D`, contains `x`, and is star-shaped
with respect to `x`, then `S` is good for the `ℓ¹` metric.  Hence (together with the
necessity argument, identical in spirit to the Euclidean case) the **characterization for
`ℓ¹` is the same as for the Euclidean metric: `S` is good iff each `S x` is star-shaped
about `x`.**

This is in sharp contrast with the general `ℓᵖ` metric for `p > 1, p ≠ 2`, where
star-shapedness is *not* sufficient (see `RequestProject/Lp.lean`).

The decisive ingredient is the "segment lemma" `l1_segment_key`: on the affine plane of the
simplex (where coordinate differences sum to zero), the `ℓ¹`-nearest point of `z` on a
segment emanating from `x` is never farther from `x` than `z` is.
-/

/-- The `ℓ¹` distance on `Fin 3 → ℝ`. -/
def d1 (a b : Fin 3 → ℝ) : ℝ := ∑ i, |a i - b i|

/-- The standard two–dimensional simplex in `ℝ³` (coordinates ≥ 0, summing to 1). -/
def D1 : Set (Fin 3 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- `y` is an `ℓ¹`-nearest point of `z` on the set `A`. -/
def IsNearest1 (A : Set (Fin 3 → ℝ)) (z y : Fin 3 → ℝ) : Prop :=
  y ∈ A ∧ ∀ b ∈ A, d1 z y ≤ d1 z b

/-- A set-valued map `S` is **good** for the `ℓ¹` metric. -/
def Good1 (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ)) : Prop :=
  ∀ x ∈ D1, (x ∈ S x) ∧ ∀ z ∈ D1, ∀ y, IsNearest1 (S x) z y → d1 y x ≤ d1 z x

/-! ## The key segment lemma (mean-zero `ℓ¹` geometry) -/

/-
**Abstract `ℓ¹` segment inequality.**

If `u, c : Fin 3 → ℝ` both have zero coordinate sum, and `t = 1` minimises
`t ↦ ∑ i, |c i - t • u i|` over `[0,1]`, then `∑ i, |u i| ≤ ∑ i, |c i|`.

(Here `u = y - x` and `c = z - x`; the hypotheses encode that `x, y, z` lie in the affine
plane of the simplex and that `y` is the `ℓ¹`-nearest point of `z` on the segment `[x, y]`.)
-/
lemma l1_segment_key (u c : Fin 3 → ℝ)
    (hu : ∑ i, u i = 0) (hc : ∑ i, c i = 0)
    (hmin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∑ i, |c i - u i| ≤ ∑ i, |c i - t * u i|) :
    ∑ i, |u i| ≤ ∑ i, |c i| := by
  -- By definition of $w$, we know that $\sum_{i} w_i = 0$.
  set w : Fin 3 → ℝ := fun i => c i - u i
  have hw : ∑ i, w i = 0 := by
    aesop;
  -- By definition of $w$, we know that $\sum_{i} |u_i| \leq \sum_{i} |c_i|$ if and only if $0 \leq \sum_{i} u_i \cdot \sigma_i$, where $\sigma_i = \text{sign}(w_i)$ if $w_i \neq 0$ and $\sigma_i = \text{sign}(u_i)$ if $w_i = 0$.
  have h_sigma : 0 ≤ ∑ i, u i * (if w i = 0 then Real.sign (u i) else Real.sign (w i)) := by
    -- By definition of $w$, we know that $\sum_{i} |w_i + r u_i| \geq \sum_{i} |w_i|$ for all $r \in [0, 1]$.
    have h_ineq : ∀ r ∈ Set.Icc (0 : ℝ) 1, ∑ i, |w i + r * u i| ≥ ∑ i, |w i| := by
      intro r hr; specialize hmin ( 1 - r ) ( by linarith [ hr.1, hr.2 ] ) ( by linarith [ hr.1, hr.2 ] ) ; simp_all +decide [ sub_mul ] ;
      convert hmin using 3 ; ring;
    -- Choose $r$ small enough such that $r * |u_i| < |w_i|$ for all $i$ where $w_i \neq 0$.
    obtain ⟨r, hr₀, hr₁⟩ : ∃ r ∈ Set.Ioo (0 : ℝ) 1, ∀ i, w i ≠ 0 → r * |u i| < |w i| := by
      by_cases h_nonzero : ∃ i, w i ≠ 0 ∧ u i ≠ 0;
      · obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 ∧ u i ≠ 0 := h_nonzero
        have h_min : ∃ m > 0, ∀ i, w i ≠ 0 → u i ≠ 0 → m ≤ |w i| / |u i| := by
          have h_min : ∃ m ∈ Finset.image (fun i => |w i| / |u i|) (Finset.univ.filter (fun i => w i ≠ 0 ∧ u i ≠ 0)), ∀ j ∈ Finset.image (fun i => |w i| / |u i|) (Finset.univ.filter (fun i => w i ≠ 0 ∧ u i ≠ 0)), m ≤ j := by
            exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ i, hi ⟩ ) ⟩, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj ⟩;
          simp +zetaDelta at *;
          exact ⟨ |c h_min.choose - u h_min.choose| / |u h_min.choose|, div_pos ( abs_pos.mpr h_min.choose_spec.1.1 ) ( abs_pos.mpr h_min.choose_spec.1.2 ), fun i hi₁ hi₂ => h_min.choose_spec.2 _ _ hi₁ hi₂ rfl ⟩;
        obtain ⟨ m, hm₀, hm ⟩ := h_min;
        use Min.min ( m / 2 ) ( 1 / 2 );
        norm_num +zetaDelta at *;
        exact ⟨ hm₀, fun i hi => if hi' : u i = 0 then by aesop else by have := hm i hi hi'; rw [ le_div_iff₀ ( abs_pos.mpr hi' ) ] at this; cases min_cases ( m / 2 ) ( 1 / 2 ) <;> nlinarith [ abs_pos.mpr hi', abs_nonneg ( c i - u i ) ] ⟩;
      · exact ⟨ 1 / 2, ⟨ by norm_num, by norm_num ⟩, fun i hi => by specialize h_nonzero; contrapose! h_nonzero; use i; aesop ⟩;
    -- For each $i$, we have $|w_i + r u_i| - |w_i| = r u_i \cdot \text{sign}(w_i)$ if $w_i \neq 0$ and $|w_i + r u_i| - |w_i| = r |u_i|$ if $w_i = 0$.
    have h_diff : ∀ i, |w i + r * u i| - |w i| = r * u i * (if w i = 0 then Real.sign (u i) else Real.sign (w i)) := by
      intro i; split_ifs <;> simp_all +decide [ Real.sign ] ;
      · split_ifs <;> cases abs_cases ( u i ) <;> cases abs_cases r <;> nlinarith;
      · split_ifs <;> cases abs_cases ( w i + r * u i ) <;> cases abs_cases ( w i ) <;> nlinarith [ hr₁ i ‹_›, abs_le.mp ( show |r * u i| ≤ |w i| by exact le_of_lt ( by simpa [ abs_mul, abs_of_pos hr₀.1 ] using hr₁ i ‹_› ) ) ];
    have := h_ineq r ⟨ hr₀.1.le, hr₀.2.le ⟩ ; simp_all +decide [ mul_assoc ] ;
    simp_all +decide [ sub_eq_iff_eq_add ];
    simp_all +decide [ Finset.sum_add_distrib ];
    rw [ show ( ∑ i : Fin 3, if w i = 0 then r * ( u i * ( u i |> Real.sign ) ) else r * ( u i * ( w i |> Real.sign ) ) ) = r * ( ∑ i : Fin 3, if w i = 0 then u i * ( u i |> Real.sign ) else u i * ( w i |> Real.sign ) ) by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring ] at this ; nlinarith;
  simp_all +decide [ Fin.sum_univ_three ];
  split_ifs at h_sigma <;> simp_all +decide [ Real.sign ];
  · grind;
  · grind;
  · grind +splitImp;
  · grind;
  · grind

/-- **Core variational lemma (ℓ¹).**  If `A ⊆ D`, `A` is star-shaped about `x ∈ D`, and `y`
is an `ℓ¹`-nearest point of `z ∈ D` on `A`, then `d1 y x ≤ d1 z x`. -/
lemma nearest1_dist_le_of_starConvex {A : Set (Fin 3 → ℝ)} {x z y : Fin 3 → ℝ}
    (hx : x ∈ D1) (hz : z ∈ D1) (hAD : A ⊆ D1)
    (hstar : StarConvex ℝ x A) (hy : IsNearest1 A z y) :
    d1 y x ≤ d1 z x := by
  obtain ⟨hyA, hymin⟩ := hy
  have hyD : y ∈ D1 := hAD hyA
  -- coordinate-sum-zero of the differences
  have hu : ∑ i, (y i - x i) = 0 := by
    rw [Finset.sum_sub_distrib, hyD.2, hx.2]; ring
  have hc : ∑ i, (z i - x i) = 0 := by
    rw [Finset.sum_sub_distrib, hz.2, hx.2]; ring
  -- segment from x to y lies in A, so y minimises ℓ¹ distance to z over it
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∑ i, |(z i - x i) - (y i - x i)| ≤ ∑ i, |(z i - x i) - t * (y i - x i)| := by
    intro t ht0 ht1
    have hmem : (1 - t) • x + t • y ∈ A := by
      have := hstar hyA (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
      simpa using this
    have h := hymin _ hmem
    -- rewrite both ℓ¹ distances coordinatewise
    have e1 : d1 z y = ∑ i, |(z i - x i) - (y i - x i)| := by
      unfold d1; apply Finset.sum_congr rfl; intro i _; congr 1; ring
    have e2 : d1 z ((1 - t) • x + t • y) = ∑ i, |(z i - x i) - t * (y i - x i)| := by
      unfold d1; apply Finset.sum_congr rfl; intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      congr 1; ring
    rw [e1, e2] at h; exact h
  have key := l1_segment_key (fun i => y i - x i) (fun i => z i - x i) hu hc (by
    intro t ht0 ht1; simpa using hseg t ht0 ht1)
  -- translate back to d1
  have ey : d1 y x = ∑ i, |y i - x i| := rfl
  have ez : d1 z x = ∑ i, |z i - x i| := rfl
  rw [ey, ez]; simpa using key

/-- **Sufficiency / characterization (ℓ¹).**  If every value `S x` lies in `D`, contains
`x`, and is star-shaped about `x`, then `S` is good for the `ℓ¹` metric. -/
theorem good1_of_starConvex (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ))
    (h : ∀ x ∈ D1, x ∈ S x ∧ StarConvex ℝ x (S x) ∧ S x ⊆ D1) : Good1 S := by
  intro x hx
  obtain ⟨hxmem, hstar, hsub⟩ := h x hx
  refine ⟨hxmem, ?_⟩
  intro z hz y hy
  exact nearest1_dist_le_of_starConvex hx hz hsub hstar hy

/-! ## Examples (ℓ¹) -/

/-- `D` is convex. -/
lemma convex_D1 : Convex ℝ D1 := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 i; have := hy.1 i; positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    simpa using hab

/-- First vertex `e₀ = (1,0,0)`. -/
def v0 : Fin 3 → ℝ := ![1, 0, 0]
/-- Second vertex `e₁ = (0,1,0)`. -/
def v1 : Fin 3 → ℝ := ![0, 1, 0]
/-- Third vertex `e₂ = (0,0,1)`. -/
def v2 : Fin 3 → ℝ := ![0, 0, 1]

lemma v0_mem : v0 ∈ D1 := by
  refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [v0, Fin.sum_univ_three]
lemma v1_mem : v1 ∈ D1 := by
  refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [v1, Fin.sum_univ_three]
lemma v2_mem : v2 ∈ D1 := by
  refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [v2, Fin.sum_univ_three]

/-- **Good example 1 (ℓ¹).**  The constant map `S x = D` is good. -/
theorem good1_const_D : Good1 (fun _ => D1) := by
  apply good1_of_starConvex
  intro x hx
  exact ⟨hx, (convex_D1).starConvex hx, le_refl _⟩

/-- **Good example 2 (ℓ¹).**  The singleton map `S x = {x}` is good. -/
theorem good1_singleton : Good1 (fun x => {x}) := by
  apply good1_of_starConvex
  intro x hx
  exact ⟨rfl, starConvex_singleton x, by simpa using hx⟩

/-- **Good example 3 (ℓ¹, non-convex).**  The "V" map `S x = [x,e₁] ∪ [x,e₂]` is good. -/
theorem good1_V : Good1 (fun x => segment ℝ x v1 ∪ segment ℝ x v2) := by
  apply good1_of_starConvex
  intro x hx
  refine ⟨Or.inl (left_mem_segment ℝ x v1), ?_, ?_⟩
  · exact StarConvex.union ((convex_segment x v1).starConvex (left_mem_segment ℝ x v1))
      ((convex_segment x v2).starConvex (left_mem_segment ℝ x v2))
  · rintro p (hp | hp)
    · exact convex_D1.segment_subset hx v1_mem hp
    · exact convex_D1.segment_subset hx v2_mem hp

/-- The two-point valued map `S x = {x, e₁}`. -/
def S1bad : (Fin 3 → ℝ) → Set (Fin 3 → ℝ) := fun x => {x, v1}

/-- **Not-good example (ℓ¹).**  `S1bad` is not good: at `x = e₀`, the point
`z = (1/4)·e₀ + (3/4)·e₁ ∈ D` has `ℓ¹`-nearest point the far vertex `e₁`, which is strictly
farther from `e₀` than `z` is. -/
theorem not_good1_twoPoint : ¬ Good1 S1bad := by
  intro h
  have hx : v0 ∈ D1 := v0_mem
  obtain ⟨_, h2⟩ := h v0 hx
  set z : Fin 3 → ℝ := ![1/4, 3/4, 0] with hzdef
  have hzD : z ∈ D1 := by
    refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [hzdef, Fin.sum_univ_three] <;> norm_num
  have hnear : IsNearest1 (S1bad v0) z v1 := by
    refine ⟨Or.inr rfl, ?_⟩
    intro b hb
    rcases hb with hb | hb <;> subst hb
    · simp [d1, Fin.sum_univ_three, v0, v1, hzdef]; norm_num
    · simp [d1, Fin.sum_univ_three, v1, hzdef]
  have := h2 z hzD v1 hnear
  simp [d1, Fin.sum_univ_three, v0, v1, hzdef] at this
  norm_num at this