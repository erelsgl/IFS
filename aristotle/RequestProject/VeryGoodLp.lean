import Mathlib
import RequestProject.Lp

open scoped BigOperators

set_option maxHeartbeats 4000000

/-!
# "Very good" multifunctions on the standard 2-simplex — the `ℓᵖ` case (`p > 1`)

This file is the `ℓᵖ` analogue of `RequestProject/VeryGood.lean`, formalized for the
representative strictly-convex exponent `p = 6` (whose distance is a polynomial, so the
witnesses are exact rational arithmetic).  Distance and "nearest point" are measured in the
`ℓ⁶` metric `dist6` with 6-th power `Q6` (see `RequestProject/Lp.lean`).  A map `S` is
**very good** when for every `x ∈ D`: `[1] x ∈ S x` and `[2']` for every `z ∈ D`, every
`ℓ⁶`-nearest point `y` of `z` on `S x` lies on the closed line segment `[z, x]`.

Since `y ∈ [z, x]` implies `dist6 y x ≤ dist6 z x` (`dist6_le_of_mem_segment`),
**very good ⟹ good** (`veryGood6_imp_good6`).

## The characterization for `ℓᵖ`, `p > 1` — *same as `ℓ²`*, and the contrast with `ℓ¹`

The central — and perhaps surprising — fact is that for every strictly convex `ℓᵖ`
(`p > 1`, including `p = 2`) the metric projection of a point `z` onto an `ℓᵖ`-**ball
centred at `x`** is **radial**: it lands on the ray from `x` through `z`.  (The KKT/first
order optimality condition holds because both gradients `∇ Q6(z,·)` and `∇ Q6(·,x)` at the
radial point are parallel to the componentwise 5th power of `z - x`.)  Consequently:

>  For `ℓᵖ` with `p > 1`, `S` is very good  ⟺  for every `x ∈ D` there is `R ≥ 0` with
>  `S x = {a ∈ D | dist_p(a, x) ≤ R}` — exactly the same "spherical-cap" characterization
>  as in the Euclidean case `RequestProject/VeryGood.lean`.

The decisive sufficiency direction is `veryGood6_cap`: every `ℓ⁶`-cap-valued map is very
good.  Uniqueness of the nearest point (needed so that *every* nearest point is the radial
one) comes from **strict convexity** of `Q6(z, ·)` (`Q6_unique_min`), which holds for
`p > 1`.

**Contrast with `ℓ¹`.**  For `p = 1` the norm is *not* strictly convex, so the projection
onto an `ℓ¹`-ball, while it *has* the radial point as *a* nearest point, also has *other*
nearest points off the segment — hence `ℓ¹`-caps are generally **not** very good
(`RequestProject/VeryGoodL1.lean`).

**Contrast with "good".**  Unlike the Euclidean case — where convex / star-shaped values
such as a segment `[x,a]` or the "V" are *good but not very good* — for `ℓ⁶` such values are
typically **not even good** (e.g. `not_good6_segment` in `RequestProject/Lp.lean`; the "V"
and "half-cap" likewise fail).  So for `p ≠ 2` the *good* and *very good* classes are far
closer together, and the rich supply of good-but-not-very-good examples available for `ℓ²`
disappears.
-/

namespace VeryGoodL6

/-- A set-valued map `S` is **very good** for the `ℓ⁶` metric. -/
def VeryGood6 (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ)) : Prop :=
  ∀ x ∈ D1, (x ∈ S x) ∧ ∀ z ∈ D1, ∀ y, IsNearest6 (S x) z y → y ∈ segment ℝ z x

/-! ## Very good implies good -/

/-
A point of the segment `[z, x]` is no farther from `x` than `z` is, in `ℓ⁶`.
-/
lemma dist6_le_of_mem_segment {x z y : Fin 3 → ℝ} (hy : y ∈ segment ℝ z x) :
    dist6 y x ≤ dist6 z x := by
  rw [ dist6_le_iff ];
  obtain ⟨a, b, ha, hb, hab, rfl⟩ : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ y = a • z + b • x := by
    rcases hy with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ a, b, ha, hb, hab, rfl ⟩ ;
  refine' Finset.sum_le_sum fun i _ => _;
  rw [ show ( a • z + b • x ) i - x i = a * ( z i - x i ) by simpa using by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring ] ; rw [ mul_pow ] ; exact mul_le_of_le_one_left ( by positivity ) ( pow_le_one₀ ( by positivity ) ( by linarith ) ) ;

/-- **Very good ⟹ good** for `ℓ⁶`. -/
theorem veryGood6_imp_good6 (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ)) (h : VeryGood6 S) :
    Good6 S := by
  intro x hx
  obtain ⟨hxmem, h2⟩ := h x hx
  exact ⟨hxmem, fun z hz y hy => dist6_le_of_mem_segment (h2 z hz y hy)⟩

/-! ## Very good examples -/

/-- **Very good example (ℓ⁶).**  The constant map `S x = D` is very good. -/
theorem veryGood6_const_D : VeryGood6 (fun _ => D1) := by
  intro x hx
  refine ⟨hx, ?_⟩
  intro z hz y hy
  obtain ⟨hyD, hymin⟩ := hy
  have h0 : dist6 z y ≤ dist6 z z := hymin z hz
  rw [dist6_le_iff] at h0
  have hzz : Q6 z z = 0 := by simp [Q6]
  rw [hzz] at h0
  have hQ : Q6 z y = 0 := le_antisymm h0 (Q6_nonneg z y)
  have hyz : y = z := by
    have hterm : ∀ i ∈ Finset.univ, (z i - y i) ^ 6 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 (by simpa [Q6] using hQ)
    funext i
    have := hterm i (Finset.mem_univ i)
    have : z i - y i = 0 := by
      have h6 := pow_eq_zero_iff (n := 6) (by norm_num) |>.1 this
      simpa using h6
    linarith
  rw [hyz]
  exact left_mem_segment ℝ z x

/-- **Very good example (ℓ⁶).**  The singleton map `S x = {x}` is very good. -/
theorem veryGood6_singleton : VeryGood6 (fun x => {x}) := by
  intro x hx
  refine ⟨rfl, ?_⟩
  intro z hz y hy
  obtain ⟨hymem, _⟩ := hy
  rw [Set.mem_singleton_iff] at hymem
  rw [hymem]
  exact right_mem_segment ℝ z x

/-! ## The spherical `ℓ⁶`-cap and its very-goodness -/

/-- The `ℓ⁶`-cap, described by the 6-th power radius `R6`: `{a ∈ D | Q6 a x ≤ R6}`. -/
def cap6 (x : Fin 3 → ℝ) (R6 : ℝ) : Set (Fin 3 → ℝ) := {a | a ∈ D1 ∧ Q6 a x ≤ R6}

/-
`Q6 (·, x)` is convex on the whole space.
-/
lemma convexOn_Q6 (x : Fin 3 → ℝ) : ConvexOn ℝ Set.univ (fun w => Q6 w x) := by
  constructor <;> norm_num;
  · exact convex_univ;
  · intro w v a b ha hb hab
    have h_convex : ∀ i, (a * w i + b * v i - x i)^6 ≤ a * (w i - x i)^6 + b * (v i - x i)^6 := by
      intro i
      have h_convex : ConvexOn ℝ Set.univ (fun t : ℝ => (t - x i)^6) := by
        apply_rules [ convexOn_of_deriv2_nonneg, convex_univ ];
        · exact Continuous.continuousOn ( by continuity );
        · exact Differentiable.differentiableOn ( by norm_num );
        · exact Differentiable.differentiableOn ( by rw [ show deriv ( fun t : ℝ => ( t - x i ) ^ 6 ) = fun t : ℝ => 6 * ( t - x i ) ^ 5 by funext; norm_num [ mul_comm ] ] ; norm_num );
        · unfold deriv ; norm_num [ fderiv_apply_one_eq_deriv ] ; intros ; positivity;
      generalize_proofs at *; (
      exact h_convex.2 trivial trivial ha hb hab);
    simpa only [ Q6, Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using Finset.sum_le_sum fun i _ => h_convex i

/-
The `ℓ⁶`-cap is convex.
-/
lemma convex_cap6 (x : Fin 3 → ℝ) (R6 : ℝ) : Convex ℝ (cap6 x R6) := by
  have h_sublevel : Convex ℝ {a | Q6 a x ≤ R6} := by
    convert ConvexOn.convex_le ( convexOn_Q6 x ) R6 using 1;
    aesop;
  exact convex_D1.inter h_sublevel

/-
First-order (tangent line) convexity of `t ↦ t^6`.
-/
lemma pow6_tangent (u v : ℝ) : v ^ 6 + 6 * v ^ 5 * (u - v) ≤ u ^ 6 := by
  nlinarith [ sq_nonneg ( u ^ 2 - v ^ 2 ), sq_nonneg ( ( u - v ) ^ 2 ), sq_nonneg ( ( u + v ) ^ 2 ), sq_nonneg ( u * ( u - v ) ), sq_nonneg ( v * ( u - v ) ), sq_nonneg ( ( u - v ) * ( u + v ) ), mul_nonneg ( sq_nonneg ( u - v ) ) ( sq_nonneg ( u + v ) ) ]

/-
Strict midpoint convexity of `t ↦ t^6`.
-/
lemma pow6_strict_mid {u v : ℝ} (h : u ≠ v) : ((u + v) / 2) ^ 6 < (u ^ 6 + v ^ 6) / 2 := by
  by_contra h_contra;
  exact h ( by nlinarith [ mul_self_pos.2 ( sub_ne_zero.2 h ), sq_nonneg ( u^2 - v^2 ), sq_nonneg ( ( u - v ) ^2 ), sq_nonneg ( ( u + v ) ^2 ), pow_pos ( mul_self_pos.2 ( sub_ne_zero.2 h ) ) 2, pow_pos ( mul_self_pos.2 ( sub_ne_zero.2 h ) ) 3 ] )

/-
`Q6 (z, ·)` has at most one minimiser on a convex set: if `y₁, y₂` both minimise the
`ℓ⁶`-distance to `z` over a convex set, they are equal.  (Strict convexity, `p > 1`.)
-/
lemma Q6_unique_min {A : Set (Fin 3 → ℝ)} (hA : Convex ℝ A) {z y₁ y₂ : Fin 3 → ℝ}
    (h1 : IsNearest6 A z y₁) (h2 : IsNearest6 A z y₂) : y₁ = y₂ := by
  by_contra h_neq;
  have h_midpoint : Q6 z ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) < (Q6 z y₁ + Q6 z y₂) / 2 := by
    -- Since $y₁ \neq y₂$, there exists some $i$ such that $y₁ i \neq y₂ i$.
    obtain ⟨i, hi⟩ : ∃ i, y₁ i ≠ y₂ i := by
      exact Function.ne_iff.mp h_neq;
    have h_midpoint : ∀ i, ((z i - (1 / 2 : ℝ) * (y₁ i + y₂ i)) ^ 6) ≤ ((z i - y₁ i) ^ 6 + (z i - y₂ i) ^ 6) / 2 := by
      intro i
      have h_midpoint_i : ((z i - y₁ i) + (z i - y₂ i)) ^ 6 ≤ 32 * ((z i - y₁ i) ^ 6 + (z i - y₂ i) ^ 6) := by
        nlinarith only [ sq_nonneg ( ( z i - y₁ i ) ^ 2 - ( z i - y₂ i ) ^ 2 ), sq_nonneg ( ( z i - y₁ i ) * ( z i - y₂ i ) ), sq_nonneg ( ( z i - y₁ i ) ^ 2 + ( z i - y₂ i ) ^ 2 ), sq_nonneg ( ( z i - y₁ i ) - ( z i - y₂ i ) ), sq_nonneg ( ( z i - y₁ i ) + ( z i - y₂ i ) ) ];
      linarith;
    have h_midpoint_strict : ((z i - (1 / 2 : ℝ) * (y₁ i + y₂ i)) ^ 6) < ((z i - y₁ i) ^ 6 + (z i - y₂ i) ^ 6) / 2 := by
      convert pow6_strict_mid ( show z i - y₁ i ≠ z i - y₂ i from by simpa using hi ) using 1 ; ring;
    convert Finset.sum_lt_sum ( fun i _ => h_midpoint i ) ⟨ i, Finset.mem_univ i, h_midpoint_strict ⟩ using 1 ; norm_num [ Fin.sum_univ_three ] ; ring;
    · unfold Q6; norm_num [ Fin.sum_univ_three ] ; ring;
    · norm_num [ Fin.sum_univ_three, Q6 ] ; ring;
  have h_midpoint_in_A : (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ ∈ A := by
    exact hA h1.1 h2.1 ( by norm_num ) ( by norm_num ) ( by norm_num );
  have := h1.2 _ h_midpoint_in_A; have := h2.2 _ h_midpoint_in_A; ( erw [ dist6_le_iff ] at *; norm_num at * ; linarith; )

/-
The radial point `x + s•(z-x)` is `ℓ⁶`-nearest to `z` among all points of the `ℓ⁶`-ball
of 6-th power radius `Q6 (x+s•(z-x)) x` centred at `x` (`s ∈ [0,1]`).  This is the radial
projection lemma — the crux special to `p > 1`.
-/
lemma radial6_nearest_ball (z x : Fin 3 → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (b : Fin 3 → ℝ) (hb : Q6 b x ≤ Q6 (x + s • (z - x)) x) :
    Q6 z (x + s • (z - x)) ≤ Q6 z b := by
  by_cases hs : s = 0;
  · simp_all +decide [ Q6 ];
    -- Since $\sum i, (b i - x i) ^ 6 \leq 0$, we have $b i = x i$ for all $i$.
    have h_eq : ∀ i, b i = x i := by
      exact fun i => eq_of_sub_eq_zero ( by contrapose! hb; exact lt_of_lt_of_le ( by positivity ) ( Finset.single_le_sum ( fun i _ => by positivity ) ( Finset.mem_univ i ) ) );
    aesop;
  · have hP_nonpos : ∑ i, 6 * (z i - x i) ^ 5 * (b i - (x i + s * (z i - x i))) ≤ 0 := by
      unfold Q6 at *;
      norm_num [ Fin.sum_univ_three ] at *;
      nlinarith [ pow_pos ( lt_of_le_of_ne hs0 ( Ne.symm hs ) ) 5, pow_pos ( lt_of_le_of_ne hs0 ( Ne.symm hs ) ) 6, pow6_tangent ( b 0 - x 0 ) ( s * ( z 0 - x 0 ) ), pow6_tangent ( b 1 - x 1 ) ( s * ( z 1 - x 1 ) ), pow6_tangent ( b 2 - x 2 ) ( s * ( z 2 - x 2 ) ) ];
    have hS1_nonneg : ∑ i, 6 * (x i + s * (z i - x i) - z i) ^ 5 * (b i - (x i + s * (z i - x i))) ≥ 0 := by
      have hS1_nonneg : ∑ i, 6 * (x i + s * (z i - x i) - z i) ^ 5 * (b i - (x i + s * (z i - x i))) = (s - 1) ^ 5 * ∑ i, 6 * (z i - x i) ^ 5 * (b i - (x i + s * (z i - x i))) := by
        rw [ Finset.mul_sum _ _ _ ] ; congr ; ext i ; ring;
      exact hS1_nonneg.symm ▸ mul_nonneg_of_nonpos_of_nonpos ( by nlinarith [ pow_nonneg ( sub_nonneg.mpr hs1 ) 5 ] ) hP_nonpos;
    have hS1_nonneg : ∑ i, (b i - z i) ^ 6 ≥ ∑ i, (x i + s * (z i - x i) - z i) ^ 6 + ∑ i, 6 * (x i + s * (z i - x i) - z i) ^ 5 * (b i - (x i + s * (z i - x i))) := by
      rw [ ← Finset.sum_add_distrib ];
      exact Finset.sum_le_sum fun i _ => by linarith [ pow6_tangent ( b i - z i ) ( x i + s * ( z i - x i ) - z i ) ] ;
    unfold Q6; simp_all +decide [ Fin.sum_univ_three ] ;
    linarith

/-- Scaling: `Q6 (x + s•(z-x)) x = s^6 * Q6 z x`. -/
lemma Q6_self_scale (z x : Fin 3 → ℝ) (s : ℝ) :
    Q6 (x + s • (z - x)) x = s ^ 6 * Q6 z x := by
  simp only [Q6, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-
The radial point lies on the segment `[z, x]` (for `s ∈ [0,1]`).
-/
lemma radial6_mem_segment (z x : Fin 3 → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x + s • (z - x) ∈ segment ℝ z x := by
  rw [ segment_eq_image ];
  exact ⟨ 1 - s, ⟨ by linarith, by linarith ⟩, by ext i; simpa using by ring ⟩

/-
**Sufficiency / characterization (ℓ⁶).**  Every `ℓ⁶`-cap-valued map
`S x = {a ∈ D | Q6 a x ≤ R6 x}` (with `R6 x ≥ 0`) is very good.
-/
theorem veryGood6_cap (R6 : (Fin 3 → ℝ) → ℝ) (hR : ∀ x, 0 ≤ R6 x) :
    VeryGood6 (fun x => cap6 x (R6 x)) := by
  intro x hx; refine ⟨ ?_, ?_ ⟩;
  · exact ⟨ hx, by norm_num [ Q6 ] ; linarith [ hR x ] ⟩;
  · intro z hz y hy; by_cases h : Q6 z x ≤ R6 x <;> simp_all +decide [ IsNearest6 ] ;
    · have h_eq : Q6 z y ≤ 0 := by
        have := hy.2 z ?_ <;> simp_all +decide [ dist6_le_iff ];
        · exact this.trans ( by unfold Q6; norm_num );
        · exact ⟨ hz, h ⟩;
      have h_eq : y = z := by
        have h_eq : ∀ i, (z i - y i) ^ 6 = 0 := by
          exact fun i => le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => show 0 ≤ ( z i - y i ) ^ 6 by positivity ) ( Finset.mem_univ i ) ) h_eq ) ( by positivity );
        grind +extAll;
      exact h_eq.symm ▸ left_mem_segment _ _ _;
    · set s := (R6 x / Q6 z x) ^ ((1 : ℝ) / 6)
      have hs0 : 0 ≤ s := by
        exact Real.rpow_nonneg ( div_nonneg ( hR x ) ( Q6_nonneg _ _ ) ) _
      have hs1 : s ≤ 1 := by
        exact Real.rpow_le_one ( div_nonneg ( hR x ) ( by exact Finset.sum_nonneg fun _ _ => by positivity ) ) ( div_le_one_of_le₀ h.le ( by exact Finset.sum_nonneg fun _ _ => by positivity ) ) ( by positivity )
      have hm : x + s • (z - x) ∈ cap6 x (R6 x) := by
        refine' ⟨ _, _ ⟩;
        · have h_convex : Convex ℝ D1 := by
            exact convex_D1;
          convert h_convex hx hz ( show 0 ≤ 1 - s by linarith ) ( show 0 ≤ s by linarith ) ( by linarith ) using 1 ; ext i ; norm_num ; ring;
        · rw [ Q6_self_scale ];
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( div_nonneg ( hR x ) ( by linarith [ hR x ] ) ) ] ; norm_num [ show Q6 z x ≠ 0 by linarith [ hR x ] ]
      have hm_nearest : IsNearest6 (cap6 x (R6 x)) z (x + s • (z - x)) := by
        refine' ⟨ hm, fun b hb => _ ⟩;
        apply radial6_nearest_ball z x hs0 hs1 b (by
        convert hb.2 using 1;
        rw [ Q6_self_scale ];
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( div_nonneg ( hR x ) ( by linarith [ hR x ] ) ) ] ; norm_num [ show Q6 z x ≠ 0 by linarith [ hR x ] ]) |> fun h => dist6_le_iff _ _ _ _ |>.2 h
      have hy_eq_m : y = x + s • (z - x) := by
        apply Q6_unique_min (convex_cap6 x (R6 x)) hy hm_nearest
      have hy_segment : y ∈ segment ℝ z x := by
        convert radial6_mem_segment z x hs0 hs1 using 1
      exact hy_segment

/-! ## Contrasting good examples for `ℓ⁶` (recap)

For the Euclidean metric, convex / star-shaped values such as a single segment `[x, a]` or
the non-convex "V" are *good but not very good*.  For `ℓ⁶` these values are typically **not
even good**: `RequestProject/Lp.lean`'s `not_good6_segment` exhibits a star-shaped (indeed
convex) value `S x = [x, a]` that already fails the weaker *good* property.  Thus for `p ≠ 2`
the supply of good-but-not-very-good examples available for `ℓ²` collapses, and the very good
values are precisely the `ℓᵖ`-caps (`veryGood6_cap`), with `{x}` and `D` the extreme cases. -/

end VeryGoodL6