import Mathlib
import RequestProject.L1

open scoped BigOperators

set_option maxHeartbeats 4000000

/-!
# Good multifunctions on the standard 2-simplex for the `ℓᵖ` metric (`p > 1`)

This file analyses the "good multifunction" problem (see `RequestProject/Main.lean`) when
distance and "nearest point" are measured in the `ℓᵖ` metric with `p > 1`.

The headline phenomenon, **in sharp contrast with the Euclidean (`p = 2`) and the `ℓ¹`
cases** (where `good ⟺ star-shaped`, see `Main.lean` and `L1.lean`):

> For `ℓᵖ` with `p > 1, p ≠ 2`, star-shapedness of the values `S x` is **no longer
> sufficient** for `S` to be good.  Even a *convex* value — a single segment `[x, a]` —
> can violate property `[2]`.

We make this precise and machine-checked for the representative exponent `p = 6` (any
`p ∉ {1, 2}` exhibits the same failure; `p = 6` is chosen because the `ℓ⁶`-distance is a
polynomial, so the witness can be verified by exact rational arithmetic).

Concretely, `not_good6_segment` shows that the *reflexive, star-shaped-valued* map
`S x = [x, a]` (segment from `x` to a fixed vertex-free point `a ∈ D`) is **not** good for
the `ℓ⁶` metric: at a specific `x ∈ D`, a point `z ∈ D` closer to `x` than `a` is, has its
`ℓ⁶`-nearest point on `[x,a]` strictly farther from `x` than `z` is.

## The characterization for `p > 1`

The correct characterization (valid for any metric) is the *projection / ball* condition:

>  `S` is good  ⟺  for every `x ∈ D` and every `z ∈ D`, every nearest point of `z` on
>  `S x` lies in the closed `ℓᵖ`-ball `B̄_p(x, dist_p(z,x))`.

For `p = 2` this is equivalent to star-shapedness; for `p = 1` star-shapedness is again
equivalent (`L1.lean`).  For general `p > 1` it is *strictly stronger* than
star-shapedness, as the counterexample below shows.
-/

/-- The 6-th power of the `ℓ⁶` distance: `Q6 a b = ∑ i, (a i - b i)^6`. -/
def Q6 (a b : Fin 3 → ℝ) : ℝ := ∑ i, (a i - b i) ^ 6

/-- The genuine `ℓ⁶` distance `(∑ i, |a i - b i|^6)^(1/6)`.  Since `6` is even,
`|a i - b i|^6 = (a i - b i)^6`, so this equals `(Q6 a b)^(1/6)`. -/
noncomputable def dist6 (a b : Fin 3 → ℝ) : ℝ := (Q6 a b) ^ ((1 : ℝ) / 6)

/-- `y` is an `ℓ⁶`-nearest point of `z` on `A`. -/
def IsNearest6 (A : Set (Fin 3 → ℝ)) (z y : Fin 3 → ℝ) : Prop :=
  y ∈ A ∧ ∀ b ∈ A, dist6 z y ≤ dist6 z b

/-- A set-valued map `S` is **good** for the `ℓ⁶` metric. -/
def Good6 (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ)) : Prop :=
  ∀ x ∈ D1, (x ∈ S x) ∧ ∀ z ∈ D1, ∀ y, IsNearest6 (S x) z y → dist6 y x ≤ dist6 z x

lemma Q6_nonneg (a b : Fin 3 → ℝ) : 0 ≤ Q6 a b := by
  unfold Q6; apply Finset.sum_nonneg; intro i _; positivity

/-- The order bridge: comparing `ℓ⁶` distances is the same as comparing the 6-th powers. -/
lemma dist6_le_iff (a b c d : Fin 3 → ℝ) : dist6 a b ≤ dist6 c d ↔ Q6 a b ≤ Q6 c d := by
  unfold dist6
  exact Real.rpow_le_rpow_iff (Q6_nonneg a b) (Q6_nonneg c d) (by norm_num)

lemma dist6_lt_iff (a b c d : Fin 3 → ℝ) : dist6 a b < dist6 c d ↔ Q6 a b < Q6 c d := by
  rw [← not_le, ← not_le, dist6_le_iff]

/-! ## Convexity of the distance along the segment -/

/-
For fixed `b d : Fin 3 → ℝ`, the map `t ↦ ∑ i, (b i + t • d i)^6` is convex.
-/
lemma convexOn_sum6 (b d : Fin 3 → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => ∑ i, (b i + t * d i) ^ 6) := by
  have h_convex : ∀ i : Fin 3, ConvexOn ℝ Set.univ (fun t : ℝ => (b i + t * d i) ^ 6) := by
    intro i
    have h_convex : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 6) := by
      apply_rules [ Even.convexOn_pow ] ; norm_num;
    convert h_convex.comp_affineMap ( AffineMap.const ℝ ℝ ( b i ) + ( d i ) • AffineMap.id ℝ ℝ ) using 1;
    ext; simp +decide [ mul_comm ];
  exact ⟨ convex_univ, fun x hx y hy a b ha hb hab => by simpa [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_left_comm, mul_add, pow_mul, hab.symm ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_convex i |>.2 hx hy ha hb hab ⟩

/-! ## Abstract "minimiser bracket" lemma -/

/-
If `G` is convex, `s` minimises `G` on `[0,1]`, `t0 ≤ t1` are in `[0,1]`, and
`G t1 < G t0`, then `t0 < s`.
-/
lemma min_bracket {G : ℝ → ℝ} (hG : ConvexOn ℝ Set.univ G)
    {s t0 t1 : ℝ}
    (hmin : ∀ t, 0 ≤ t → t ≤ 1 → G s ≤ G t)
    (ht1 : 0 ≤ t1) (ht11 : t1 ≤ 1)
    (hle : t0 ≤ t1) (hG01 : G t1 < G t0) : t0 < s := by
  contrapose! hG01;
  by_cases h_cases : s < t1;
  · have := hG.2 ( Set.mem_univ s ) ( Set.mem_univ t1 );
    convert le_trans ( this ( show 0 ≤ ( t1 - t0 ) / ( t1 - s ) by exact div_nonneg ( by linarith ) ( by linarith ) ) ( show 0 ≤ ( t0 - s ) / ( t1 - s ) by exact div_nonneg ( by linarith ) ( by linarith ) ) ( by rw [ ← add_div, div_eq_iff ] <;> linarith ) ) _ using 1 <;> norm_num;
    · grind;
    · rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_iff₀ ] <;> nlinarith [ hmin t1 ht1 ht11 ];
  · rw [ show t0 = t1 by linarith ]

/-! ## The counterexample data -/

/-- Center point `x = (9/200, 3/8, 29/50) ∈ D`. -/
noncomputable def xc : Fin 3 → ℝ := ![9/200, 3/8, 29/50]
/-- Fixed target `a = (61/100, 17/100, 11/50) ∈ D`. -/
noncomputable def ac : Fin 3 → ℝ := ![61/100, 17/100, 11/50]
/-- Test point `z = (59/100, 19/100, 11/50) ∈ D`. -/
noncomputable def zc : Fin 3 → ℝ := ![59/100, 19/100, 11/50]

/-- The reflexive, star-shaped-valued map `S x = [x, a]`. -/
def Sseg : (Fin 3 → ℝ) → Set (Fin 3 → ℝ) := fun x => segment ℝ x ac

lemma xc_mem : xc ∈ D1 := by
  refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [xc, Fin.sum_univ_three] <;> norm_num
lemma zc_mem : zc ∈ D1 := by
  refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [zc, Fin.sum_univ_three] <;> norm_num
lemma ac_mem : ac ∈ D1 := by
  refine ⟨fun i => ?_, ?_⟩ <;> [fin_cases i; skip] <;> simp [ac, Fin.sum_univ_three] <;> norm_num

/-- `Sseg` is reflexive and star-shaped-valued (even convex-valued): each `S x` is a segment
from `x`, hence contains `x` and is star-shaped about `x`. -/
lemma Sseg_starConvex (x : Fin 3 → ℝ) : x ∈ Sseg x ∧ StarConvex ℝ x (Sseg x) := by
  refine ⟨left_mem_segment ℝ x ac, (convex_segment x ac).starConvex (left_mem_segment ℝ x ac)⟩

/-! ## Existence of the nearest point and the value of `Q6` along the segment -/

/-- The segment `[xc, ac]` is compact. -/
lemma isCompact_Sseg : IsCompact (Sseg xc) := by
  have h : Sseg xc = (fun t : ℝ => xc + t • (ac - xc)) '' (Set.Icc 0 1) := by
    rw [Sseg, segment_eq_image']
  rw [h]; exact (isCompact_Icc).image (by fun_prop)

/-- Existence of an `ℓ⁶`-nearest point of `zc` on `[xc, ac]`. -/
lemma exists_nearest6 : ∃ y ∈ Sseg xc, ∀ b ∈ Sseg xc, Q6 zc y ≤ Q6 zc b := by
  have hcont : ContinuousOn (fun w => Q6 zc w) (Sseg xc) := by
    apply Continuous.continuousOn; unfold Q6; fun_prop
  obtain ⟨y, hy, hmin⟩ := isCompact_Sseg.exists_isMinOn ⟨xc, left_mem_segment ℝ xc ac⟩ hcont
  exact ⟨y, hy, fun b hb => hmin hb⟩

/-! ## Numeric and parametric facts about the configuration -/

/-- `Q6 (xc + t•(ac-xc)) xc = t^6 * Q6 ac xc`: the `ℓ⁶`-distance (to the 6th power) from a
segment point to `xc` scales like `t^6`. -/
lemma Q6_self_param (t : ℝ) : Q6 (xc + t • (ac - xc)) xc = t ^ 6 * Q6 ac xc := by
  simp only [Q6, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- `Q6 zc (xc + t•(ac-xc))` in the affine form used by `convexOn_sum6`. -/
lemma Q6_z_param (t : ℝ) :
    Q6 zc (xc + t • (ac - xc)) = ∑ i, ((zc i - xc i) + t * (-(ac i - xc i))) ^ 6 := by
  simp only [Q6, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- `Q6 ac xc > 0` (`ac ≠ xc`). -/
lemma A6_pos : 0 < Q6 ac xc := by
  simp only [Q6, Fin.sum_univ_three, ac, xc]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- **R1.**  `Q6 zc xc ≤ (967/1000)^6 * Q6 ac xc`  (i.e. `t₀ ≥ s₀`). -/
lemma R1 : Q6 zc xc ≤ (967 / 1000 : ℝ) ^ 6 * Q6 ac xc := by
  simp only [Q6, Fin.sum_univ_three, ac, xc, zc]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- **R2.**  `Q6 zc (xc + (1209/1250)•(ac-xc)) < Q6 zc (xc + (967/1000)•(ac-xc))`
(`G t₁ < G t₀`). -/
lemma R2 : Q6 zc (xc + (1209 / 1250 : ℝ) • (ac - xc))
    < Q6 zc (xc + (967 / 1000 : ℝ) • (ac - xc)) := by
  simp only [Q6, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    ac, xc, zc]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-! ## The main counterexample -/

/-- **Star-shapedness is not sufficient for `ℓᵖ`, `p > 1` (here `p = 6`).**

The map `S x = [x, a]` is reflexive and star-shaped-valued (`Sseg_starConvex`), yet it is
*not* good for the `ℓ⁶` metric: at `x = xc`, the point `z = zc ∈ D` (which is *closer* to
`x` than `a` is) has its `ℓ⁶`-nearest point on `[x, a]` strictly *farther* from `x` than `z`
is, violating property `[2]`. -/
theorem not_good6_segment : ¬ Good6 Sseg := by
  intro h
  obtain ⟨_, h2⟩ := h xc xc_mem
  -- the nearest point y of zc on the segment
  obtain ⟨y, hy_mem, hy_min⟩ := exists_nearest6
  have hnear : IsNearest6 (Sseg xc) zc y := by
    refine ⟨hy_mem, ?_⟩
    intro b hb; exact (dist6_le_iff _ _ _ _).2 (hy_min b hb)
  -- goodness would give dist6 y xc ≤ dist6 zc xc
  have hgood := h2 zc zc_mem y hnear
  rw [dist6_le_iff] at hgood   -- Q6 y xc ≤ Q6 zc xc
  -- but we show Q6 zc xc < Q6 y xc, a contradiction
  have hlt : Q6 zc xc < Q6 y xc := by
    -- write y = xc + s•(ac-xc), s ∈ [0,1]
    rw [Sseg, segment_eq_image'] at hy_mem
    obtain ⟨s, -, hys⟩ := hy_mem
    have hys' : xc + s • (ac - xc) = y := hys
    -- the distance-to-z function along the segment
    set G : ℝ → ℝ := fun t => Q6 zc (xc + t • (ac - xc)) with hGdef
    have hGconv : ConvexOn ℝ Set.univ G := by
      have hc := convexOn_sum6 (fun i => zc i - xc i) (fun i => -(ac i - xc i))
      have : G = fun t => ∑ i, ((zc i - xc i) + t * (-(ac i - xc i))) ^ 6 := by
        funext t; rw [hGdef]; exact Q6_z_param t
      rw [this]; exact hc
    -- s minimises G over [0,1]
    have hmin : ∀ t, 0 ≤ t → t ≤ 1 → G s ≤ G t := by
      intro t ht0 ht1
      have hmem : xc + t • (ac - xc) ∈ Sseg xc := by
        rw [Sseg, segment_eq_image']; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
      have hle := hy_min _ hmem
      rw [hGdef]; simp only; rw [hys']; exact hle
    -- the convexity bracket forces s > 967/1000
    have hs_gt : (967 / 1000 : ℝ) < s :=
      min_bracket (t0 := 967 / 1000) (t1 := 1209 / 1250) hGconv hmin
        (by norm_num) (by norm_num) (by norm_num) R2
    -- conclude Q6 zc xc ≤ (967/1000)^6 * A6 < s^6 * A6 = Q6 y xc
    have hQy : Q6 y xc = s ^ 6 * Q6 ac xc := by rw [← hys']; exact Q6_self_param s
    rw [hQy]
    calc Q6 zc xc ≤ (967 / 1000 : ℝ) ^ 6 * Q6 ac xc := R1
      _ < s ^ 6 * Q6 ac xc := by
          have hpow : (967 / 1000 : ℝ) ^ 6 < s ^ 6 := by gcongr
          exact mul_lt_mul_of_pos_right hpow A6_pos
  exact absurd hgood (not_le.2 hlt)

/-! ## Contrasting good examples for `ℓ⁶`

The extreme star-shaped values *are* still good for `ℓ⁶` (these hold for any metric): the
full simplex `S x = D` and the singletons `S x = {x}`.  The point of `not_good6_segment` is
that the *intermediate* star-shaped values (segments) need not be. -/

/-- **Good example (ℓ⁶).**  The singleton map `S x = {x}` is good. -/
theorem good6_singleton : Good6 (fun x => {x}) := by
  intro x hx
  refine ⟨rfl, ?_⟩
  intro z hz y hy
  obtain ⟨hymem, _⟩ := hy
  rw [Set.mem_singleton_iff] at hymem
  subst hymem
  rw [dist6_le_iff]
  have hz0 : Q6 y y = 0 := by simp [Q6]
  rw [hz0]; exact Q6_nonneg z y

/-- **Good example (ℓ⁶).**  The constant map `S x = D` is good: the `ℓ⁶`-nearest point of
`z ∈ D` on `D` is `z` itself. -/
theorem good6_const_D : Good6 (fun _ => D1) := by
  intro x hx
  refine ⟨hx, ?_⟩
  intro z hz y hy
  obtain ⟨hymem, hymin⟩ := hy
  -- z ∈ D minimises, so Q6 z y ≤ Q6 z z = 0, forcing y = z
  have h0 : dist6 z y ≤ dist6 z z := hymin z hz
  rw [dist6_le_iff] at h0
  have hzz : Q6 z z = 0 := by simp [Q6]
  rw [hzz] at h0
  have hQ : Q6 z y = 0 := le_antisymm h0 (Q6_nonneg z y)
  have hyz : y = z := by
    have hterm : ∀ i ∈ Finset.univ, (z i - y i) ^ 6 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 ?_
      simpa [Q6] using hQ
    funext i
    have := hterm i (Finset.mem_univ i)
    have : z i - y i = 0 := by
      have h6 := pow_eq_zero_iff (n := 6) (by norm_num) |>.1 this
      simpa using h6
    linarith
  rw [hyz]