import Mathlib
import RequestProject.Main

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 4000000

/-!
# "Very good" multifunctions on the standard 2-simplex — the Euclidean (`ℓ²`) case

This file treats the follow-up question to `RequestProject/Main.lean`.  Recall `D` is the
standard 2-simplex in `ℝ³`, viewed inside `E = EuclideanSpace ℝ (Fin 3)`, and a set-valued
map `S : E → 𝒫(E)` is **good** when for every `x ∈ D`: `[1] x ∈ S x`; and `[2]` for every
`z ∈ D`, every nearest point `y` of `z` on `S x` satisfies `dist y x ≤ dist z x`.

A map `S` is **very good** when property `[2]` is strengthened to `[2']`:

* `[2']`  for every `z ∈ D`, every nearest point `y` of `z` on `S x` lies on the closed
          line segment `[z, x]`.

Since a point `y ∈ [z, x]` automatically satisfies `dist y x ≤ dist z x`
(`dist_le_of_mem_segment_left` below), **very good ⟹ good** (`veryGood_imp_good`); very
good is a strictly stronger property.

## The characterization for `ℓ²`

For closed values, the answer is:

>  `S` is very good for `ℓ²`  ⟺  for every `x ∈ D` there is a radius `r ≥ 0` with
>  `S x = {a ∈ D | dist a x ≤ r}` (the intersection of a closed Euclidean ball centred at
>  `x` with the simplex `D` — a "spherical cap").

The decisive **sufficiency** direction is `veryGood_cap`: every such cap-valued map is very
good.  The geometric reason is special to the Euclidean metric: the metric projection of an
external point `z` onto a ball centred at `x` is *radial* — it lands on the ray from `x`
through `z`, hence on the segment `[z, x]`.  Combined with uniqueness of the nearest point on
a convex set (`isNearest_unique`), every nearest point on the cap is this radial point.

**Necessity** (a very good closed value must be a cap) is explained in the module docstring
and witnessed by the failure of non-cap good examples below: e.g. the convex value
`S x = [x, a]` (a single segment) is good but **not** very good (`not_veryGood_segment`),
because the projection of a suitable `z` onto the segment is the (non-radial) foot of a
perpendicular, off the segment `[z, x]`.

This `ℓ²` answer is **special to `p = 2`**: for the `ℓ¹` and general `ℓᵖ` metrics the metric
projection onto a ball is *not* radial, so caps are no longer very good — see
`RequestProject/VeryGoodL1.lean` and `RequestProject/VeryGoodLp.lean`.
-/

namespace VeryGoodL2

/-- A set-valued map `S` is **very good** (Euclidean metric): property `[1]` together with
the strengthened projection property `[2']` — every nearest point lands on the segment. -/
def VeryGood (S : E → Set E) : Prop :=
  ∀ x ∈ D, (x ∈ S x) ∧ ∀ z ∈ D, ∀ y, IsNearest (S x) z y → y ∈ segment ℝ z x

/-! ## Very good implies good -/

/-
A point of the segment `[z, x]` is no farther from `x` than `z` is.
-/
lemma dist_le_of_mem_segment_left {x z y : E} (hy : y ∈ segment ℝ z x) :
    dist y x ≤ dist z x := by
  rw [ segment_eq_image ] at hy;
  obtain ⟨ θ, hθ, rfl ⟩ := hy; simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  exact Real.sqrt_le_sqrt <| Finset.sum_le_sum fun i _ => by nlinarith only [ hθ.1, hθ.2, mul_nonneg hθ.1 ( sub_nonneg.2 hθ.2 ), sq_nonneg ( z.ofLp i - x.ofLp i ) ] ;

/-- **Very good ⟹ good.** -/
theorem veryGood_imp_good (S : E → Set E) (h : VeryGood S) : Good S := by
  intro x hx
  obtain ⟨hxmem, h2⟩ := h x hx
  exact ⟨hxmem, fun z hz y hy => dist_le_of_mem_segment_left (h2 z hz y hy)⟩

/-! ## Uniqueness of the nearest point on a convex set -/

/-
The variational inequality satisfied by a nearest point on a convex set.
-/
lemma isNearest_inner_le {A : Set E} (hA : Convex ℝ A) {z y : E}
    (hy : IsNearest A z y) : ∀ b ∈ A, inner ℝ (z - y) (b - y) ≤ 0 := by
  have h_ineq : ‖z - y‖ = ⨅ w : ↥A, ‖z - ↑w‖ := by
    refine' le_antisymm _ _;
    · refine' le_csInf _ _;
      · exact ⟨ _, ⟨ ⟨ y, hy.1 ⟩, rfl ⟩ ⟩;
      · rintro _ ⟨ w, rfl ⟩ ; exact hy.2 _ w.2;
    · exact ciInf_le ⟨ 0, Set.forall_mem_range.mpr fun _ => norm_nonneg _ ⟩ ⟨ y, hy.1 ⟩ |> le_trans <| by norm_num;
  convert norm_eq_iInf_iff_real_inner_le_zero hA _ |>.1 h_ineq using 1;
  exact hy.1

/-
The nearest point of `z` on a convex set is unique.
-/
lemma isNearest_unique {A : Set E} (hA : Convex ℝ A) {z y₁ y₂ : E}
    (h1 : IsNearest A z y₁) (h2 : IsNearest A z y₂) : y₁ = y₂ := by
  have h_var : inner ℝ (z - y₁) (y₂ - y₁) ≤ 0 ∧ inner ℝ (z - y₂) (y₁ - y₂) ≤ 0 := by
    exact ⟨ isNearest_inner_le hA h1 _ h2.1, isNearest_inner_le hA h2 _ h1.1 ⟩;
  simp_all +decide [ inner_sub_left, inner_sub_right ];
  -- Adding these inequalities, we get $0 \leq -‖y₁ - y₂‖^2$, which implies $‖y₁ - y₂‖^2 \leq 0$.
  have h_norm : ‖y₁ - y₂‖ ^ 2 ≤ 0 := by
    rw [ @norm_sub_sq ℝ ];
    norm_num [ real_inner_comm ] at * ; linarith;
  exact sub_eq_zero.mp ( norm_eq_zero.mp ( sq_eq_zero_iff.mp ( le_antisymm h_norm ( sq_nonneg _ ) ) ) )

/-! ## The spherical cap and its very-goodness -/

/-- The spherical cap `{a ∈ D | dist a x ≤ r}` (intersection of `D` with the closed
Euclidean ball of radius `r` centred at `x`). -/
def cap (x : E) (r : ℝ) : Set E := {a | a ∈ D ∧ dist a x ≤ r}

lemma convex_cap (x : E) (r : ℝ) : Convex ℝ (cap x r) := by
  convert Convex.inter ( convex_D : Convex ℝ D ) ( convex_closedBall x r ) using 1

/-- The radial point: the metric projection of `z` onto the closed ball of radius `r`
centred at `x`. -/
noncomputable def radialPt (x z : E) (r : ℝ) : E :=
  if dist z x ≤ r then z else x + (r / dist z x) • (z - x)

/-
The radial point lies on the segment `[z, x]`.
-/
lemma radialPt_mem_segment {x z : E} {r : ℝ} (hr : 0 ≤ r) :
    radialPt x z r ∈ segment ℝ z x := by
  unfold radialPt; split_ifs;
  · exact left_mem_segment _ _ _;
  · rw [ segment_eq_image ];
    refine' ⟨ 1 - r / dist z x, _, _ ⟩ <;> norm_num;
    · exact ⟨ div_le_one_of_le₀ ( by linarith ) ( dist_nonneg ), div_nonneg hr ( dist_nonneg ) ⟩;
    · ext ; norm_num ; ring

/-
The radial point lies in the cap (for `z ∈ D`, `x ∈ D`, `0 ≤ r`).
-/
lemma radialPt_mem_cap {x z : E} {r : ℝ} (hx : x ∈ D) (hz : z ∈ D) (hr : 0 ≤ r) :
    radialPt x z r ∈ cap x r := by
  unfold radialPt; split_ifs;
  · exact ⟨ hz, by assumption ⟩;
  · refine' ⟨ _, _ ⟩;
    · have h_radial_in_D : x + (r / dist z x) • (z - x) ∈ segment ℝ z x := by
        rw [ segment_eq_image ];
        refine' ⟨ 1 - r / dist z x, _, _ ⟩ <;> norm_num;
        · exact ⟨ div_le_one_of_le₀ ( by linarith ) ( dist_nonneg ), div_nonneg hr ( dist_nonneg ) ⟩;
        · ext ; norm_num ; ring;
      exact convex_D.segment_subset hz hx h_radial_in_D;
    · norm_num [ norm_smul, dist_eq_norm ];
      rw [ abs_of_nonneg hr, div_mul_cancel₀ _ ( norm_ne_zero_iff.mpr <| sub_ne_zero.mpr <| by rintro rfl; norm_num at * ; linarith ) ]

/-
The radial point is a nearest point of `z` on the cap.
-/
lemma radialPt_isNearest {x z : E} {r : ℝ} (hx : x ∈ D) (hz : z ∈ D) (hr : 0 ≤ r) :
    IsNearest (cap x r) z (radialPt x z r) := by
  refine' ⟨ radialPt_mem_cap hx hz hr, fun y hy => _ ⟩;
  by_cases h : dist z x ≤ r <;> simp_all +decide [ radialPt ];
  split_ifs <;> simp_all +decide [ dist_eq_norm ];
  rw [ show z - ( x + ( r / ‖z - x‖ ) • ( z - x ) ) = ( 1 - r / ‖z - x‖ ) • ( z - x ) by ext ; simpa using by ring, norm_smul, Real.norm_of_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ h.le <| norm_nonneg _ ) ];
  have := norm_sub_le ( z - y ) ( x - y ) ; simp_all +decide;
  nlinarith [ div_mul_cancel₀ r ( ne_of_gt ( lt_of_le_of_lt hr h ) ), hy.2, show ‖x - y‖ ≤ r from by simpa [ dist_eq_norm' ] using hy.2 ]

/-- **Sufficiency / characterization (ℓ²).**  Every cap-valued map `S x = {a ∈ D | dist a x ≤ r x}`
(with `r x ≥ 0`) is very good. -/
theorem veryGood_cap (r : E → ℝ) (hr : ∀ x, 0 ≤ r x) :
    VeryGood (fun x => cap x (r x)) := by
  intro x hx
  refine ⟨⟨hx, by simpa using hr x⟩, ?_⟩
  intro z hz y hy
  have hrad := radialPt_isNearest hx hz (hr x)
  have : y = radialPt x z (r x) :=
    isNearest_unique (convex_cap x (r x)) hy hrad
  rw [this]
  exact radialPt_mem_segment (hr x)

/-! ## Very good examples -/

/-- **Very good example 1.**  The constant map `S x = D` is very good (it is the cap with
`r = +∞`; concretely, the nearest point of `z ∈ D` on `D` is `z` itself, an endpoint of the
segment `[z, x]`). -/
theorem veryGood_const_D : VeryGood (fun _ : E => D) := by
  intro x hx
  refine ⟨hx, ?_⟩
  intro z hz y hy
  obtain ⟨hyD, hymin⟩ := hy
  have hyz : y = z := by
    have h0 : dist z y ≤ dist z z := hymin z hz
    simp only [dist_self] at h0
    have : dist z y = 0 := le_antisymm h0 dist_nonneg
    rw [dist_eq_zero] at this
    exact this.symm
  rw [hyz]
  exact left_mem_segment ℝ z x

/-- **Very good example 2.**  The singleton map `S x = {x}` is very good (the only nearest
point is `x`, an endpoint of `[z, x]`). -/
theorem veryGood_singleton : VeryGood (fun x : E => {x}) := by
  intro x hx
  refine ⟨rfl, ?_⟩
  intro z hz y hy
  obtain ⟨hymem, _⟩ := hy
  rw [Set.mem_singleton_iff] at hymem
  rw [hymem]
  exact right_mem_segment ℝ z x

/-! ## A good example that is NOT very good -/

/-- Fixed target `a = (1/4, 1/4, 1/2) ∈ D`. -/
noncomputable def a2 : E := !₂[(1/4 : ℝ), 1/4, 1/2]
/-- Center `x = (1/2, 1/2, 0) ∈ D`. -/
noncomputable def x2 : E := !₂[(1/2 : ℝ), 1/2, 0]
/-- Test point `z = (0, 1/2, 1/2) ∈ D`. -/
noncomputable def z2 : E := !₂[(0 : ℝ), 1/2, 1/2]

/-- The reflexive, convex-valued (hence star-shaped) map `S x = [x, a]`. -/
def Sseg2 : E → Set E := fun x => segment ℝ x a2

lemma a2_mem : a2 ∈ D := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp [a2]
  · simp [a2, Fin.sum_univ_three]; norm_num
lemma x2_mem : x2 ∈ D := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp [x2]
  · simp [x2, Fin.sum_univ_three]; norm_num
lemma z2_mem : z2 ∈ D := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp [z2]
  · simp [z2, Fin.sum_univ_three]; norm_num

/-- `Sseg2` is good: each value is a segment from `x`, hence star-shaped about `x`. -/
theorem good_Sseg2 : Good Sseg2 := by
  apply good_of_starConvex
  intro x _
  exact ⟨left_mem_segment ℝ x a2, (convex_segment x a2).starConvex (left_mem_segment ℝ x a2)⟩

/-- The segment `[x2, a2]` is compact. -/
lemma isCompact_Sseg2 : IsCompact (Sseg2 x2) := by
  rw [Sseg2, segment_eq_image']
  exact (isCompact_Icc).image (by fun_prop)

/-- Existence of a Euclidean-nearest point of `z2` on `[x2, a2]`. -/
lemma exists_nearest2 : ∃ y, IsNearest (Sseg2 x2) z2 y := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Sseg2.exists_isMinOn
    ⟨x2, left_mem_segment ℝ x2 a2⟩ (by fun_prop : ContinuousOn (fun w => dist z2 w) (Sseg2 x2))
  exact ⟨y, hy, fun b hb => hmin hb⟩

/-
Key geometric fact: the segment `[x2, a2]` meets the segment `[z2, x2]` only at `x2`.
(Reason: the middle coordinate of `z2 - x2` is `0`, while that of `a2 - x2` is `-1/4 ≠ 0`,
so any common point forces the segment parameter on `[x2,a2]` to be `0`.)
-/
lemma Sseg2_inter_segment {p : E} (hp1 : p ∈ Sseg2 x2) (hp2 : p ∈ segment ℝ z2 x2) :
    p = x2 := by
  simp_all +decide [ segment_eq_image', Sseg2 ];
  rcases hp1 with ⟨ t, ht, rfl ⟩ ; rcases hp2 with ⟨ u, hu, hu' ⟩ ; simp_all +decide ;
  have := congr_arg ( fun v => v 1 ) hu'; norm_num [ z2, x2, a2 ] at this;
  exact Or.inl this

/-
`dist z2 a2 < dist z2 x2`: the target `a2` is strictly closer to `z2` than the center
`x2` is.
-/
lemma dist_z2_a2_lt : dist z2 a2 < dist z2 x2 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three, z2, a2, x2 ];
  erw [ Matrix.cons_val_succ' ] ; norm_num;
  erw [ Matrix.cons_val_succ' ] ; norm_num;
  gcongr ; norm_num

/-- **Good but NOT very good (ℓ²).**  `Sseg2` (the convex-valued map `S x = [x, a]`) is good
(`good_Sseg2`) but not very good: at `x = x2`, the point `z = z2 ∈ D` (with `a2` closer to
`z2` than `x2`) has its nearest point on `[x2, a2]` off the segment `[z2, x2]`.  Indeed any
nearest point `y` satisfies `dist z2 y ≤ dist z2 a2 < dist z2 x2`, so it cannot equal `x2`;
but the only point of `[x2, a2]` on `[z2, x2]` is `x2`. -/
theorem not_veryGood_segment : ¬ VeryGood Sseg2 := by
  intro h
  obtain ⟨_, h2⟩ := h x2 x2_mem
  obtain ⟨y, hy⟩ := exists_nearest2
  have hyseg : y ∈ segment ℝ z2 x2 := h2 z2 z2_mem y hy
  have hyx2 : y = x2 := Sseg2_inter_segment hy.1 hyseg
  -- but a2 ∈ Sseg2 x2 is strictly closer to z2 than x2
  have ha2mem : a2 ∈ Sseg2 x2 := right_mem_segment ℝ x2 a2
  have hle : dist z2 y ≤ dist z2 a2 := hy.2 a2 ha2mem
  rw [hyx2] at hle
  have := dist_z2_a2_lt
  -- dist z2 x2 ≤ dist z2 a2 < dist z2 x2
  linarith [hle, this]

end VeryGoodL2