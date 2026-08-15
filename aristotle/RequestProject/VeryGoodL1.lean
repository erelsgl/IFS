import Mathlib
import RequestProject.L1

open scoped BigOperators

set_option maxHeartbeats 4000000

/-!
# "Very good" multifunctions on the standard 2-simplex — the `ℓ¹` case

This file is the `ℓ¹` analogue of `RequestProject/VeryGood.lean`.  Distance and "nearest
point" are measured in the `ℓ¹` (taxicab) metric `d1 a b = ∑ i, |a i - b i|` (see
`RequestProject/L1.lean`).  A map `S` is **very good** when for every `x ∈ D`: `[1] x ∈ S x`
and `[2']` for every `z ∈ D`, every `ℓ¹`-nearest point `y` of `z` on `S x` lies on the
closed line segment `[z, x]`.

Since `y ∈ [z, x]` implies `d1 y x ≤ d1 z x` (`d1_le_of_mem_segment`), **very good ⟹ good**.

## The characterization for `ℓ¹` — and the contrast with `ℓ²`

Recall that for the *good* property the `ℓ¹` answer coincides with the Euclidean one
(star-shapedness, `RequestProject/L1.lean`).  For the **very good** property the situation
is different from `ℓ²`:

* `S x = {x}` and `S x = D` are very good (`veryGood1_singleton`, `veryGood1_const_D`).

* The convex value `S x = [x, a]` (a single segment) is **good but not very good**
  (`not_veryGood1_segment`), exactly as in the Euclidean case: a point `z` whose closest
  point of `[x,a]` is an interior foot, off the segment `[z, x]`.

* Crucially, **spherical `ℓ¹`-caps are NOT very good** (unlike `ℓ²`).  The Euclidean
  characterization "very good ⟺ each value is a metric ball-cap" *fails* for `ℓ¹`, because
  the metric projection onto an `ℓ¹`-ball (a diamond) is not radial.  So star-shapedness is
  necessary but far from sufficient, and there is no clean "ball-cap" description: the very
  good `ℓ¹` values are those whose radial free boundary is `ℓ¹`-orthogonal to the radius —
  a much smaller and metric-specific family, with `{x}` and `D` the obvious members.

`cap1` (the `ℓ¹`-cap) is recorded here as a *good* example (`good1_cap`); its failure to be
very good in general is the `ℓ¹` counterpart of the Euclidean success `veryGood_cap`.
-/

namespace VeryGoodL1

/-- A set-valued map `S` is **very good** for the `ℓ¹` metric. -/
def VeryGood1 (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ)) : Prop :=
  ∀ x ∈ D1, (x ∈ S x) ∧ ∀ z ∈ D1, ∀ y, IsNearest1 (S x) z y → y ∈ segment ℝ z x

/-! ## Very good implies good -/

/-
A point of the segment `[z, x]` is no farther from `x` than `z` is, in `ℓ¹`.
-/
lemma d1_le_of_mem_segment {x z y : Fin 3 → ℝ} (hy : y ∈ segment ℝ z x) :
    d1 y x ≤ d1 z x := by
  -- By definition of $d1$, we have $d1 y x = \sum i, |y i - x i|$.
  simp [d1];
  obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hy; simp +decide [ Fin.sum_univ_three, * ] ; ring_nf;
  rw [ show b = 1 - a by linarith ] ; ring_nf;
  norm_num [ ← mul_sub, abs_mul, abs_of_nonneg ha ];
  nlinarith [ abs_nonneg ( z 0 - x 0 ), abs_nonneg ( z 1 - x 1 ), abs_nonneg ( z 2 - x 2 ) ]

/-- **Very good ⟹ good** for `ℓ¹`. -/
theorem veryGood1_imp_good1 (S : (Fin 3 → ℝ) → Set (Fin 3 → ℝ)) (h : VeryGood1 S) :
    Good1 S := by
  intro x hx
  obtain ⟨hxmem, h2⟩ := h x hx
  exact ⟨hxmem, fun z hz y hy => d1_le_of_mem_segment (h2 z hz y hy)⟩

/-! ## Very good examples -/

/-- **Very good example (ℓ¹).**  The constant map `S x = D` is very good. -/
theorem veryGood1_const_D : VeryGood1 (fun _ => D1) := by
  intro x hx
  refine ⟨hx, ?_⟩
  intro z hz y hy
  obtain ⟨hyD, hymin⟩ := hy
  have h0 : d1 z y ≤ d1 z z := hymin z hz
  have hzz : d1 z z = 0 := by simp [d1]
  rw [hzz] at h0
  have hge : 0 ≤ d1 z y := by unfold d1; positivity
  have : d1 z y = 0 := le_antisymm h0 hge
  -- d1 z y = 0 forces y = z
  have hyz : y = z := by
    have hterm : ∀ i ∈ Finset.univ, |z i - y i| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).1 (by simpa [d1] using this)
    funext i
    have := hterm i (Finset.mem_univ i)
    have : z i - y i = 0 := by simpa [abs_eq_zero] using this
    linarith
  rw [hyz]
  exact left_mem_segment ℝ z x

/-- **Very good example (ℓ¹).**  The singleton map `S x = {x}` is very good. -/
theorem veryGood1_singleton : VeryGood1 (fun x => {x}) := by
  intro x hx
  refine ⟨rfl, ?_⟩
  intro z hz y hy
  obtain ⟨hymem, _⟩ := hy
  rw [Set.mem_singleton_iff] at hymem
  rw [hymem]
  exact right_mem_segment ℝ z x

/-! ## The `ℓ¹`-cap is good (but, in general, not very good) -/

/-- The `ℓ¹`-cap `{a ∈ D | d1 a x ≤ r}`. -/
def cap1 (x : Fin 3 → ℝ) (r : ℝ) : Set (Fin 3 → ℝ) := {a | a ∈ D1 ∧ d1 a x ≤ r}

/-
**Good example (ℓ¹).**  Every `ℓ¹`-cap-valued map (radius `r x ≥ 0`) is good.  This holds
for *any* metric: a nearest point `y` of `z` lies in the cap, so `d1 y x ≤ r x`; if
`d1 z x ≤ r x` then `z` itself is in the cap, forcing `y = z`; otherwise `d1 y x ≤ r x < d1 z x`.
-/
theorem good1_cap (r : (Fin 3 → ℝ) → ℝ) (hr : ∀ x, 0 ≤ r x) :
    Good1 (fun x => cap1 x (r x)) := by
  intro x hx;
  unfold cap1;
  refine' ⟨ ⟨ hx, by simp +decide [ d1 ] ; linarith [ hr x ] ⟩, _ ⟩;
  intro z hz y hy;
  by_cases h : d1 z x ≤ r x;
  · have := hy.2 z ⟨ hz, h ⟩ ; simp_all +decide [ d1 ] ;
    -- Since $\sum i, |z i - y i| \leq 0$, we have $|z i - y i| = 0$ for all $i$, implying $z = y$.
    have h_eq : z = y := by
      exact funext fun i => sub_eq_zero.mp ( abs_nonpos_iff.mp ( le_trans ( Finset.single_le_sum ( fun i _ => abs_nonneg ( z i - y i ) ) ( Finset.mem_univ i ) ) this ) );
    rw [ h_eq ];
  · exact le_trans hy.1.2 ( le_of_not_ge h )

/-! ## A good example that is NOT very good (ℓ¹) -/

/-- Fixed target `a = (1/4, 1/4, 1/2) ∈ D`. -/
noncomputable def a1 : Fin 3 → ℝ := ![1/4, 1/4, 1/2]
/-- Center `x = (1/2, 1/2, 0) ∈ D`. -/
noncomputable def x1 : Fin 3 → ℝ := ![1/2, 1/2, 0]
/-- Test point `z = (0, 1/2, 1/2) ∈ D`. -/
noncomputable def z1 : Fin 3 → ℝ := ![0, 1/2, 1/2]

/-- The reflexive, convex-valued (hence star-shaped) map `S x = [x, a]`. -/
def Sseg1 : (Fin 3 → ℝ) → Set (Fin 3 → ℝ) := fun x => segment ℝ x a1

lemma a1_mem : a1 ∈ D1 := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp [a1]
  · simp [a1, Fin.sum_univ_three]; norm_num
lemma x1_mem : x1 ∈ D1 := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp [x1]
  · simp [x1, Fin.sum_univ_three]; norm_num
lemma z1_mem : z1 ∈ D1 := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp [z1]
  · simp [z1, Fin.sum_univ_three]; norm_num

/-- `Sseg1` is good: each value is a segment from `x`, hence star-shaped about `x` and `⊆ D`. -/
theorem good1_Sseg1 : Good1 Sseg1 := by
  apply good1_of_starConvex
  intro x hx
  refine ⟨left_mem_segment ℝ x a1, (convex_segment x a1).starConvex (left_mem_segment ℝ x a1), ?_⟩
  exact convex_D1.segment_subset hx a1_mem

/-- The segment `[x1, a1]` is compact. -/
lemma isCompact_Sseg1 : IsCompact (Sseg1 x1) := by
  rw [Sseg1, segment_eq_image']
  exact (isCompact_Icc).image (by fun_prop)

/-- Existence of an `ℓ¹`-nearest point of `z1` on `[x1, a1]`. -/
lemma exists_nearest1 : ∃ y, IsNearest1 (Sseg1 x1) z1 y := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Sseg1.exists_isMinOn
    ⟨x1, left_mem_segment ℝ x1 a1⟩ (by unfold d1; fun_prop : ContinuousOn (fun w => d1 z1 w) (Sseg1 x1))
  exact ⟨y, hy, fun b hb => hmin hb⟩

/-
Key geometric fact: the segment `[x1, a1]` meets the segment `[z1, x1]` only at `x1`.
(The middle coordinate of `z1 - x1` is `0`, while that of `a1 - x1` is `-1/4 ≠ 0`.)
-/
lemma Sseg1_inter_segment {p : Fin 3 → ℝ} (hp1 : p ∈ Sseg1 x1) (hp2 : p ∈ segment ℝ z1 x1) :
    p = x1 := by
  simp_all +decide [ Sseg1, segment_eq_image' ];
  obtain ⟨ x, hx, rfl ⟩ := hp1; obtain ⟨ y, hy, hy' ⟩ := hp2; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
  unfold z1 x1 a1 at * ; norm_num at * ;
  linarith

/-- `d1 z1 a1 < d1 z1 x1`: in `ℓ¹`, `d1 z1 a1 = 1/2 < 1 = d1 z1 x1`. -/
lemma d1_z1_a1_lt : d1 z1 a1 < d1 z1 x1 := by
  simp [d1, Fin.sum_univ_three, z1, a1, x1]
  norm_num

/-- **Good but NOT very good (ℓ¹).**  `Sseg1` is good (`good1_Sseg1`) but not very good: at
`x = x1`, the point `z = z1 ∈ D` (with `a1` strictly closer to `z1` than `x1` is) has its
`ℓ¹`-nearest point on `[x1, a1]` off the segment `[z1, x1]`. -/
theorem not_veryGood1_segment : ¬ VeryGood1 Sseg1 := by
  intro h
  obtain ⟨_, h2⟩ := h x1 x1_mem
  obtain ⟨y, hy⟩ := exists_nearest1
  have hyseg : y ∈ segment ℝ z1 x1 := h2 z1 z1_mem y hy
  have hyx1 : y = x1 := Sseg1_inter_segment hy.1 hyseg
  have ha1mem : a1 ∈ Sseg1 x1 := right_mem_segment ℝ x1 a1
  have hle : d1 z1 y ≤ d1 z1 a1 := hy.2 a1 ha1mem
  rw [hyx1] at hle
  have := d1_z1_a1_lt
  linarith [hle, this]

end VeryGoodL1