import JLMS.CZeroTools

/-!
# Positive and negative parts of real C₀ functions

The positive part stays continuous and vanishes at infinity. These norm and
sublinearity lemmas are the lattice ingredients for the signed Riesz theorem.
They do not assume compactness, scatteredness or a countable base.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {K : Type*} [TopologicalSpace K]

def positivePartCZero (f : CZero ℝ K) : CZero ℝ K where
  toFun x := max (f x) 0
  continuous_toFun := f.continuous_toFun.max continuous_const
  zero_at_infty' := by simpa using f.zero_at_infty'.max (tendsto_const_nhds (x := (0 : ℝ)))

@[simp] theorem positivePartCZero_apply (f : CZero ℝ K) (x : K) :
    positivePartCZero f x = max (f x) 0 := rfl

theorem positivePartCZero_nonneg (f : CZero ℝ K) (x : K) :
    0 ≤ positivePartCZero f x := le_max_right _ _

theorem norm_positivePartCZero_le (f : CZero ℝ K) : ‖positivePartCZero f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖max (f x) 0‖ ≤ ‖f‖
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _ |>.trans (norm_CZero_apply_le f x)) (norm_nonneg f)

theorem positivePartCZero_eq_zero {f : CZero ℝ K} (h : ∀ x, f x ≤ 0) :
    positivePartCZero f = 0 := by
  ext x
  exact max_eq_right (h x)

theorem positivePartCZero_smul {c : ℝ} (hc : 0 ≤ c) (f : CZero ℝ K) :
    positivePartCZero (c • f) = c • positivePartCZero f := by
  ext x
  change max (c * f x) 0 = c * max (f x) 0
  by_cases hx : 0 ≤ f x
  · rw [max_eq_left hx, max_eq_left (mul_nonneg hc hx)]
  · have hfx : f x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hfx, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hfx), mul_zero]

theorem positivePartCZero_sub_negative (f : CZero ℝ K) :
    positivePartCZero f - positivePartCZero (-f) = f := by
  ext x
  change max (f x) 0 - max (-f x) 0 = f x
  by_cases hx : 0 ≤ f x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · have hfx : f x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hfx, max_eq_left (neg_nonneg.mpr hfx)]
    ring

theorem norm_le_positivePartCZero_add_negative (f : CZero ℝ K) :
    ‖f‖ ≤ ‖positivePartCZero f‖ + ‖positivePartCZero (-f)‖ := by
  calc
    ‖f‖ = ‖positivePartCZero f - positivePartCZero (-f)‖ :=
      congrArg norm (positivePartCZero_sub_negative f).symm
    _ ≤ ‖positivePartCZero f‖ + ‖positivePartCZero (-f)‖ := norm_sub_le _ _

theorem norm_positivePartCZero_add_le (f g : CZero ℝ K) :
    ‖positivePartCZero (f + g)‖ ≤ ‖positivePartCZero f‖ + ‖positivePartCZero g‖ := by
  apply (BoundedContinuousFunction.norm_le (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  change ‖max (f x + g x) 0‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have hf : max (f x) 0 ≤ ‖positivePartCZero f‖ := by
    simpa only [positivePartCZero_apply, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (f x) (0 : ℝ))]
      using norm_CZero_apply_le (positivePartCZero f) x
  have hg : max (g x) 0 ≤ ‖positivePartCZero g‖ := by
    simpa only [positivePartCZero_apply, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (g x) (0 : ℝ))]
      using norm_CZero_apply_le (positivePartCZero g) x
  apply max_le
  · linarith [le_max_left (f x) 0, le_max_left (g x) 0]
  · exact add_nonneg (norm_nonneg _) (norm_nonneg _)

end JLMS
