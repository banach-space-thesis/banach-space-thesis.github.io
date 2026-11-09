import BanachIsometric.StarBody
import Mathlib.Analysis.NormedSpace.Normalize
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Geometry of definite homogeneous functions

Sphere Lipschitz regularity implies global Lipschitz regularity without a
triangle inequality for the function. In finite dimension its unit sublevel
set is compact and contains a neighbourhood of zero. These are the geometric
hypotheses needed to apply the covariance and moment arguments to Theorem A.
-/

namespace BanachIsometric

open NormedSpace
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The normalization estimate used in equation (2), with no ordering of the
two norms required. The second vector must be nonzero. -/
theorem norm_mul_normalize_sub_le (x y : V) (hy : y ≠ 0) :
    ‖x‖ * ‖normalize x - normalize y‖ ≤ 2 * ‖x - y‖ := by
  have hid : ‖x‖ • (normalize x - normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • normalize y := by
    simp only [smul_sub, sub_smul, norm_smul_normalize]
    abel
  calc
    ‖x‖ * ‖normalize x - normalize y‖ =
        ‖‖x‖ • (normalize x - normalize y)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
    _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • normalize y‖ := by
      rw [hid]
      exact norm_add_le _ _
    _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs, norm_normalize hy, mul_one]
    _ ≤ 2 * ‖x - y‖ := by
      have h := abs_norm_sub_norm_le y x
      rw [norm_sub_rev] at h
      linarith

/-- Upper sphere bounds extend to linear norm bounds by positive homogeneity. -/
theorem IsDefinitePositiveHomogeneous.le_norm_mul {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {M : ℝ}
    (hM : ∀ u : V, ‖u‖ = 1 → p u ≤ M) (x : V) : p x ≤ M * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, (hp.eq_zero_iff 0).mpr rfl]
  rw [hp.radial_identity hx]
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := norm_normalize hx
  nlinarith [hM (‖x‖⁻¹ • x) hu, norm_nonneg x]

/-- Lower sphere bounds extend to linear norm bounds by positive homogeneity. -/
theorem IsDefinitePositiveHomogeneous.norm_mul_le {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {ε : ℝ}
    (hε : ∀ u : V, ‖u‖ = 1 → ε ≤ p u) (x : V) : ε * ‖x‖ ≤ p x := by
  by_cases hx : x = 0
  · simp [hx, (hp.eq_zero_iff 0).mpr rfl]
  rw [hp.radial_identity hx]
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := norm_normalize hx
  nlinarith [hε (‖x‖⁻¹ • x) hu, norm_nonneg x]

/-- The global Lipschitz estimate for a definite positive homogeneous function.
`M` bounds its values on the sphere, and `C` is its sphere Lipschitz constant.
Neither convexity nor central symmetry is assumed. -/
theorem IsDefinitePositiveHomogeneous.lipschitzWith_of_sphere {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {M C : ℝ≥0}
    (hM : ∀ u : V, ‖u‖ = 1 → p u ≤ M)
    (hC : LipschitzOnWith C p (Metric.sphere 0 1)) :
    LipschitzWith (M + 2 * C) p := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp0 : p 0 = 0 := (hp.eq_zero_iff 0).mpr rfl
  have hcoef : (M : ℝ) ≤ ((M + 2 * C : ℝ≥0) : ℝ) := by
    push_cast
    nlinarith [C.coe_nonneg]
  by_cases hx : x = 0
  · subst x
    rw [hp0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hp.nonneg y),
      dist_zero_left]
    exact (hp.le_norm_mul hM y).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg y))
  by_cases hy : y = 0
  · subst y
    rw [hp0, Real.dist_eq, sub_zero, abs_of_nonneg (hp.nonneg x), dist_zero_right]
    exact (hp.le_norm_mul hM x).trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg x))
  have hu : normalize x ∈ Metric.sphere (0 : V) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize hx
  have hv : normalize y ∈ Metric.sphere (0 : V) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize hy
  have hdiff : |p (normalize x) - p (normalize y)| ≤
      (C : ℝ) * ‖normalize x - normalize y‖ := by
    simpa only [Real.dist_eq, dist_eq_norm] using hC.dist_le_mul _ hu _ hv
  have hpv : |p (normalize y)| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (hp.nonneg _)]
    exact hM _ (norm_normalize hy)
  have hnorm : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  rw [Real.dist_eq, dist_eq_norm, hp.radial_identity hx, hp.radial_identity hy]
  change |‖x‖ * p (normalize x) - ‖y‖ * p (normalize y)| ≤ _
  calc
    |‖x‖ * p (normalize x) - ‖y‖ * p (normalize y)| =
        |‖x‖ * (p (normalize x) - p (normalize y)) +
          (‖x‖ - ‖y‖) * p (normalize y)| := by congr 1; ring
    _ ≤ |‖x‖ * (p (normalize x) - p (normalize y))| +
        |(‖x‖ - ‖y‖) * p (normalize y)| := abs_add_le _ _
    _ = ‖x‖ * |p (normalize x) - p (normalize y)| +
        |‖x‖ - ‖y‖| * |p (normalize y)| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg x), abs_mul]
    _ ≤ ‖x‖ * ((C : ℝ) * ‖normalize x - normalize y‖) + ‖x - y‖ * (M : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdiff (norm_nonneg x))
        (mul_le_mul hnorm hpv (abs_nonneg _) (norm_nonneg _))
    _ = (C : ℝ) * (‖x‖ * ‖normalize x - normalize y‖) + (M : ℝ) * ‖x - y‖ := by ring
    _ ≤ (C : ℝ) * (2 * ‖x - y‖) + (M : ℝ) * ‖x - y‖ := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (norm_mul_normalize_sub_le x y hy) C.coe_nonneg) _
    _ = ((M + 2 * C : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring

end BanachIsometric
