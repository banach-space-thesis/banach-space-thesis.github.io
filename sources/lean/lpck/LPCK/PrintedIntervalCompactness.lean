import LPCK.PrintedScalarCompactness
import ThesisCommon.Analysis.IntervalDualRepresentation
import ThesisCommon.Analysis.L1RademacherMaximumBound
import ThesisCommon.Analysis.SigmaL1Partition
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The interval compactness result follows from cotype two of its actual
dual. For a scalar L₁ space the finite cotype inequality is obtained by
integrating the pointwise Khintchine estimate in finite Euclidean space. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LPCK.Printed
open ThesisCommon Grothendieck

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem l1_cotype_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    HasRademacherCotype (Lp 𝕜 1 μ) 2 3 := by
  classical
  refine ⟨le_rfl, by norm_num, ?_⟩
  intro n f
  let g (i : Fin n) (x : Ω) : EuclideanSpace ℝ (Fin n) :=
    ‖f i x‖ • EuclideanSpace.single i (1 : ℝ)
  let v (x : Ω) := ∑ i, g i x
  have hv_int : Integrable v μ :=
    integrable_finset_sum _ (fun i _ =>
      (L1.integrable_coeFn (f i)).norm.smul_const (EuclideanSpace.single i (1 : ℝ)))
  have hv (x : Ω) (i : Fin n) : v x i = ‖f i x‖ := by
    let ev := EuclideanSpace.proj (𝕜 := ℝ) i
    change ev (∑ j, g j x) = _
    rw [map_sum]
    simp [ev, g, EuclideanSpace.single_apply, apply_ite, eq_comm]
  let A (θ : Fin n → Bool) := ‖∑ i, signedValue (θ i) (f i)‖
  let a (θ : Fin n → Bool) (x : Ω) := ‖∑ i, signedValue (θ i) (f i x)‖
  have ha (θ : Fin n → Bool) : Integrable (a θ) μ :=
    ((L1.integrable_coeFn (∑ i, signedValue (θ i) (f i))).congr
      (l1_sign_sum_coe f θ)).norm
  have hpoint (x : Ω) : ‖v x‖ ≤ 3 * mean (fun θ => a θ x) := by
    have h := rclike_rademacher_second_le_nine_first_sq (fun i => f i x)
    have he : ‖v x‖ ^ 2 = ∑ i, ‖f i x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [hv, Real.norm_eq_abs, sq_abs]
    rw [← he] at h
    have hnonneg : 0 ≤ mean (fun θ => a θ x) := mean_nonneg (fun _ => norm_nonneg _)
    change ‖v x‖ ^ 2 ≤ 9 * mean (fun θ => a θ x)^2 at h
    nlinarith [norm_nonneg (v x)]
  have hint : ‖∫ x, v x ∂μ‖ ≤ 3 * mean A := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have h := integral_mono hv_int.norm ((integrable_finite_mean a ha).const_mul 3) hpoint
    rw [integral_const_mul, integral_finite_mean a ha] at h
    simpa only [A, a, ← l1_sign_sum_norm] using h
  have hcoord (i : Fin n) : (∫ x, v x ∂μ) i = ‖f i‖ := by
    change (EuclideanSpace.proj (𝕜 := ℝ) i) (∫ x, v x ∂μ) = _
    rw [← (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hv_int, L1.norm_eq_integral_norm]
    congr 1
    funext x
    exact hv x i
  have he : ‖∫ x, v x ∂μ‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hcoord, Real.norm_eq_abs, sq_abs]
  have hma : 0 ≤ mean A := mean_nonneg (fun _ => norm_nonneg _)
  have h₁ := (sq_le_sq₀ (norm_nonneg (∫ x, v x ∂μ)) (by positivity : 0 ≤ 3 * mean A)).2 hint
  have h₂ := mean_mul_sq_le (fun _ : Fin n → Bool => (1 : ℝ)) A
  simp only [one_mul, one_pow, mean_const] at h₂
  have hresult : (∑ i, ‖f i‖ ^ 2) ≤ 9 * mean (fun θ => A θ ^ 2) := by
    rw [he] at h₁
    nlinarith
  simpa only [Real.rpow_two, mean, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, A, signedValue, show (3 : ℝ) ^ 2 = 9 by norm_num,
    mul_assoc] using hresult

/-- LPCK Proposition 3.7, including p = 1 and excluding p = 2 exactly. -/
theorem proposition_3_7 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p < 2)
    (T : IntervalContinuous 𝕜 →L[𝕜] lp (fun _ : ℕ => 𝕜) p) : IsCompactOperator T := by
  let μ (_ : UnitInterval) := volume.restrict (Set.Icc (0 : ℝ) 1)
  let e := (intervalContinuousDualLebesgueEquiv 𝕜).trans
    (sigmaL1PartitionEquiv (𝕜 := 𝕜) μ).symm.toContinuousLinearEquiv
  exact scalarLp_compact_of_dual_cotype_two
    ((l1_cotype_two (𝕜 := 𝕜) (sigmaMeasure μ)).two_of_equiv (𝕜 := 𝕜) e) p hp T

end LPCK.Printed
