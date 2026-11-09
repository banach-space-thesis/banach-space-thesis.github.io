import PL1.IntrinsicGraph
import PL1.ResolventEstimates
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Lifting a common eigenspace into the intrinsic graph

The analytic lifting step of the non-Schur construction. A bounded-below map
into the base space lifts to a closed isomorphic copy in the intrinsic graph
when its weighted coordinates have a uniform summable bound. Specializing to
the common resolvent eigenvalue `a = 1` gives the first-chaos mechanism.
The concrete Rademacher map from `ell2` is not assumed to have been constructed.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators NNReal

namespace PL1.EigenvectorEmbedding

open IntrinsicGraph ResolventEstimates

variable {𝕜 H Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

section GeneralLift

variable (D : ℕ → Y →L[𝕜] Y) (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
  (T : H →L[𝕜] Y) (hs : ∀ x, Summable (fun n => ‖D n (T x)‖))

/-- The algebraic lift of a map whose coordinate norms are summable. -/
def liftLinear : H →ₗ[𝕜] Space D where
  toFun x := ofSummable D h0 (T x) (hs x)
  map_add' x y := by
    apply evalZero_injective D
    simp only [map_add, evalZero_ofSummable]
  map_smul' c x := by
    apply evalZero_injective D
    simp only [map_smul, evalZero_ofSummable, RingHom.id_apply]

/-- A uniform coordinate-sum estimate makes the lift continuous. -/
def lift (C : ℝ) (hC : ∀ x, (∑' n, ‖D n (T x)‖) ≤ C * ‖x‖) :
    H →L[𝕜] Space D :=
  (liftLinear D h0 T hs).mkContinuous C (fun x => by
    change ‖ofSummable D h0 (T x) (hs x)‖ ≤ C * ‖x‖
    rw [norm_ofSummable]
    exact hC x)

variable (C : ℝ) (hC : ∀ x, (∑' n, ‖D n (T x)‖) ≤ C * ‖x‖)

@[simp]
theorem evalZero_lift (x : H) : evalZero D (lift D h0 T hs C hC x) = T x :=
  evalZero_ofSummable D h0 (T x) (hs x)

@[simp]
theorem coord_lift (n : ℕ) (x : H) : coord D n (lift D h0 T hs C hC x) = D n (T x) := rfl

theorem norm_lift_eq (x : H) :
    ‖lift D h0 T hs C hC x‖ = ∑' n, ‖D n (T x)‖ :=
  norm_ofSummable D h0 (T x) (hs x)

theorem norm_base_le_lift (x : H) : ‖T x‖ ≤ ‖lift D h0 T hs C hC x‖ := by
  simpa only [evalZero_lift] using norm_evalZero_le D (lift D h0 T hs C hC x)

theorem lift_antilipschitz (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    AntilipschitzWith K (lift D h0 T hs C hC) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  exact (hT x).trans (mul_le_mul_of_nonneg_left (norm_base_le_lift D h0 T hs C hC x) K.coe_nonneg)

theorem lift_isClosed_range [CompleteSpace H] (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    IsClosed ((lift D h0 T hs C hC).range : Set (Space D)) :=
  (lift_antilipschitz D h0 T hs C hC K hT).isClosed_range
    (lift D h0 T hs C hC).uniformContinuous

/-- The lifted embedding is a genuine continuous linear equivalence onto its closed range. -/
def liftEquivRange [CompleteSpace H] [CompleteSpace Y]
    (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    H ≃L[𝕜] (lift D h0 T hs C hC).range :=
  (lift D h0 T hs C hC).equivRange
    (lift_antilipschitz D h0 T hs C hC K hT).injective
    (lift_isClosed_range D h0 T hs C hC K hT)

include h0 hs C hC in
theorem containsIsomorphicCopy_of_coordinate_bound [CompleteSpace H] [CompleteSpace Y]
    (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    PL1.ContainsIsomorphicCopy 𝕜 H (Space D) :=
  ⟨(lift D h0 T hs C hC).range,
    lift_isClosed_range D h0 T hs C hC K hT,
    ⟨liftEquivRange D h0 T hs C hC K hT⟩⟩

end GeneralLift

section ScalarCoordinates

variable (D : ℕ → Y →L[𝕜] Y) (T : H →L[𝕜] Y) (α : ℕ → 𝕜)
  (hα : Summable (fun n => ‖α n‖))
  (heigen : ∀ n x, D n (T x) = α n • T x)

include heigen

include hα in
theorem scalar_coordinates_summable (x : H) : Summable (fun n => ‖D n (T x)‖) := by
  simpa only [heigen, norm_smul] using hα.mul_right ‖T x‖

theorem scalar_coordinates_tsum (x : H) :
    (∑' n, ‖D n (T x)‖) = (∑' n, ‖α n‖) * ‖T x‖ := by
  simp only [heigen, norm_smul, tsum_mul_right]

theorem scalar_coordinates_bound (x : H) :
    (∑' n, ‖D n (T x)‖) ≤ ((∑' n, ‖α n‖) * ‖T‖) * ‖x‖ := by
  rw [scalar_coordinates_tsum D T α heigen]
  calc
    _ ≤ (∑' n, ‖α n‖) * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (tsum_nonneg (fun n => norm_nonneg _))
    _ = _ := by ring

include hα in
theorem containsIsomorphicCopy_of_scalar_coordinates [CompleteSpace H] [CompleteSpace Y]
    (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    PL1.ContainsIsomorphicCopy 𝕜 H (Space D) :=
  containsIsomorphicCopy_of_coordinate_bound D h0 T
    (scalar_coordinates_summable D T α hα heigen)
    ((∑' n, ‖α n‖) * ‖T‖)
    (scalar_coordinates_bound D T α heigen) K hT

end ScalarCoordinates

/-- The scalar resolvent multiplier on a common eigenspace with eigenvalue `a`. -/
def dyadicEigenvalue (a : ℝ) (n : ℕ) : ℝ := (1 + (dyadicRatio ^ 2) ^ n * a)⁻¹

/-- The resulting eigenvalues of the weighted intrinsic coordinate operators. -/
def intrinsicEigenCoefficient (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => a * dyadicRatio ^ (n + 1) / (1 + (dyadicRatio ^ 2) ^ (n + 1) * a)

theorem dyadic_eigen_denominator_pos (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    0 < 1 + (dyadicRatio ^ 2) ^ n * a := by
  have hp : 0 ≤ (dyadicRatio ^ 2) ^ n := pow_nonneg (sq_nonneg _) _
  positivity

theorem intrinsicEigenCoefficient_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ intrinsicEigenCoefficient a n := by
  cases n with
  | zero => exact zero_le_one
  | succ n =>
    exact div_nonneg (mul_nonneg ha (pow_nonneg dyadicRatio_nonneg _))
      (dyadic_eigen_denominator_pos a ha _).le

theorem intrinsicEigenCoefficient_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    intrinsicEigenCoefficient a (n + 1) ≤ a * dyadicRatio ^ (n + 1) := by
  change a * dyadicRatio ^ (n + 1) / (1 + (dyadicRatio ^ 2) ^ (n + 1) * a) ≤ _
  apply (div_le_iff₀ (dyadic_eigen_denominator_pos a ha _)).2
  apply le_mul_of_one_le_right (mul_nonneg ha (pow_nonneg dyadicRatio_nonneg _))
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (sq_nonneg _) _) ha)

theorem intrinsicEigenCoefficient_tail_summable (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun n => intrinsicEigenCoefficient a (n + 1)) :=
  (geometric_tail_summable.mul_left a).of_nonneg_of_le
    (fun n => intrinsicEigenCoefficient_nonneg a ha (n + 1))
    (intrinsicEigenCoefficient_le a ha)

theorem intrinsicEigenCoefficient_summable (a : ℝ) (ha : 0 ≤ a) :
    Summable (intrinsicEigenCoefficient a) :=
  (summable_nat_add_iff 1).1 (intrinsicEigenCoefficient_tail_summable a ha)

theorem intrinsicEigenCoefficient_norm_summable (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun n => ‖(intrinsicEigenCoefficient a n : 𝕜)‖) := by
  simpa only [RCLike.norm_ofReal, abs_of_nonneg (intrinsicEigenCoefficient_nonneg a ha _)] using
    intrinsicEigenCoefficient_summable a ha

/-- An explicit upper bound for the change from base norm to intrinsic norm. -/
def eigenNormBound (a : ℝ) : ℝ := 1 + a * dyadicRatio / (1 - dyadicRatio)

theorem eigenNormBound_nonneg (a : ℝ) (ha : 0 ≤ a) : 0 ≤ eigenNormBound a := by
  unfold eigenNormBound
  exact add_nonneg zero_le_one
    (div_nonneg (mul_nonneg ha dyadicRatio_nonneg) one_sub_dyadicRatio_pos.le)

theorem intrinsicEigenCoefficient_tsum_le (a : ℝ) (ha : 0 ≤ a) :
    (∑' n, intrinsicEigenCoefficient a n) ≤ eigenNormBound a := by
  rw [(intrinsicEigenCoefficient_summable a ha).tsum_eq_zero_add]
  change 1 + (∑' n, intrinsicEigenCoefficient a (n + 1)) ≤ _
  calc
    _ ≤ 1 + (∑' n, a * dyadicRatio ^ (n + 1)) :=
      add_le_add le_rfl (Summable.tsum_le_tsum (intrinsicEigenCoefficient_le a ha)
        (intrinsicEigenCoefficient_tail_summable a ha) (geometric_tail_summable.mul_left a))
    _ = eigenNormBound a := by rw [tsum_mul_left, geometric_tail_tsum]; unfold eigenNormBound; ring

theorem intrinsicEigenCoefficient_norm_tsum_le (a : ℝ) (ha : 0 ≤ a) :
    (∑' n, ‖(intrinsicEigenCoefficient a n : 𝕜)‖) ≤ eigenNormBound a := by
  simpa only [RCLike.norm_ofReal, abs_of_nonneg (intrinsicEigenCoefficient_nonneg a ha _)] using
    intrinsicEigenCoefficient_tsum_le a ha

/-- Cancellation between the dyadic weight and the defect of a resolvent multiplier. -/
theorem intrinsicEigenCoefficient_eq_weighted_defect (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    intrinsicEigenCoefficient a (n + 1) =
      (dyadicRatio ^ (n + 1))⁻¹ * (1 - dyadicEigenvalue a (n + 1)) := by
  unfold intrinsicEigenCoefficient dyadicEigenvalue
  rw [dyadicRatio_sq_pow]
  have hd : 1 + (dyadicRatio ^ (n + 1)) ^ 2 * a ≠ 0 := by
    rw [← dyadicRatio_sq_pow]
    exact ne_of_gt (dyadic_eigen_denominator_pos a ha _)
  field_simp [dyadicRatio_pow_ne_zero, ne_of_gt dyadicRatio_pos, hd]
  ring

section CommonEigenspace

variable (S : ℕ → Y →L[𝕜] Y) (T : H →L[𝕜] Y) (a : ℝ) (ha : 0 ≤ a)
  (heigen : ∀ n x, S n (T x) = (dyadicEigenvalue a n : 𝕜) • T x)

include ha heigen

theorem analysisCoordinate_eigen (n : ℕ) (x : H) :
    analysisCoordinate S n (T x) = (intrinsicEigenCoefficient a n : 𝕜) • T x := by
  cases n with
  | zero => simp [analysisCoordinate, intrinsicEigenCoefficient]
  | succ n =>
    simp only [analysisCoordinate, smul_apply, sub_apply, ContinuousLinearMap.id_apply, heigen]
    rw [intrinsicEigenCoefficient_eq_weighted_defect a ha n,
      RCLike.ofReal_mul, RCLike.ofReal_sub, RCLike.ofReal_one, mul_smul, sub_smul, one_smul]

theorem dyadic_coordinates_summable (x : H) :
    Summable (fun n => ‖analysisCoordinate S n (T x)‖) :=
  scalar_coordinates_summable (analysisCoordinate S) T
    (fun n => (intrinsicEigenCoefficient a n : 𝕜))
    (intrinsicEigenCoefficient_norm_summable a ha) (analysisCoordinate_eigen S T a ha heigen) x

theorem dyadic_coordinates_tsum_le (x : H) :
    (∑' n, ‖analysisCoordinate S n (T x)‖) ≤ eigenNormBound a * ‖T x‖ := by
  rw [scalar_coordinates_tsum (analysisCoordinate S) T
    (fun n => (intrinsicEigenCoefficient a n : 𝕜)) (analysisCoordinate_eigen S T a ha heigen)]
  exact mul_le_mul_of_nonneg_right (intrinsicEigenCoefficient_norm_tsum_le a ha) (norm_nonneg _)

theorem dyadic_coordinates_bound (x : H) :
    (∑' n, ‖analysisCoordinate S n (T x)‖) ≤ (eigenNormBound a * ‖T‖) * ‖x‖ :=
  (dyadic_coordinates_tsum_le S T a ha heigen x).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (T.le_opNorm x) (eigenNormBound_nonneg a ha))

/-- The bounded lift of a common eigenspace into the actual intrinsic graph. -/
def commonEigenvectorLift : H →L[𝕜] Space (analysisCoordinate S) :=
  lift (analysisCoordinate S) rfl T (dyadic_coordinates_summable S T a ha heigen)
    (eigenNormBound a * ‖T‖) (dyadic_coordinates_bound S T a ha heigen)

@[simp]
theorem evalZero_commonEigenvectorLift (x : H) :
    evalZero (analysisCoordinate S) (commonEigenvectorLift S T a ha heigen x) = T x :=
  evalZero_lift _ _ _ _ _ _ x

theorem commonEigenvectorLift_norm_bounds (x : H) :
    ‖T x‖ ≤ ‖commonEigenvectorLift S T a ha heigen x‖ ∧
      ‖commonEigenvectorLift S T a ha heigen x‖ ≤ eigenNormBound a * ‖T x‖ := by
  constructor
  · exact norm_base_le_lift _ _ _ _ _ _ x
  · rw [norm_eq_tsum_operators, evalZero_commonEigenvectorLift]
    exact dyadic_coordinates_tsum_le S T a ha heigen x

/-- A common eigenspace that is a Banach-space copy in the base space remains
a closed Banach-space copy with the intrinsic norm. -/
theorem containsIsomorphicCopy_of_common_eigenspace [CompleteSpace H] [CompleteSpace Y]
    (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    PL1.ContainsIsomorphicCopy 𝕜 H (Space (analysisCoordinate S)) :=
  containsIsomorphicCopy_of_coordinate_bound (analysisCoordinate S) rfl T
    (dyadic_coordinates_summable S T a ha heigen)
    (eigenNormBound a * ‖T‖) (dyadic_coordinates_bound S T a ha heigen) K hT

end CommonEigenspace

/-- The intrinsic norm bound for the first-chaos eigenvalue is exactly `2 + √2`. -/
theorem eigenNormBound_one : eigenNormBound 1 = 2 + Real.sqrt 2 := by
  unfold eigenNormBound
  field_simp [ne_of_gt one_sub_dyadicRatio_pos]
  rw [dyadicRatio_eq_sqrt_div_two]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- The first-chaos lifting statement needed in Theorem B. -/
theorem containsIsomorphicCopy_of_first_chaos [CompleteSpace H] [CompleteSpace Y]
    (S : ℕ → Y →L[𝕜] Y) (T : H →L[𝕜] Y)
    (heigen : ∀ n x, S n (T x) = (((1 + (dyadicRatio ^ 2) ^ n)⁻¹ : ℝ) : 𝕜) • T x)
    (K : ℝ≥0) (hT : ∀ x, ‖x‖ ≤ K * ‖T x‖) :
    PL1.ContainsIsomorphicCopy 𝕜 H (Space (analysisCoordinate S)) :=
  containsIsomorphicCopy_of_common_eigenspace S T 1 (by norm_num)
    (by simpa [dyadicEigenvalue] using heigen) K hT

/-- The same conclusion using the customary positive lower norm bound. -/
theorem containsIsomorphicCopy_of_common_eigenspace_boundedBelow
    [CompleteSpace H] [CompleteSpace Y]
    (S : ℕ → Y →L[𝕜] Y) (T : H →L[𝕜] Y) (a : ℝ) (ha : 0 ≤ a)
    (heigen : ∀ n x, S n (T x) = (dyadicEigenvalue a n : 𝕜) • T x)
    (b : ℝ) (hb : 0 < b) (hT : ∀ x, b * ‖x‖ ≤ ‖T x‖) :
    PL1.ContainsIsomorphicCopy 𝕜 H (Space (analysisCoordinate S)) := by
  apply containsIsomorphicCopy_of_common_eigenspace S T a ha heigen
    ⟨b⁻¹, inv_nonneg.2 hb.le⟩
  intro x
  change ‖x‖ ≤ b⁻¹ * ‖T x‖
  calc
    ‖x‖ = b⁻¹ * (b * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb), one_mul]
    _ ≤ b⁻¹ * ‖T x‖ := mul_le_mul_of_nonneg_left (hT x) (inv_nonneg.2 hb.le)

end PL1.EigenvectorEmbedding
