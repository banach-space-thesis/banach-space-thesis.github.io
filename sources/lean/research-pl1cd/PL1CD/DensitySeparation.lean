import PL1CD.FiniteExpectations
import PL1.KernelTranslations
import PL1.SpikeSeparation

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace PL1CD.FiniteExpectations

open PL1.Walsh PL1.FiniteCoordinateKernels PL1.ScalarRealification

theorem convolution_kernel_empty (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν]
    (x : PL1.Walsh.Group) :
    convolutionL1 (𝕜 := ℝ) ν (kernelL1 ∅ x) = kernelL1 ∅ x := by
  simp [kernelL1_eq_sum, convolutionL1_character, coefficient]

theorem norm_density_sub_one_ge (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (x : PL1.Walsh.Group) (B : Set PL1.Walsh.Group)
    (hBm : MeasurableSet B) (hB : DependsOn S B) :
    2 * (ν.real B - haar.real B) ≤
      ‖convolutionL1 (𝕜 := ℝ) ν (kernelL1 S x - kernelL1 ∅ x)‖ := by
  let q := translatedDensity ν S x
  let C := translatedSet B x
  have hqm : Integrable (fun y => q y) haar :=
    q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hq0 : ∀ᵐ y ∂haar, 0 ≤ q y :=
    ae_of_all _ (translatedDensity_nonneg ν S x)
  have hq1 : ∫ y, q y ∂haar = 1 := integral_translatedDensity ν S x
  have hCm : MeasurableSet C := measurableSet_translatedSet hBm x
  have hmass : ∫ y in C, q y ∂haar = ν.real B := setIntegral_translatedDensity ν S hBm hB x
  have hmeasure : haar.real C = haar.real B := by
    exact congrArg ENNReal.toReal (measure_translatedSet hBm x)
  have hbound := PL1.SpikeSeparation.split_lower_bound hqm hq0 hq1 C hCm (-1 : ℝ) 1
  simp only [Real.norm_eq_abs, abs_neg, abs_one, mul_one, smul_eq_mul] at hbound
  rw [hmass, hmeasure] at hbound
  have heq : ‖convolutionL1 (𝕜 := ℝ) ν (kernelL1 S x - kernelL1 ∅ x)‖ =
      ∫ y, ‖(-1 : ℝ) + q y * 1‖ ∂haar := by
    rw [map_sub, convolution_kernel_empty, ← translatedDensity_eq_convolution,
      L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (ContinuousMap.toLp 1 haar ℝ q) (kernelL1 ∅ x),
      ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar q,
      coeFn_kernelL1 ∅ x] with y hsub hq hk
    rw [hsub, Pi.sub_apply, hq, hk]
    simp [PL1.FiniteCoordinateKernels.kernel_apply, sub_eq_add_neg, add_comm]
  rw [heq]
  simp only [mul_one, Real.norm_eq_abs]
  linarith

variable (𝕜 : Type*) [RCLike 𝕜]

theorem norm_reL1_le (f : Lp 𝕜 1 haar) : ‖reL1 𝕜 f‖ ≤ ‖f‖ := by
  have h : ‖reL1 𝕜‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_compLpL_le (@RCLike.reCLM 𝕜 _)).trans
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa only [RCLike.reCLM_apply, one_mul] using RCLike.norm_re_le_norm z
  exact ((reL1 𝕜).le_opNorm f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg f))

theorem norm_scalar_density_sub_one_ge (ν : Measure PL1.Walsh.Group)
    [IsProbabilityMeasure ν] (S : Finset ℕ) (x : PL1.Walsh.Group)
    (B : Set PL1.Walsh.Group) (hBm : MeasurableSet B) (hB : DependsOn S B) :
    2 * (ν.real B - haar.real B) ≤
      ‖convolutionL1 (𝕜 := 𝕜) ν (kernel 𝕜 S x - kernel 𝕜 ∅ x)‖ := by
  have hre : reL1 𝕜 (convolutionL1 ν (kernel 𝕜 S x - kernel 𝕜 ∅ x)) =
      convolutionL1 (𝕜 := ℝ) ν (kernelL1 S x - kernelL1 ∅ x) := by
    change reL1 𝕜 (convolutionL1 ν
      (ofRealL1 𝕜 (kernelL1 S x) - ofRealL1 𝕜 (kernelL1 ∅ x))) = _
    rw [← map_sub]
    exact DFunLike.congr_fun (reL1_convolution_ofRealL1 𝕜 ν) _
  exact (norm_density_sub_one_ge ν S x B hBm hB).trans
    (by rw [← hre]; exact norm_reL1_le 𝕜 _)

theorem norm_increment_ge_event_gap (S : Finset ℕ) (m n : ℕ)
    (hSn : S ⊆ Finset.range n) (hSm : Disjoint S (Finset.range m))
    (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν] (x : PL1.Walsh.Group)
    (B : Set PL1.Walsh.Group) (hBm : MeasurableSet B) (hB : DependsOn S B) :
    2 * (ν.real B - haar.real B) ≤
      ‖convolutionL1 (𝕜 := 𝕜) ν
        (PL1.ExplicitMartingale.kernelL1 𝕜 n x - PL1.ExplicitMartingale.kernelL1 𝕜 m x)‖ :=
  (norm_scalar_density_sub_one_ge 𝕜 ν S x B hBm hB).trans
    (norm_project_increment_le 𝕜 S m n hSn hSm ν x)

end PL1CD.FiniteExpectations
