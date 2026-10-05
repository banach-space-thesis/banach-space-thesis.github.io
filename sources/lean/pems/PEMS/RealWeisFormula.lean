import PEMS.PositiveWeisFormula
import PEMS.L1WeakNoncompactnessModulus
import ThesisCommon.Analysis.IntegralKernelTruncationModulus
import ThesisCommon.Analysis.BandProjectionModulus

/-! The real signed Weis norm formula on compact standard measure spaces.
The positive formula is transferred by the actual operator modulus. Kernel
uniqueness identifies its canonical density truncations with truncations of
any supplied kernel of the actual integral part. Best attainment is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter ThesisCommon
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace PEMS

section KernelCongruence
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]
variable {k h : X × Y → ℝ} {K H : LOne ℝ μ →L[ℝ] LOne ℝ ν}

theorem truncatedOperator_eq_of_kernel_ae
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H)
    (heq : k =ᵐ[μ.prod ν] h) (r : ℝ) :
    hk.truncatedOperator r = hh.truncatedOperator r := by
  apply ((hk.truncatedOperator_represents r).congr_ae
    (measurable_truncatedKernel hh.measurable r) ?_).unique (hh.truncatedOperator_represents r)
  filter_upwards [heq] with z hz
  simp only [truncatedKernel, Set.indicator_apply, Set.mem_setOf_eq, hz]

theorem truncatedOperator_eq_of_same_operator
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h K) (r : ℝ) :
    hk.truncatedOperator r = hh.truncatedOperator r :=
  truncatedOperator_eq_of_kernel_ae hk hh (hk.kernel_unique hh) r

end KernelCongruence

section Standard
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem real_standard_truncation_inf_le_localized
    {k : X × Y → ℝ} (S K : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) ≤
      localizedWeakNoncompactness (S + K) := by
  have hPK : integralBandProjection (S + K) = K := by
    rw [map_add, (integralBandProjection_eq_zero_iff S).mpr hS,
      integralBandProjection_eq_self ⟨k, hk⟩, zero_add]
  have hPabs : integralBandProjection |S + K| = |K| := by
    have h := integralOperatorOrderClosedIdeal.bandProjection_abs (S + K)
    change integralBandProjection |S + K| = |integralBandProjection (S + K)| at h
    exact h.trans (congrArg abs hPK)
  have hres : |S + K| - integralBandProjection |S + K| = |S| := by
    rw [hPabs, singular_integral_abs_add hS ⟨k, hk⟩, add_sub_cancel_right]
  obtain ⟨κ, hκ, _, hrepr, hρ⟩ := exists_positive_operator_kernel_parts |S + K| (abs_nonneg _)
  letI := hκ
  have hρK : IsIntegralKernel (kernelRealDensity κ ν) |K| := hPabs ▸ hρ
  have htail : ∀ r : ℝ, hρ.truncatedOperator r = hk.abs.truncatedOperator r := fun r =>
    truncatedOperator_eq_of_kernel_ae hρ hk.abs (hρK.kernel_unique hk.abs) r
  have hnorm : ∀ n : ℕ,
      ‖|S + K| - integralBandProjection |S + K| + hρ.truncatedOperator n‖ =
        ‖S + hk.truncatedOperator n‖ := by
    intro n
    rw [hres, htail, ← hk.abs_truncatedOperator,
      ← singular_integral_abs_add hS ⟨_, hk.truncatedOperator_represents n⟩,
      norm_abs_lOneOperator]
  have hle := positive_truncation_inf_le_alphaTheta |S + K| (abs_nonneg _) κ hrepr hρ
  simp_rw [hnorm] at hle
  rwa [← localizedWeakNoncompactness_eq_alphaTheta_univ,
    localizedWeakNoncompactness_abs] at hle

theorem real_standard_weis_norm_formula
    {k : X × Y → ℝ} (S K : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) =
      sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) := by
  have hlo := localizedWeakNoncompactness_le_weakEssentialNorm (S + K)
  have hmid := real_standard_truncation_inf_le_localized S K hS hk
  have hu : weakEssentialNorm (S + K) ≤
      sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) :=
    weakEssentialNorm_le_truncation_inf hk S
  exact ⟨le_antisymm (hu.trans hmid) hlo, le_antisymm hu (hmid.trans hlo)⟩

theorem real_standard_weis_norm_formula_of_decomposition
    {k : X × Y → ℝ} (T S K : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (hT : T = S + K) (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm T = localizedWeakNoncompactness T ∧
    weakEssentialNorm T = sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) := by
  subst T
  exact real_standard_weis_norm_formula S K hS hk

theorem weakEssentialNorm_eq_localized_real_standard
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  obtain ⟨k, hk⟩ := integralBandProjection_isIntegral T
  have h := (real_standard_weis_norm_formula (T - integralBandProjection T)
    (integralBandProjection T) (integralBandProjection_residual_singular T) hk).1
  simpa only [sub_add_cancel] using h

theorem weakEssentialNorm_abs_real_standard
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : weakEssentialNorm |T| = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_standard, localizedWeakNoncompactness_abs,
    weakEssentialNorm_eq_localized_real_standard]

end Standard
end PEMS
