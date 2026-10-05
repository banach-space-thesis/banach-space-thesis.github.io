import ThesisCommon.Analysis.ClopenOperatorMeasureOrder
import ThesisCommon.Analysis.KernelMeasureColumns
import ThesisCommon.Analysis.IntegralOperatorBand

/-! The integral band projection of a positive real L1 operator is exactly
the absolutely continuous part of its actual product measure. The RN
density's column estimate is proved from the marginal bound, and measure
singularity is connected to lattice singularity through operator order. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

theorem IsIntegralOperator.clopenOperatorMeasure_absolutelyContinuous
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hI : IsIntegralOperator S) (hS : 0 ≤ S) :
    clopenOperatorMeasure S hS ≪ μ.prod ν := by
  obtain ⟨k, hk⟩ := hI
  rw [hk.clopenOperatorMeasure_eq hS]
  exact withDensity_absolutelyContinuous _ _

theorem isSingularOperator_of_clopenOperatorMeasure_mutuallySingular
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (hms : clopenOperatorMeasure S hS ⟂ₘ μ.prod ν) : IsSingularOperator S := by
  let P := integralBandProjection (μ := μ) (ν := ν) S
  have hP : 0 ≤ P := integralBandProjection_nonneg S hS
  have hPI : IsIntegralOperator P := integralBandProjection_isIntegral S
  have hPS : P ≤ S := integralBandProjection_le_id S hS
  have hmsP : clopenOperatorMeasure P hP ⟂ₘ μ.prod ν :=
    hms.mono (clopenOperatorMeasure_mono P S hP hS hPS) le_rfl
  have hzero : clopenOperatorMeasure P hP = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
      (hPI.clopenOperatorMeasure_absolutelyContinuous hP) hmsP
  exact (integralBandProjection_eq_zero_iff S).mp
    ((clopenOperatorMeasure_eq_zero_iff P hP).mp hzero)

theorem exists_integralOperator_clopenMeasure_acPart
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    ∃ K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, ∃ hK : 0 ≤ K,
      IsIntegralOperator K ∧ K ≤ S ∧
      clopenOperatorMeasure K hK =
        (μ.prod ν).withDensity ((clopenOperatorMeasure S hS).rnDeriv (μ.prod ν)) := by
  let ρ := clopenOperatorMeasure S hS
  obtain ⟨k, hkm, hkpos, hki, hrepr⟩ := exists_real_density_acPart (μ := μ) (ν := ν) ρ
  have hdom : integralKernelMeasure μ ν k ≤ ρ := by
    rw [hrepr]
    exact Measure.withDensity_rnDeriv_le ρ (μ.prod ν)
  have hfst : (integralKernelMeasure μ ν k).map Prod.fst ≤ ENNReal.ofReal ‖S‖ • μ :=
    (Measure.map_mono hdom measurable_fst).trans (clopenOperatorMeasure_fst_le S hS)
  have hbound := hasKernelBound_of_kernelMeasure_fst_le hki hkpos (norm_nonneg S) hfst
  let K := integralKernelOperator hkm hbound
  have hk : IsIntegralKernel k K := isIntegralKernel_integralKernelOperator hkm hbound
  have hK : 0 ≤ K := hk.positive_of_nonneg_ae (Eventually.of_forall hkpos)
  have hM : clopenOperatorMeasure K hK = integralKernelMeasure μ ν k := hk.clopenOperatorMeasure_eq hK
  refine ⟨K, hK, ⟨k, hk⟩, ?_, hM.trans hrepr⟩
  apply (clopenOperatorMeasure_le_iff K S hK hS).mp
  rw [hM]
  exact hdom

theorem clopenOperatorMeasure_residual_eq_singularPart
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hK : 0 ≤ K) (hKS : K ≤ S)
    (hM : clopenOperatorMeasure K hK =
      (μ.prod ν).withDensity ((clopenOperatorMeasure S hS).rnDeriv (μ.prod ν))) :
    clopenOperatorMeasure (S - K) (sub_nonneg.mpr hKS) =
      (clopenOperatorMeasure S hS).singularPart (μ.prod ν) := by
  apply (Measure.add_left_inj (clopenOperatorMeasure K hK) _ _).mp
  calc
    clopenOperatorMeasure (S - K) (sub_nonneg.mpr hKS) + clopenOperatorMeasure K hK =
        clopenOperatorMeasure S hS := by
      simpa only [sub_add_cancel] using
        (clopenOperatorMeasure_add (S - K) K (sub_nonneg.mpr hKS) hK).symm
    _ = (clopenOperatorMeasure S hS).singularPart (μ.prod ν) + clopenOperatorMeasure K hK := by
      rw [hM]
      exact Measure.haveLebesgueDecomposition_add _ _

theorem clopenOperatorMeasure_integralBandProjection
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    clopenOperatorMeasure (integralBandProjection S) (integralBandProjection_nonneg S hS) =
      (μ.prod ν).withDensity ((clopenOperatorMeasure S hS).rnDeriv (μ.prod ν)) := by
  obtain ⟨K, hK, hKI, hKS, hM⟩ := exists_integralOperator_clopenMeasure_acPart S hS
  have hR : 0 ≤ S - K := sub_nonneg.mpr hKS
  have hRM := clopenOperatorMeasure_residual_eq_singularPart S K hS hK hKS hM
  have hRsing : IsSingularOperator (S - K) := by
    apply isSingularOperator_of_clopenOperatorMeasure_mutuallySingular (S - K) hR
    rw [hRM]
    exact Measure.mutuallySingular_singularPart _ _
  have hzero := (integralBandProjection_eq_zero_iff (S - K)).mpr hRsing
  rw [map_sub, integralBandProjection_eq_self hKI] at hzero
  have heq : integralBandProjection S = K := sub_eq_zero.mp hzero
  simpa only [heq] using hM

theorem clopenOperatorMeasure_singularBandPart
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    clopenOperatorMeasure (S - integralBandProjection S)
        (sub_nonneg.mpr (integralBandProjection_le_id S hS)) =
      (clopenOperatorMeasure S hS).singularPart (μ.prod ν) :=
  clopenOperatorMeasure_residual_eq_singularPart S (integralBandProjection S) hS
    (integralBandProjection_nonneg S hS) (integralBandProjection_le_id S hS)
    (clopenOperatorMeasure_integralBandProjection S hS)

theorem isIntegralKernel_rnDeriv_integralBandProjection
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    IsIntegralKernel
      (fun z => ((clopenOperatorMeasure S hS).rnDeriv (μ.prod ν) z).toReal)
      (integralBandProjection S) := by
  obtain ⟨k, hk⟩ := integralBandProjection_isIntegral S
  have hP : 0 ≤ integralBandProjection S := integralBandProjection_nonneg S hS
  have hadd : clopenOperatorMeasure S hS =
      (clopenOperatorMeasure S hS).singularPart (μ.prod ν) +
        (μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z)) := by
    change _ = _ + integralKernelMeasure μ ν k
    rw [← hk.clopenOperatorMeasure_eq hP, clopenOperatorMeasure_integralBandProjection S hS]
    exact Measure.haveLebesgueDecomposition_add _ _
  have hden := Measure.eq_rnDeriv hk.measurable.ennreal_ofReal
    (Measure.mutuallySingular_singularPart (clopenOperatorMeasure S hS) (μ.prod ν)) hadd
  apply hk.congr_ae (Measure.measurable_rnDeriv _ _).ennreal_toReal
  filter_upwards [hden, hk.nonneg_ae_of_positive hP] with z hz hpos
  rw [← hz, ENNReal.toReal_ofReal hpos]

theorem isIntegralOperator_iff_clopenOperatorMeasure_absolutelyContinuous
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    IsIntegralOperator S ↔ clopenOperatorMeasure S hS ≪ μ.prod ν := by
  refine ⟨fun hI => hI.clopenOperatorMeasure_absolutelyContinuous hS, ?_⟩
  intro hAC
  have hM := clopenOperatorMeasure_integralBandProjection S hS
  rw [Measure.withDensity_rnDeriv_eq _ _ hAC] at hM
  have heq := clopenOperatorMeasure_injective (integralBandProjection S) S
    (integralBandProjection_nonneg S hS) hS hM
  rw [← heq]
  exact integralBandProjection_isIntegral S

theorem isSingularOperator_iff_clopenOperatorMeasure_mutuallySingular
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    IsSingularOperator S ↔ clopenOperatorMeasure S hS ⟂ₘ μ.prod ν := by
  refine ⟨?_, isSingularOperator_of_clopenOperatorMeasure_mutuallySingular S hS⟩
  intro hsing
  have hzero := (integralBandProjection_eq_zero_iff S).mpr hsing
  have hM := clopenOperatorMeasure_singularBandPart S hS
  have hM' : clopenOperatorMeasure S hS =
      (clopenOperatorMeasure S hS).singularPart (μ.prod ν) := by
    simpa only [hzero, sub_zero] using hM
  rw [hM']
  exact Measure.mutuallySingular_singularPart _ _

end ThesisCommon
