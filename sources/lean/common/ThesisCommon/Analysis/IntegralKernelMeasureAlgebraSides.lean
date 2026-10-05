import ThesisCommon.Analysis.IntegralKernelMeasureAlgebra
import ThesisCommon.Analysis.MeasureAlgebraIdentity
import ThesisCommon.Analysis.MeasureAlgebraIntegral

/-! The input and output formulations of the explicit kernel/truncation
transport in PEMS Lemma 4.3. No countability is imposed on a replacement space. -/
noncomputable section
open MeasureTheory MeasurableSpace

namespace ThesisCommon
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
variable [CountablyGenerated X] [CountablyGenerated Y]

theorem IsIntegralKernel.exists_measureAlgebra_precomp (Φ : MeasureAlgebraIso μ' μ)
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K) :
    ∃ (h : X' × Y → ℝ)
      (hh : IsIntegralKernel h (K.comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap)),
      ∀ r : ℝ, hh.truncatedOperator r =
        (hk.truncatedOperator r).comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap := by
  have hop (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
      operatorTransport Φ.symm.lOneEquiv (MeasureAlgebraIso.refl ν).lOneEquiv T =
        T.comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap := by
    ext f
    rw [operatorTransport_apply, MeasureAlgebraIso.refl_lOneEquiv_apply, Φ.lOneEquiv_symm_eq]
    simp
  obtain ⟨h, hh, htr⟩ := hk.exists_measureAlgebra_transport Φ.symm (MeasureAlgebraIso.refl ν)
  simp_rw [hop] at hh htr
  exact ⟨h, hh, htr⟩

theorem IsIntegralKernel.exists_measureAlgebra_postcomp (Ψ : MeasureAlgebraIso ν ν')
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K) :
    ∃ (h : X × Y' → ℝ)
      (hh : IsIntegralKernel h (Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp K)),
      ∀ r : ℝ, hh.truncatedOperator r =
        Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp (hk.truncatedOperator r) := by
  have hop (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
      operatorTransport (MeasureAlgebraIso.refl μ).lOneEquiv Ψ.lOneEquiv T =
        Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp T := by
    ext f
    rw [operatorTransport_apply, MeasureAlgebraIso.refl_lOneEquiv]
    rfl
  obtain ⟨h, hh, htr⟩ := hk.exists_measureAlgebra_transport (MeasureAlgebraIso.refl μ) Ψ
  simp_rw [hop] at hh htr
  exact ⟨h, hh, htr⟩

end ThesisCommon
