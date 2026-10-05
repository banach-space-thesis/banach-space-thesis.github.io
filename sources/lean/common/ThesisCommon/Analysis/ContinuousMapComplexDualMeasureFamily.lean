import ThesisCommon.Analysis.ContinuousMapRealDualMeasureFamily
import ThesisCommon.Analysis.ContinuousMapComplexDualAL
import ThesisCommon.Analysis.ComplexALRepresentationExtension
import ThesisCommon.Analysis.SigmaL1Order

/-! The complex continuous-map dual is isometric to an ell-one family of
complex L1 spaces of actual finite Borel measures on the original K.
The construction extends the proved real representation through the actual
real form of the complex dual and the genuine measure coproduct. -/
noncomputable section
universe u
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]

set_option maxHeartbeats 1000000 in
theorem exists_continuousMapComplexDual_measure_family :
    ∃ (I : Type u) (μ : I → Measure K), (∀ i, IsFiniteMeasure (μ i)) ∧
      Nonempty ((C(K, ℂ) →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun i => Lp ℂ 1 (μ i)) 1) := by
  obtain ⟨I, μ, hμ, d, hd⟩ := exists_ordered_continuousMapDual_measure_family (K := K)
  let r : (C(K, ℝ) →L[ℝ] ℝ) ≃ₗᵢ[ℝ] Lp ℝ 1 (sigmaMeasure μ) :=
    d.trans (sigmaL1PartitionEquiv (𝕜 := ℝ) μ).symm
  have hr (φ : C(K, ℝ) →L[ℝ] ℝ) : 0 ≤ r φ ↔ 0 ≤ φ := by
    rw [← sigmaL1PartitionEquiv_nonneg μ]
    change (∀ i, 0 ≤ sigmaL1PartitionEquiv μ ((sigmaL1PartitionEquiv μ).symm (d φ)) i) ↔ _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (hd φ).symm
  let B := continuousMapComplexDualBanachLatticeModel (K := K)
  let b : B.realForm ≃ₗᵢ[ℝ] Lp ℝ 1 (sigmaMeasure μ) :=
    (continuousMapDualRealFormEquiv (K := K)).trans r
  have hb (φ : B.realForm) : 0 ≤ b φ ↔ 0 ≤ φ := by
    change 0 ≤ r (continuousMapDualRealFormEquiv φ) ↔ _
    rw [hr]
    rfl
  exact ⟨I, μ, hμ, ⟨(B.complexL1RepresentationEquiv b hb).trans
    (sigmaL1PartitionEquiv (𝕜 := ℂ) μ)⟩⟩

end ThesisCommon
