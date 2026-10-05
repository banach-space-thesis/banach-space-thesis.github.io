import PEMS.SigmaMeasureStrictLocalizable
import ThesisCommon.Analysis.SigmaL1Order
import ThesisCommon.Analysis.ALFiniteL1FamilyRepresentation
import ThesisCommon.Analysis.ComplexALRepresentationExtension
import ThesisCommon.Analysis.RealBanachLatticeCoordinates

/-! Constructive Kakutani representation for the paper's intrinsic real and
complex AL spaces. The representing measure is an actual coproduct of finite
fragment measures and satisfies the exact strict-localizability definition. -/
noncomputable section
universe u
open Set MeasureTheory ThesisCommon
namespace PEMS

theorem exists_ordered_lOne_representation_of_real_AL
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [HasSolidNorm E] [CompleteSpace E]
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖) :
    ∃ (X : Type u) (m : MeasurableSpace X),
      ∃ μ : @Measure X m, StrictlyLocalizable μ ∧
        ∃ e : E ≃ₗᵢ[ℝ] Lp ℝ 1 μ, ∀ x, 0 ≤ e x ↔ 0 ≤ x := by
  obtain ⟨I, X, m, μ, hfinite, hnonempty, d, hd⟩ := exists_ordered_lp_finite_L1_of_AL hAL
  letI := m
  letI := hfinite
  letI := hnonempty
  let e := d.trans (sigmaL1PartitionEquiv μ).symm
  refine ⟨Sigma X, inferInstance, sigmaMeasure μ, sigmaMeasure_strictlyLocalizable μ, e, ?_⟩
  intro x
  rw [← sigmaL1PartitionEquiv_nonneg μ]
  change (∀ i, 0 ≤ sigmaL1PartitionEquiv μ ((sigmaL1PartitionEquiv μ).symm (d x)) i) ↔ 0 ≤ x
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (hd x).symm

theorem exists_lOne_representation_of_real_isAL
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hAL : IsALSpace ℝ E) :
    ∃ (X : Type u) (m : MeasurableSpace X),
      ∃ μ : @Measure X m, StrictlyLocalizable μ ∧ Nonempty (E ≃ₗᵢ[ℝ] Lp ℝ 1 μ) := by
  obtain ⟨B, hB⟩ := hAL
  letI : CompleteSpace B.realForm := B.closed_realForm.isComplete.completeSpace_coe
  obtain ⟨X, m, μ, hμ, e, _⟩ := exists_ordered_lOne_representation_of_real_AL hB
  letI := m
  exact ⟨X, m, μ, hμ, ⟨B.realFormLinearIsometryEquiv.symm.trans e⟩⟩

theorem exists_lOne_representation_of_complex_AL_model
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (B : BanachLatticeModel ℂ E)
    (hB : ∀ x y : B.realForm, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖) :
    ∃ (X : Type u) (m : MeasurableSpace X),
      ∃ μ : @Measure X m, StrictlyLocalizable μ ∧
        ∃ (eR : B.realForm ≃ₗᵢ[ℝ] Lp ℝ 1 μ) (eC : E ≃ₗᵢ[ℂ] Lp ℂ 1 μ),
          (∀ x, 0 ≤ eR x ↔ 0 ≤ x) ∧
          ∀ z, complexL1Modulus (eC z) = eR (B.modulus z) := by
  letI : CompleteSpace B.realForm := B.closed_realForm.isComplete.completeSpace_coe
  obtain ⟨X, m, μ, hμ, eR, heR⟩ := exists_ordered_lOne_representation_of_real_AL hB
  letI := m
  exact ⟨X, m, μ, hμ, eR, B.complexL1RepresentationEquiv eR heR, heR,
    B.complexL1RepresentationEquiv_modulus eR heR⟩

theorem exists_lOne_representation_of_complex_isAL
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (hAL : IsALSpace ℂ E) :
    ∃ (X : Type u) (m : MeasurableSpace X),
      ∃ μ : @Measure X m, StrictlyLocalizable μ ∧ Nonempty (E ≃ₗᵢ[ℂ] Lp ℂ 1 μ) := by
  obtain ⟨B, hB⟩ := hAL
  obtain ⟨X, m, μ, hμ, _, eC, _, _⟩ := exists_lOne_representation_of_complex_AL_model B hB
  exact ⟨X, m, μ, hμ, ⟨eC⟩⟩

end PEMS
