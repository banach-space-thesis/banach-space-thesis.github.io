import LindenstraussRetraction.MainFromBasis
import LindenstraussRetraction.DirectSumBlockBasis
import LindenstraussRetraction.RenormedBlockBasis
import LindenstraussRetraction.AuxiliaryNoRetraction
import LindenstraussRetraction.ConcreteFDD

/-! The main existence theorem, proved from the explicit constructed space.
The finite-block construction gives W its own bounded Schauder basis; the
proved interval renorming then makes that basis bimonotone. -/

noncomputable section
namespace LindenstraussRetraction

variable (𝕜 : Type) [RCLike 𝕜]
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

def auxiliarySchauderBasis : SchauderBasis 𝕜 (AuxiliarySpace 𝕜) :=
  c0SumPacketSchauderBasis 𝕜 (RenormedSummationSpace 𝕜) (renormedSummationBlockBasisData 𝕜)

theorem auxiliarySchauderBasis_partialSum_bound (N : ℕ) :
    ‖(auxiliarySchauderBasis 𝕜).partialSum N‖ ≤ 3 :=
  norm_c0SumPacketSchauderBasis_partialSum_le 𝕜 (RenormedSummationSpace 𝕜)
    (renormedSummationBlockBasisData 𝕜) N

/-- Theorem `thm:main`, including both whole-bidual consequences for the
same separable Banach space with a bimonotone basis. -/
theorem mainTheorem [TopologicalSpace.SeparableSpace 𝕜] : MainStatement 𝕜 :=
  mainStatement_of_boundedBasis_counterexample (auxiliarySchauderBasis 𝕜)
    3 (by norm_num) (auxiliarySchauderBasis_partialSum_bound 𝕜)
    (no_uniformUnitBallRetraction_auxiliarySpace 𝕜)

theorem mainUnitBallTheorem [TopologicalSpace.SeparableSpace 𝕜] : MainUnitBallStatement 𝕜 := by
  obtain ⟨X,hb,hno,_,_⟩ := mainTheorem 𝕜
  exact ⟨X,hb,hno⟩

theorem concreteAuxiliarySpaceTheorem : ConcreteAuxiliarySpaceStatement 𝕜 :=
  ⟨auxiliary_hasMonotoneFDD 𝕜, no_uniformUnitBallRetraction_auxiliarySpace 𝕜⟩

theorem auxiliarySpaceTheorem [TopologicalSpace.SeparableSpace 𝕜] : AuxiliarySpaceStatement 𝕜 := by
  letI : TopologicalSpace.SeparableSpace (AuxiliarySpace 𝕜) := (auxiliarySchauderBasis 𝕜).separableSpace
  exact ⟨{ Carrier := AuxiliarySpace 𝕜 }, concreteAuxiliarySpaceTheorem 𝕜⟩

/-- The real version of the manuscript's theorem, with no prerequisite hypotheses. -/
theorem main_real : MainStatement ℝ := mainTheorem ℝ

/-- The complex version of the manuscript's theorem, with no prerequisite hypotheses. -/
theorem main_complex : MainStatement ℂ := mainTheorem ℂ

end LindenstraussRetraction
