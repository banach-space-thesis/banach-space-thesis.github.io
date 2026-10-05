import PEMS.L1WeakNoncompactness
import ThesisCommon.Analysis.MeasureAlgebraCutTransport

/-! The exact localized weak-noncompactness functional is invariant under
arbitrary finite measure-algebra isomorphisms. Cutoffs and their admissible
measures are transported through actual L1 isometries. There is no point-map,
topology, or countable-generation hypothesis on any of the four spaces. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace PEMS
open ThesisCommon
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
variable (Φ : MeasureAlgebraIso μ μ') (Ψ : MeasureAlgebraIso ν ν')

theorem cutOperatorNorm_measureAlgebraTransport (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (B : Set Y) (hB : MeasurableSet B) :
    cutOperatorNorm (measureAlgebraOperatorEquiv Φ Ψ T) (Ψ.imageSet B hB) =
      cutOperatorNorm T B := by
  rw [cutOperatorNorm_eq _ _ (Ψ.measurableSet_imageSet B hB), cutOperatorNorm_eq _ B hB]
  exact norm_measureAlgebraOperatorEquiv_outputCut Φ Ψ T B hB

theorem smallSetSup_univ_measureAlgebraTransport (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (δ : ℝ) :
    smallSetSup (measureAlgebraOperatorEquiv Φ Ψ T) univ δ = smallSetSup T univ δ := by
  unfold smallSetSup
  congr 1
  ext q
  simp only [mem_setOf_eq, compl_univ, empty_union]
  constructor
  · rintro ⟨B, hB, _, hsmall, heq⟩
    have hc := cutOperatorNorm_measureAlgebraTransport Φ.symm Ψ.symm
      (measureAlgebraOperatorEquiv Φ Ψ T) B hB
    rw [measureAlgebraOperatorEquiv_symm_apply] at hc
    refine ⟨Ψ.symm.imageSet B hB, Ψ.symm.measurableSet_imageSet B hB, subset_univ _, ?_,
      heq.trans hc.symm⟩
    rwa [Ψ.symm.measure_imageSet B hB]
  · rintro ⟨B, hB, _, hsmall, heq⟩
    refine ⟨Ψ.imageSet B hB, Ψ.measurableSet_imageSet B hB, subset_univ _, ?_,
      heq.trans (cutOperatorNorm_measureAlgebraTransport Φ Ψ T B hB).symm⟩
    rwa [Ψ.measure_imageSet B hB]

theorem alphaTheta_univ_measureAlgebraTransport (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    alphaTheta (measureAlgebraOperatorEquiv Φ Ψ T) univ = alphaTheta T univ := by
  simp only [alphaTheta, smallSetSup_univ_measureAlgebraTransport Φ Ψ T]

theorem localizedWeakNoncompactness_measureAlgebraTransport (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    localizedWeakNoncompactness (measureAlgebraOperatorEquiv Φ Ψ T) =
      localizedWeakNoncompactness T := by
  rw [localizedWeakNoncompactness_eq_alphaTheta_univ,
    localizedWeakNoncompactness_eq_alphaTheta_univ, alphaTheta_univ_measureAlgebraTransport]

/-- Transfer the precise norm identity in either direction through any
finite measure-algebra replacement of domain and output. -/
theorem weakEssentialNorm_eq_localized_measureAlgebraTransport_iff
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm (measureAlgebraOperatorEquiv Φ Ψ T) =
      localizedWeakNoncompactness (measureAlgebraOperatorEquiv Φ Ψ T) ↔
        weakEssentialNorm T = localizedWeakNoncompactness T := by
  rw [localizedWeakNoncompactness_measureAlgebraTransport Φ Ψ T]
  change weakEssentialNorm (operatorTransport Φ.lOneEquiv Ψ.lOneEquiv T) = _ ↔ _
  rw [weakEssentialNorm_operatorTransport]

end PEMS
