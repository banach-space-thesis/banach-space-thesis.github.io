import SurveyStatements.P4LpDualApproximation
import SurveyStatements.P4DFJPWeakInclusion

/-!
# Dense adjoint restriction for the actual DFJP inclusion

Hahn--Banach extends each functional on the closed diagonal to the ℓ² sum.
Finite coordinate restrictions converge in norm and, on the diagonal, each
restriction is an actual ambient-space functional.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option synthInstance.maxSize 2048

open Set Filter Topology
open scoped ENNReal

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E)

def ambientDualTruncation (φ : StrongDual 𝕜 (DFJPSum D)) (s : Finset ℤ) : StrongDual 𝕜 E :=
  ∑ j ∈ s, (lp2DualCoordinate φ j).comp
    (DFJPScale.continuousLinearEquiv D j).symm.toContinuousLinearMap

lemma adjoint_ambientDualTruncation (φ : StrongDual 𝕜 (DFJPSum D)) (s : Finset ℤ) :
    banachAdjoint (inclusion D) (ambientDualTruncation D φ s) =
      (lp2DualTruncation φ s).comp (dfjpDiagonal D).subtypeL := by
  ext f
  simp only [banachAdjoint_apply, ambientDualTruncation, lp2DualTruncation,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change (DFJPScale.continuousLinearEquiv D j).symm (inclusion D f) = f.val j
  rw [← coordinate_eq D f j]
  exact (DFJPScale.continuousLinearEquiv D j).symm_apply_apply (f.val j)

/-- Every continuous functional on the interpolation space is a norm limit
of actual restrictions of ambient continuous functionals. -/
theorem adjoint_inclusion_denseRange : DenseRange (banachAdjoint (inclusion D)) := by
  intro φ
  obtain ⟨ψ, hψ, _⟩ := exists_extension_norm_eq (dfjpDiagonal D) φ
  have heq : ψ.comp (dfjpDiagonal D).subtypeL = φ := by
    ext f
    exact hψ f
  have ht : Tendsto
      (fun s : Finset ℤ => banachAdjoint (inclusion D) (ambientDualTruncation D ψ s))
      atTop (𝓝 φ) := by
    simp only [adjoint_ambientDualTruncation]
    rw [← heq]
    exact (((ContinuousLinearMap.compL 𝕜 (DFJPSpace D) (DFJPSum D) 𝕜).flip
      (dfjpDiagonal D).subtypeL).continuous.tendsto ψ).comp (tendsto_lp2DualTruncation ψ)
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun s =>
    ⟨ambientDualTruncation D ψ s, rfl⟩)

theorem bidual_inclusion_injective : Function.Injective (bidualMap (inclusion D)) := by
  intro ξ η h
  apply ContinuousLinearMap.ext
  intro φ
  have heq : ∀ ψ : StrongDual 𝕜 E,
      ξ (banachAdjoint (inclusion D) ψ) = η (banachAdjoint (inclusion D) ψ) := by
    intro ψ
    exact congrArg (fun q => q ψ) h
  exact congr_fun ((adjoint_inclusion_denseRange D).equalizer ξ.continuous η.continuous
    (funext heq)) φ

end DFJPSpace

end SurveyStatements.P4
