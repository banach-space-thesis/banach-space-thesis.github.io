import SurveyStatements.P4DFJPSpan
import SurveyStatements.P4DFJPContractions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Finite rank of the lifted projections follows from their finite range
on the ambient closed span of the generating set. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

namespace DFJPSpace

theorem contraction_hasFiniteRank (D : DFJPGaugeData 𝕜 E) (T : E →L[𝕜] E)
    (hK : ∀ x ∈ D.carrier, T x ∈ D.carrier) (hT : ‖T‖ ≤ 1)
    (F : Submodule 𝕜 E) [FiniteDimensional 𝕜 F]
    (hF : ∀ x ∈ closure (Submodule.span 𝕜 D.carrier : Set E), T x ∈ F) :
    HasFiniteRank 𝕜 (contraction D T hK hT) := by
  let C := contraction D T hK hT
  have hCF (g : LinearMap.range C.toLinearMap) : inclusion D g.val ∈ F := by
    obtain ⟨f, hf⟩ := g.property
    rw [← hf]
    change inclusion D (contractionLinearMap D T hK hT f) ∈ F
    rw [inclusion_contractionLinearMap]
    exact hF (inclusion D f) (inclusion_mem_closure_span D f)
  let L : LinearMap.range C.toLinearMap →ₗ[𝕜] F :=
    { toFun := fun g => ⟨inclusion D g.val, hCF g⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        exact (inclusion D).map_add f.val g.val
      map_smul' := by
        intro a f
        apply Subtype.ext
        exact (inclusion D).map_smul a f.val }
  have hL : Function.Injective L := by
    intro f g h
    apply Subtype.ext
    apply inclusion_injective D
    exact congrArg (fun q : F => q.val) h
  exact FiniteDimensional.of_injective L hL

end DFJPSpace

end SurveyStatements.P4
