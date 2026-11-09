import SurveyStatements.P4BlockBasisProjections
import SurveyStatements.P4Lp2Reflexivity
import SurveyStatements.P4ProductReflexivity

/-! A complete reflexive space with a contractive finite decomposition is a
complemented subspace of a complete reflexive space with an actual Schauder basis. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

theorem exists_reflexive_basis_retraction
    (D : ContractiveFiniteDecomposition 𝕜 Z) (hZ : IsReflexiveNormedSpace 𝕜 Z) :
    ∃ V : ReflexiveBanachSpaceWithBasis.{u, v} 𝕜,
      ∃ J : Z →L[𝕜] V.Carrier, ∃ Q : V.Carrier →L[𝕜] Z,
        Q.comp J = ContinuousLinearMap.id 𝕜 Z := by
  classical
  let G : ∀ n, FiniteBasisExtension 𝕜 (D.Block n) :=
    fun n => by
      letI : Module ℝ (D.Block n) := RestrictScalars.module ℝ 𝕜 (D.Block n)
      letI : IsScalarTower ℝ 𝕜 (D.Block n) := RestrictScalars.isScalarTower _ _ _
      letI : NormedSpace ℝ (D.Block n) := NormedSpace.restrictScalars _ 𝕜 _
      exact Classical.choice (exists_finiteBasisExtension (𝕜 := 𝕜) (E := D.Block n))
  letI : ∀ n, CompleteSpace (G n).Complement := fun n => inferInstance
  let V : ReflexiveBanachSpaceWithBasis.{u, v} 𝕜 :=
    { Carrier := BlockBasisSpace D G
      reflexive := reflexive_prod (𝕜 := 𝕜) hZ
        (lp2_reflexive (𝕜 := 𝕜) (E := fun n => (G n).Complement)
          (fun n => (G n).complement_reflexive))
      schauderBasis := blockBasisSpace_hasSchauderBasis D G }
  refine ⟨V, ContinuousLinearMap.inl 𝕜 Z (lp (fun n => (G n).Complement) 2),
    ContinuousLinearMap.fst 𝕜 Z (lp (fun n => (G n).Complement) 2), ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  rfl

end SurveyStatements.P4
