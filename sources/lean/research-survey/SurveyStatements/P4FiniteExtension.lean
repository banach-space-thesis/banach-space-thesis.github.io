import SurveyStatements.P4FiniteStabilization
import SurveyStatements.P4FiniteSchauder
import SurveyStatements.P4FiniteReflexivity

/-! Uniform finite basis extensions, including the zero-dimensional case. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Module

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

structure FiniteBasisExtension (𝕜 : Type u) [RCLike 𝕜]
    (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  Carrier : Type v
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace 𝕜 Carrier]
  [finiteDimensional : FiniteDimensional 𝕜 Carrier]
  embedding : E →L[𝕜] Carrier
  retraction : Carrier →L[𝕜] E
  retraction_comp_embedding : retraction.comp embedding = ContinuousLinearMap.id 𝕜 E
  norm_embedding_le : ‖embedding‖ ≤ 2
  norm_retraction_le : ‖retraction‖ ≤ 1
  length : ℕ
  basis : Basis (Fin length) 𝕜 Carrier
  norm_prefix_le : ∀ k : Fin (length + 1), ‖finiteBasisPrefix basis k‖ ≤ 1

attribute [instance] FiniteBasisExtension.normedAddCommGroup
  FiniteBasisExtension.normedSpace FiniteBasisExtension.finiteDimensional

theorem exists_finiteBasisExtension [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    [FiniteDimensional 𝕜 E] : Nonempty (FiniteBasisExtension 𝕜 E) := by
  classical
  by_cases hzero : Module.finrank 𝕜 E = 0
  · let b : Basis (Fin 0) 𝕜 E := Module.finBasisOfFinrankEq 𝕜 E hzero
    refine ⟨{ Carrier := E
              embedding := ContinuousLinearMap.id 𝕜 E
              retraction := ContinuousLinearMap.id 𝕜 E
              retraction_comp_embedding := by ext x; rfl
              norm_embedding_le := ContinuousLinearMap.norm_id_le.trans (by norm_num)
              norm_retraction_le := ContinuousLinearMap.norm_id_le
              length := 0
              basis := b
              norm_prefix_le := ?_ }⟩
    intro k
    simp [finiteBasisPrefix]
  · let b := Module.finBasis 𝕜 E
    have hN : 0 < Module.finrank 𝕜 E := Nat.pos_of_ne_zero hzero
    obtain ⟨m, hm, hbound, hcomp, hJ, hQ, hpref⟩ := exists_repeatedFrame_extension b hN
    exact ⟨{ Carrier := RepeatedFrameSpace b m hN
             embedding := repeatedFrameEmbedding b hm hN hbound
             retraction := repeatedFrameRetraction b m hN
             retraction_comp_embedding := hcomp
             norm_embedding_le := hJ
             norm_retraction_le := hQ
             length := m * Module.finrank 𝕜 E
             basis := finitePathBasis (repeatedPathVectors b m hN)
               (fun i => b.ne_zero (periodicFinIndex hN i.val))
             norm_prefix_le := hpref }⟩

namespace FiniteBasisExtension

variable (G : FiniteBasisExtension 𝕜 E)

theorem schauderBasis : HasSchauderBasis 𝕜 G.Carrier :=
  ⟨Set.Iio G.length, finiteBasisSequence G.basis, finiteBasis_isSchauder G.basis⟩

theorem reflexive : IsReflexiveNormedSpace 𝕜 G.Carrier := finiteDimensional_reflexive

abbrev Complement := LinearMap.ker G.retraction.toLinearMap

instance : FiniteDimensional 𝕜 G.Complement := inferInstance

theorem complement_reflexive : IsReflexiveNormedSpace 𝕜 G.Complement :=
  finiteDimensional_reflexive

end FiniteBasisExtension

end SurveyStatements.P4
