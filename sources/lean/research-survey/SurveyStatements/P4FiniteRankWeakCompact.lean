import SurveyStatements.P4FiniteReflexivity
import SurveyStatements.P4Approximation

/-! Actual finite-rank operators are weakly compact, and the bidual criterion
is closed under the pointwise norm limits used in the bridge. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Filter Topology

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem HasFiniteRank.weaklyCompact {T : X →L[𝕜] Y} (hT : HasFiniteRank 𝕜 T) :
    IsWeaklyCompactOperator 𝕜 T := by
  let F := LinearMap.range T.toLinearMap
  letI : FiniteDimensional 𝕜 F := hT
  let Q : X →L[𝕜] F := T.codRestrict F (fun x => ⟨x, rfl⟩)
  have hId : IsWeaklyCompactOperator 𝕜 (ContinuousLinearMap.id 𝕜 F) :=
    reflexive_iff_weaklyCompact_id.mp finiteDimensional_reflexive
  have h := (hId.comp_right Q).comp_left F.subtypeL
  have heq : F.subtypeL.comp ((ContinuousLinearMap.id 𝕜 F).comp Q) = T := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [heq] at h
  exact h

theorem weaklyCompact_of_finiteRank_bidual_tendsto [CompleteSpace Y]
    (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y) (hA : ∀ n, HasFiniteRank 𝕜 (A n))
    (hbidual : ∀ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
      Tendsto (fun n => bidualMap (A n) ξ) atTop (𝓝 (bidualMap T ξ))) :
    IsWeaklyCompactOperator 𝕜 T := by
  apply weaklyCompact_of_bidual_mem_image
  intro ξ
  exact (isClosed_bidualImage (𝕜 := 𝕜) (F := Y)).mem_of_tendsto (hbidual ξ)
    (Eventually.of_forall fun n => (hA n).weaklyCompact.bidual_mem_image ξ)

end SurveyStatements.P4
