import SurveyStatements.P4ConvergentHullFiniteRange
import SurveyStatements.P4DFJPFiniteDecomposition
import SurveyStatements.P4TailConvexAdjoint

/-! The genuine bridge from two-sided approximants to a complete reflexive
space with compatible contractive finite-dimensional projections. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

open Set Filter Topology
open scoped OnePoint

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y]

theorem twoSided_reflexive_fdd_factorization
    (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hfinite : ∀ n, HasFiniteRank 𝕜 (A n))
    (hpoint : ∀ x : X, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hbound : ∀ n, ‖A n‖ ≤ C)
    (hbidual : ∀ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
      Tendsto (fun n => bidualMap (A n) ξ) atTop (𝓝 (bidualMap T ξ)))
    (hadjoint : ∀ φ : StrongDual 𝕜 Y,
      Tendsto (fun n => banachAdjoint (A n) φ) atTop (𝓝 (banachAdjoint T φ))) :
    ∃ D : DFJPGaugeData 𝕜 C(OnePoint ℕ, Y),
      IsReflexiveNormedSpace 𝕜 (DFJPSpace D) ∧
      Nonempty (ContractiveFiniteDecomposition 𝕜 (DFJPSpace D)) ∧
      ∃ S : X →L[𝕜] DFJPSpace D, ∃ B : DFJPSpace D →L[𝕜] Y, B.comp S = T := by
  let R := convergentLift A T hpoint hbound
  have hR : IsWeaklyCompactOperator 𝕜 R :=
    convergentLift_weaklyCompact_of_dualDensity A T hfinite hpoint hbound hbidual
      convergentDual_coordinate_span_dense
  have hshrinking : ∀ Φ : StrongDual 𝕜 C(OnePoint ℕ, Y), Tendsto
      (fun n => banachAdjoint R (banachAdjoint (convergentFreeze (𝕜 := 𝕜) (Y := Y) n) Φ))
      atTop (𝓝 (banachAdjoint R Φ)) :=
    convergentLift_shrinking A T hpoint hbound hadjoint convergentDual_coordinate_span_dense
  let L := convergentFreezeSum R
  have hL : IsWeaklyCompactOperator 𝕜 L := convergentFreezeSum_weaklyCompact R hR hshrinking
  let D := operatorGaugeData L
  have hD := operatorGaugeData_weakCompact L hL
  have hunit : ∀ x : X, ‖x‖ ≤ 1 → R x ∈ D.carrier :=
    fun x hx => convergentHull_lift_mem R x hx
  have hRfinite (n : ℕ) : HasFiniteRank 𝕜 ((convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R) :=
    convergentFreeze_lift_finiteRank A T hfinite hpoint hbound n
  let F := convergentHullFiniteRange R
  letI (n : ℕ) : FiniteDimensional 𝕜 (F n) :=
    convergentHullFiniteRange_finiteDimensional R hRfinite n
  have hFDD : Nonempty (ContractiveFiniteDecomposition 𝕜 (DFJPSpace D)) :=
    DFJPSpace.finiteDecomposition_of_contractions D (convergentFreeze (𝕜 := 𝕜) (Y := Y))
      (convergentHull_preserved R) (norm_convergentFreeze_le_one (𝕜 := 𝕜) (Y := Y)) (convergentFreeze_tendsto (𝕜 := 𝕜) (Y := Y))
      (convergentFreeze_comp (𝕜 := 𝕜) (Y := Y)) F (convergentHull_closedSpan_finiteRange R hRfinite)
  let S := DFJPSpace.lift D R hunit
  let B := (ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)).comp (DFJPSpace.inclusion D)
  refine ⟨D, DFJPSpace.reflexive D hD, hFDD, S, B, ?_⟩
  change ((ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)).comp
    (DFJPSpace.inclusion D)).comp (DFJPSpace.lift D R hunit) = T
  rw [ContinuousLinearMap.comp_assoc, DFJPSpace.inclusion_comp_lift]
  exact eval_infty_comp_convergentLift A T hpoint hbound

theorem weaklyCompact_reflexive_fdd_factorization [TopologicalSpace.SeparableSpace Y]
    (hBAP : HasBoundedApproximationProperty 𝕜 Y)
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) :
    ∃ D : DFJPGaugeData 𝕜 C(OnePoint ℕ, Y),
      IsReflexiveNormedSpace 𝕜 (DFJPSpace D) ∧
      Nonempty (ContractiveFiniteDecomposition 𝕜 (DFJPSpace D)) ∧
      ∃ S : X →L[𝕜] DFJPSpace D, ∃ B : DFJPSpace D →L[𝕜] Y, B.comp S = T := by
  obtain ⟨C, hC, A, hfinite, hbound, hpoint, hbidual, hadjoint⟩ :=
    exists_twoSided_finiteRank_approximants hBAP T hT
  exact twoSided_reflexive_fdd_factorization A T hfinite hpoint hbound hbidual hadjoint

end SurveyStatements.P4
