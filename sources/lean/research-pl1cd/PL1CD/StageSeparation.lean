import PL1CD.StageFiltration
import PL1CD.HaarTransport
import PL1CD.VariationComposition
import PL1CD.IdealSeparation
import PL1CD.MaximalVariation

noncomputable section
open scoped NNReal Topology

namespace PL1CD

open Variation
variable (𝕜 : Type) [RCLike 𝕜]

def stageVariation (a : ContinuumIndex) (Z : Type*)
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    Seminorm 𝕜 (HaarL1 𝕜 →L[𝕜] Z) :=
  averagedVariation 𝕜 Z StageParameters.filtration StageParameters.levels
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)

theorem stageVariation_unitResolvent_eq_two (a : ContinuumIndex) :
    stageVariation 𝕜 a (HaarL1 𝕜)
      (unitResolvent 𝕜 (StageParameters.rates (AlmostDisjoint.family a))) = 2 :=
  averagedVariation_unitResolvent_eq_two 𝕜 (AlmostDisjoint.family a)
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a) (Set.Subset.refl _)

structure StageAnalyticSeparation : Prop where
  vanishing : ∀ a b, a ≠ b → ∀ T : HaarL1 𝕜 →L[𝕜] (stageProjectionFamily 𝕜 b).range,
    stageVariation 𝕜 a (stageProjectionFamily 𝕜 b).range T = 0

namespace StageAnalyticSeparation

variable {𝕜} (h : StageAnalyticSeparation 𝕜)
include h

theorem rangeWitness_positive (a : ContinuumIndex) :
    0 < stageVariation 𝕜 a (stageProjectionFamily 𝕜 a).range
      (rangeWitness 𝕜 (StageParameters.rates (AlmostDisjoint.family a))) := by
  let rates := StageParameters.rates (AlmostDisjoint.family a)
  let p := averagedVariation 𝕜 (intervalProjection 𝕜 rates).range
    StageParameters.filtration StageParameters.levels
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)
  change 0 < p (rangeWitness 𝕜 rates)
  have hcomp := averagedVariation_comp_le StageParameters.filtration StageParameters.levels
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)
    (rangeWitness 𝕜 rates) (rangeEvaluation 𝕜 rates)
  rw [rangeEvaluation_comp_witness] at hcomp
  have hmax := stageVariation_unitResolvent_eq_two 𝕜 a
  change stageVariation 𝕜 a (HaarL1 𝕜) (unitResolvent 𝕜 rates) = 2 at hmax
  change stageVariation 𝕜 a (HaarL1 𝕜) (unitResolvent 𝕜 rates) ≤ _ at hcomp
  rw [hmax] at hcomp
  change 2 ≤ ‖rangeEvaluation 𝕜 rates‖ * p (rangeWitness 𝕜 rates) at hcomp
  have hnorm := norm_rangeEvaluation_le 𝕜 rates
  have hp := apply_nonneg p (rangeWitness 𝕜 rates)
  have hbound := mul_le_mul_of_nonneg_right hnorm hp
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (hcomp.trans (by simpa only [one_mul] using hbound))

theorem theoremCSpec : TheoremCSpec 𝕜 (stageProjectionFamily 𝕜) := by
  refine ⟨fun a => ⟨stageProjectionFamily_isProjection 𝕜 a,
    stageProjectionFamily_norm_le 𝕜 a,
    intervalProjection_range_closed 𝕜 _⟩, ?_⟩
  intro a b hab
  exact not_containsIsomorphicCopy_of_variation StageParameters.filtration StageParameters.levels
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)
    (rangeWitness 𝕜 (StageParameters.rates (AlmostDisjoint.family a)))
    (h.rangeWitness_positive a) (h.vanishing a b hab)

theorem theoremC : TheoremCStatement 𝕜 := ⟨stageProjectionFamily 𝕜, h.theoremCSpec⟩

def idealSeparationData : IdealSeparationData 𝕜 (stageProjectionFamily 𝕜) where
  test a := haarLift 𝕜 (unitResolvent 𝕜 (StageParameters.rates (AlmostDisjoint.family a)))
  seminorm a := (stageVariation 𝕜 a (HaarL1 𝕜)).comp (haarExtract 𝕜).toLinearMap
  continuous a := (averagedVariation_continuous 𝕜 (HaarL1 𝕜)
    StageParameters.filtration StageParameters.levels
    (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a)).comp
    (haarExtract 𝕜).continuous
  bound a T := by
    change stageVariation 𝕜 a (HaarL1 𝕜) (haarExtract 𝕜 T) ≤ 2 * ‖T‖
    exact (averagedVariation_le 𝕜 (HaarL1 𝕜) _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (norm_haarExtract_apply_le 𝕜 T) (by norm_num))
  test_norm a := by rw [norm_haarLift, norm_unitResolvent]
  test_value a := by
    change stageVariation 𝕜 a (HaarL1 𝕜) (haarExtract 𝕜 (haarLift 𝕜 _)) = 2
    rw [haarExtract_lift]
    exact stageVariation_unitResolvent_eq_two 𝕜 a
  test_factors a := by
    rw [lift_resolvent_factors]
    have hgen := generator_mem_generatedIdeal 𝕜 (stageProjectionFamily 𝕜) {a}
      (Set.mem_singleton a)
    have hI := (generatedIdeal_isClosedTwoSided 𝕜 (stageProjectionFamily 𝕜) {a}).2
    exact (hI _ ((hI _ hgen _).2) _).1
  off_diagonal a b hab U V := by
    let T : HaarL1 𝕜 →L[𝕜] (stageProjectionFamily 𝕜 b).range :=
      (stageProjectionFamily 𝕜 b).rangeRestrict.comp (U.comp (haarEmbedding 𝕜))
    let W : (stageProjectionFamily 𝕜 b).range →L[𝕜] HaarL1 𝕜 :=
      (haarRetraction 𝕜).comp (V.comp (stageProjectionFamily 𝕜 b).range.subtypeL)
    have heq : haarExtract 𝕜 (V.comp ((stageProjectionFamily 𝕜 b).comp U)) = W.comp T := by
      ext x
      rfl
    change stageVariation 𝕜 a (HaarL1 𝕜) (haarExtract 𝕜 _) = 0
    rw [heq]
    apply le_antisymm _ (apply_nonneg _ _)
    have hcomp := averagedVariation_comp_le StageParameters.filtration StageParameters.levels
      (AlmostDisjoint.family a) (AlmostDisjoint.family_infinite a) T W
    change stageVariation 𝕜 a (HaarL1 𝕜) (W.comp T) ≤
      ‖W‖ * stageVariation 𝕜 a (stageProjectionFamily 𝕜 b).range T at hcomp
    simpa only [h.vanishing a b hab T, mul_zero] using hcomp

theorem theoremD : TheoremDStatement 𝕜 :=
  h.idealSeparationData.theoremD (stageProjectionFamily_range_schur 𝕜)

theorem theoremsCD : TheoremCStatement 𝕜 ∧ TheoremDStatement 𝕜 :=
  ⟨h.theoremC, h.theoremD⟩

end StageAnalyticSeparation
end PL1CD
