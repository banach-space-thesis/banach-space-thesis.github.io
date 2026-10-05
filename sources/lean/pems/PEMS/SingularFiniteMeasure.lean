import PEMS.CountablyGeneratedWeisTheorem
import PEMS.L1SubsigmaNoncompactness
import ThesisCommon.Analysis.L1SeparableReduction
import ThesisCommon.Analysis.OperatorNormingSequence

/-! Proposition 4.10 for arbitrary finite real measure spaces. A countable
norming sequence is retained in an actually constructed countably generated
singularity-preserving reduction. Its small-set functional is dominated by
the original one, so the checked standard-space theorem proves the full
finite-measure singular norm identity. No separability assumption remains. -/
noncomputable section
open MeasureTheory MeasurableSpace Set TopologicalSpace
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
open ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem singular_finite_alpha_eq_norm
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    alphaTheta S univ = ‖S‖ := by
  have hupper := (alphaTheta_bounds S univ MeasurableSet.univ).2
  obtain ⟨f, hf, ht⟩ := exists_operator_norming_sequence S
  obtain ⟨m, hm, n, hn, _, _, hmc, hnc, hM, _, hmap, hsing⟩ :=
    exists_countablyGenerated_singular_lOneSubsigma_reduction S hS
      ⊥ bot_le (@CountablyGenerated.mk X ⊥ ⟨∅, Set.countable_empty, by simp⟩)
      ⊥ bot_le (@CountablyGenerated.mk Y ⊥ ⟨∅, Set.countable_empty, by simp⟩)
      (Set.range f) (Set.countable_range f).isSeparable
      ∅ Set.countable_empty.isSeparable
  letI := hmc
  letI := hnc
  let R := lOneSubsigmaLift ν hn
    (S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap
  have hnorm : ‖R‖ = ‖S‖ := by
    rw [norm_lOneSubsigmaLift]
    apply norm_comp_isometry_eq_of_norming_sequence S (lOneSubsigmaEmbedding μ hm) f hf ht
    intro j
    rw [range_lOneSubsigmaEmbedding]
    exact hM (mem_range_self j)
  have hα : alphaTheta R univ = ‖R‖ :=
    singular_countablyGenerated_alpha_eq_norm R hsing
  apply le_antisymm hupper
  rw [← hnorm, ← hα]
  exact alphaTheta_univ_lOneSubsigmaLift_le S hm hn hmap

theorem singular_finite_localized_eq_norm
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    localizedWeakNoncompactness S = ‖S‖ := by
  rw [localizedWeakNoncompactness_eq_alphaTheta_univ]
  exact singular_finite_alpha_eq_norm S hS

theorem singular_finite_weakEssentialNorm_eq_norm
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    weakEssentialNorm S = ‖S‖ :=
  le_antisymm (weakEssentialNorm_le_norm S)
    ((singular_finite_localized_eq_norm S hS).symm.trans_le
      (localizedWeakNoncompactness_le_weakEssentialNorm S))

theorem proposition_4_10_real_finite
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    localizedWeakNoncompactness S = ‖S‖ ∧ ‖S‖ = weakEssentialNorm S :=
  ⟨singular_finite_localized_eq_norm S hS, (singular_finite_weakEssentialNorm_eq_norm S hS).symm⟩

theorem singular_finite_alpha_eq_adjoint_norm
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    alphaTheta S univ = ‖banachAdjoint S‖ := by
  rw [norm_banachAdjoint]
  exact singular_finite_alpha_eq_norm S hS

end PEMS
