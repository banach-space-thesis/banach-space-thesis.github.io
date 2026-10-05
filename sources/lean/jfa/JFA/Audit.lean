import JFA
import Mathlib.Analysis.Complex.Basic

/-! Compile this file after `lake build`. It checks both scalar cases, the
completion instances, the retained hypotheses, and foundational dependencies.
The final examples apply the completed proofs of Theorems 1.1, 1.4 and 1.6 and
Corollaries 1.2–1.3. -/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open scoped ZeroAtInfty

#check JFA.Theorem_1_1 ℝ ℝ ℝ ℝ
#check JFA.Theorem_1_1 ℂ ℂ ℂ ℂ
#check JFA.Corollary_1_2 ℝ ℝ ℝ ℝ
#check JFA.Corollary_1_2 ℂ ℂ ℂ ℂ
section FunctionSpaceChecks
variable (M N : Type*) [MetricSpace M] [CompactSpace M] [MetricSpace N] [CompactSpace N]
#check JFA.Corollary_1_3 ℝ ℕ M N
#check JFA.Corollary_1_3 ℂ ℕ M N
example : JFA.Corollary_1_3 ℝ ℕ M N := JFA.corollary_1_3 M N
example : JFA.Corollary_1_3 ℂ ℕ M N := JFA.corollary_1_3 M N
end FunctionSpaceChecks
#check JFA.Theorem_1_4 ℝ
#check JFA.Theorem_1_4 ℂ
#check JFA.Theorem_1_6 ℝ
#check JFA.Theorem_1_6 ℂ

example : CompleteSpace (JFA.InjectiveTensor ℝ ℝ ℝ) := inferInstance
example : CompleteSpace (JFA.InjectiveTensor ℂ ℂ ℂ) := inferInstance
example (𝕜 : Type*) [RCLike 𝕜]
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] :
    CompleteSpace (JFA.InjectiveTensor 𝕜 E X) := inferInstance
example (𝒜 : Set (Set ℕ)) : CompleteSpace (JFA.MrowkaCZero ℝ 𝒜) := inferInstance
example (𝒜 : Set (Set ℕ)) : CompleteSpace (JFA.AmplifiedMrowka ℂ 𝒜) := inferInstance

#print JFA.Theorem_1_1
#print JFA.Corollary_1_2
#print JFA.Corollary_1_3
#print JFA.Theorem_1_4
#print JFA.Theorem_1_6

#print axioms JFA.Theorem_1_1
#print axioms JFA.Corollary_1_2
#print axioms JFA.Corollary_1_3
#print axioms JFA.Theorem_1_4
#print axioms JFA.Theorem_1_6
#print axioms JFA.tensorPairing
#print axioms JFA.injectivePure_apply
#print axioms JFA.ReasonableCrossnorm.isTensorCompletion
#print axioms JFA.norm_injectivePure
#print axioms JFA.dualOperator_norm_le_iff
#print axioms JFA.mrowkaTopology
#print axioms JFA.IsClosedOperatorIdeal

-- Proved infrastructure for the full-proof stage. These are actual theorems,
-- whereas the five numbered declarations above are still proposition definitions.
#print axioms JFA.scalar_id_separable_iff
#print axioms JFA.fewOperators_unique_decomposition
#print axioms JFA.hasSeparableRange_of_tendsto
#print axioms JFA.separableOperators_closedIdeal
#print axioms JFA.tensor_decomposition_unique
#print axioms JFA.scalarCoefficientL
#print axioms JFA.scalarCoefficient_comp
#print axioms JFA.scalarCoefficient_eq_zero_iff
#print axioms JFA.injectiveInclusion_dense
#print axioms JFA.norm_rightSlice_le
#print axioms JFA.rightSlice_pairing
#print axioms JFA.norm_le_of_normingSequence_le
#print axioms JFA.exists_common_separable_subspace
#print axioms JFA.exists_annihilator_of_separable
#print axioms JFA.exists_unique_scalar_representative
#print axioms JFA.norm_scalarExtractionL_le
#print axioms JFA.norm_extractedOperator_le
#print axioms JFA.extractedOperator_slice_remainder_separable
#print axioms JFA.tensorExtension_pure
#print axioms JFA.norm_tensorExtension_le
#print axioms JFA.tensorRemainder_pure
#print axioms JFA.tensorRemainder_common_subspace
#print axioms JFA.tensorRemainder_common_subspace_all_dual
#print axioms JFA.norm_le_of_norming_slices_le
#print axioms JFA.dualBallCoordinates_isClosedEmbedding
#print axioms JFA.dualBallSecondCountableTopology
#print axioms JFA.tensorFunction_apply
#print axioms JFA.tensorFunctionIsometry
#print axioms JFA.hasSeparableRange_of_slices_in_separable_subspace
#print axioms JFA.tensorRemainder_separable
#print axioms JFA.theorem_1_1
#print axioms JFA.injectiveTensorMap_comp
#print axioms JFA.injectiveTensorMap_id
#print axioms JFA.epsilonRemainder_separable
#print axioms JFA.epsilonScalarOperator_comp
#print axioms JFA.corollary_1_2
#print axioms JFA.epsilonDecomposition
#print axioms JFA.czeroDualEvaluation_isEmbedding
#print axioms JFA.czero_nonseparable_of_nonmetrizable
#print axioms JFA.tensorContinuousIsometry
#print axioms JFA.tensorContinuousEquiv
#print axioms JFA.czeroProductEquiv
#print axioms JFA.czeroTensorEquiv
#print axioms JFA.corollary_1_3
#print axioms JFA.epsilonScalarOperator_projection
#print axioms JFA.projection_factorization_complemented
#print axioms JFA.mrowka_isCompact_neighborhood
#print axioms JFA.mrowka_locallyCompactSpace
#print axioms JFA.mrowka_t2Space
#print axioms JFA.mrowka_inl_denseRange
#print axioms JFA.mrowka_remainder_isClosed
#print axioms JFA.mrowka_remainder_discreteTopology
#print axioms JFA.mrowka_compact_meets_remainder_finitely
#print axioms JFA.mrowka_nonmetrizable
#print axioms JFA.mrowka_function_support_countable
#print axioms JFA.mrowka_set_support_countable
#print axioms JFA.mrowka_czero_nonseparable
#print axioms JFA.norm_tensorCzeroFunction
#print axioms JFA.tensorCzeroDiscreteEquiv
#print axioms JFA.czero_countable_discrete_separable
#print axioms JFA.czeroDiscreteProductEquiv
#print axioms JFA.czeroDiscreteTensorEquiv
#print axioms JFA.mrowkaAmplificationEquiv
#print axioms JFA.amplifiedRemainder_separable
#print axioms JFA.amplified_decomposition
#print axioms JFA.amplifiedScalarOperator_projection
#print axioms JFA.epsilonScalarQuotient
#print axioms JFA.epsilonScalarQuotient_surjective
#print axioms JFA.epsilonScalarOperator_eq_zero_iff
#print axioms JFA.amplifiedScalarQuotient_surjective
#print axioms JFA.amplifiedScalarOperator_comp
#print axioms JFA.amplifiedScalarOperator_eq_zero_iff
#print axioms JFA.norm_amplifiedScalarQuotient_le
#print axioms JFA.amplifiedScalarAlgebraHom
#print axioms JFA.closedOperatorIdealQuotientOrderIso
#print axioms JFA.amplifiedScalarQuotient_kernel
#print axioms JFA.amplifiedClosedIdealOrderIso
#print axioms JFA.amplifiedClosedIdealOrderIso_image
#print axioms JFA.amplifiedClosedIdealOrderIso_preimage
#print axioms JFA.compactOperators_closedIdeal
#print axioms JFA.compactOperators_subset_separableOperators
#print axioms JFA.factorizationOperators_subset_separableOperators
#print axioms JFA.closure_factorizationOperators_subset_separableOperators
#print axioms JFA.mrowka_isScattered
#print axioms JFA.amplifiedMrowka_isScattered
#print axioms JFA.amplified_noncompact_factors_cZero_identity
#print axioms JFA.factorizationOperators_subset_ideal_of_factors_identity
#print axioms JFA.amplified_ideal_contains_cZero_factorizations_of_not_subset_compact
#print axioms JFA.smulRight_mem_ideal_of_ne_zero
#print axioms JFA.czero_compact_uniform_tail
#print axioms JFA.exists_czeroTruncation_compact_approx
#print axioms JFA.cZero_compactOperators_minimal
#print axioms JFA.cZero_noncompact_factors_identity
#print axioms JFA.cZero_closedIdeal_classification
#print axioms JFA.cZero_compact_ideal_strict
#print axioms JFA.amplified_closedIdeal_classification_above_separable
#print axioms JFA.amplified_upper_ideals_strict
#print axioms JFA.projection_range_isClosed
#print axioms JFA.projection_compact_iff_finiteDimensional
#print axioms JFA.amplified_exists_cZero_retract
#print axioms JFA.amplified_complemented_infinite_contains_cZero_retract
#print axioms JFA.amplified_exists_separable_noncompact_projection
#print axioms JFA.amplified_compact_strictly_below_separable
#print axioms JFA.mrowka_isClopen_neighborhood
#print axioms JFA.exists_pairwise_disjoint_mrowka_tails
#print axioms JFA.summable_smul_disjointCzero
#print axioms JFA.disjointCzeroSynthesis
#print axioms JFA.disjointCzeroSynthesis_apply_coordinate
#print axioms JFA.mrowka_natural_values_null
#print axioms JFA.mrowkaNaturalLift_read
#print axioms JFA.mrowkaFamilyRead
#print axioms JFA.mrowkaSupportJoin_split
#print axioms JFA.mrowkaSupportedSubmodule_isClosed
#print axioms JFA.exists_countable_czero_product_retract
#print axioms JFA.separable_mrowka_factors_cZero
#print axioms JFA.amplified_separable_factors_cZero
#print axioms JFA.amplified_factorizationOperators_eq_separableOperators
#print axioms JFA.amplified_cZeroFactorizations_closedIdeal
#print axioms JFA.czeroTruncation_factor_rankOne_sum
#print axioms JFA.compact_factor_approximant_mem_ideal
#print axioms JFA.amplified_compactOperators_minimal
#print axioms JFA.amplified_zero_strictly_below_compact
#print axioms JFA.closure_factorizationOperators_closedIdeal
#print axioms JFA.factorizationOperators_subset_of_retract
#print axioms JFA.injectiveTensorMap_smulRight
#print axioms JFA.mrowka_exists_cZero_retract
#print axioms JFA.amplified_exists_X_coordinate_retract
#print axioms JFA.amplifiedCompactPreimage_closedIdeal
#print axioms JFA.amplified_X_factorizations_subset_compactPreimage
#print axioms JFA.amplified_closure_X_factorizations_eq_compactPreimage
#print axioms JFA.amplified_closedIdeal_classification
#print axioms JFA.theorem_1_6
#print axioms JFA.cZero_projection_range_iso
#print axioms JFA.cZero_complemented_infinite_iso
#print axioms JFA.amplified_separable_projection_range_iso
#print axioms JFA.cZeroSquareEquiv
#print axioms JFA.cZero_absorbs_complemented
#print axioms JFA.absorbs_complemented_cZero_subspace
#print axioms JFA.projection_complement_range_eq_kernel
#print axioms JFA.projection_range_iso_of_complement_factors_cZero
#print axioms JFA.amplified_complement_separable_projection_range_iso
#print axioms JFA.amplified_projection_scalar_zero_range_iso
#print axioms JFA.amplified_projection_scalar_identity_range_iso
#print axioms JFA.absorbs_cZero_of_retract
#print axioms JFA.projection_range_stabilized_retract
#print axioms JFA.isomorphic_of_stabilized_cZero_retracts
#print axioms JFA.projection_range_iso_of_cZero_difference
#print axioms JFA.injectiveTensorEquiv
#print axioms JFA.injectiveTensorMap_projection
#print axioms JFA.injectiveTensorProjectionRangeEquiv
#print axioms JFA.conjugateProjectionRangeEquiv
#print axioms JFA.amplifiedTensorLift_projection
#print axioms JFA.amplifiedTensorProjectionRangeEquiv
#print axioms JFA.amplifiedSequenceSelfSimilarEquiv
#print axioms JFA.amplified_lift_noncompact_projection_range_iso
#print axioms JFA.amplified_not_finiteDimensional
#print axioms JFA.amplified_noncompact_scalar_projection_range_iso
#print axioms JFA.finiteCZeroFunction
#print axioms JFA.norm_finiteCZeroFunction
#print axioms JFA.finiteCZeroEquiv
#print axioms JFA.finitePowerTensorEquiv
#print axioms JFA.finitePower_isomorphic_iff
#print axioms JFA.not_isomorphic_cZero_of_nonseparable
#print axioms JFA.finitePower_nonseparable
#print axioms JFA.not_isomorphic_finitePower_cZeroSum
#print axioms JFA.amplified_nonseparable
#print axioms JFA.not_isomorphic_finitePower_amplified
#print axioms JFA.amplified_model_unique
-- Case assembly and the checked input completing its finite scalar case.
#print axioms JFA.theorem_1_4_of_nonzero_compact_scalar_case
#print axioms JFA.projection_range_comparison_kernel_retract
#print axioms JFA.absorbs_cZero_retract
#print axioms JFA.projection_ranges_isomorphic_of_cZero_difference
#print axioms JFA.compact_nonzero_projection_range_finite_power
#print axioms JFA.amplified_lift_compact_nonzero_projection_range_iso
#print axioms JFA.amplified_nonzero_compact_scalar_projection_range_iso
#print axioms JFA.theorem_1_4
#check JFA.cZero_closedIdeal_classification (𝕜 := ℝ)
#check JFA.cZero_closedIdeal_classification (𝕜 := ℂ)
#check JFA.amplifiedScalarAlgebraHom (𝕜 := ℝ)
#check JFA.amplifiedScalarAlgebraHom (𝕜 := ℂ)

example : JFA.InjectiveTensor ℝ (JFA.cZero ℝ) ℝ ≃ₗᵢ[ℝ] C₀(ℕ, ℝ) :=
  JFA.tensorCzeroDiscreteEquiv
example : JFA.InjectiveTensor ℂ (JFA.cZero ℂ) ℂ ≃ₗᵢ[ℂ] C₀(ℕ, ℂ) :=
  JFA.tensorCzeroDiscreteEquiv
#print JFA.amplified_decomposition

-- These are proofs of the numbered proposition, instantiated over both fields.
example : JFA.Theorem_1_1 ℝ ℝ ℝ ℝ := JFA.theorem_1_1
example : JFA.Theorem_1_1 ℂ ℂ ℂ ℂ := JFA.theorem_1_1
#print JFA.theorem_1_1
example : JFA.Corollary_1_2 ℝ ℝ ℝ ℝ := JFA.corollary_1_2
example : JFA.Corollary_1_2 ℂ ℂ ℂ ℂ := JFA.corollary_1_2
#print JFA.corollary_1_2
#print JFA.corollary_1_3
example (𝒜 : Set (Set ℕ)) : JFA.Theorem_1_4 ℝ 𝒜 := JFA.theorem_1_4
example (𝒜 : Set (Set ℕ)) : JFA.Theorem_1_4 ℂ 𝒜 := JFA.theorem_1_4
#print JFA.theorem_1_4
example (𝒜 : Set (Set ℕ)) : JFA.Theorem_1_6 ℝ 𝒜 := JFA.theorem_1_6
example (𝒜 : Set (Set ℕ)) : JFA.Theorem_1_6 ℂ 𝒜 := JFA.theorem_1_6
#print JFA.theorem_1_6
