import PEMS

/-! Proposition definitions are audited for their content, not counted as proofs.
Proof declarations below are audited separately. Only propext, Classical.choice,
and Quot.sound are allowed; the verifier rejects every other axiom. -/

#print PEMS.Theorem_1_1
#print PEMS.Corollary_1_2
#print PEMS.Theorem_1_4
#print PEMS.Theorem_1_5
#print PEMS.Corollary_1_7
#print PEMS.Corollary_1_8
#print PEMS.Corollary_1_9
#print PEMS.Corollary_1_11
#print PEMS.Corollary_1_12
#print PEMS.Corollary_1_13
#print PEMS.Theorem_1_14
#print PEMS.Lemma_5_10
#print PEMS.Proposition_5_11
#check PEMS.lemma_5_10_proof
#check PEMS.factorization_value_le_measure
#check PEMS.proposition_5_11_of_factorization
#check PEMS.theorem_1_1_zero
#check PEMS.theorem_1_1_subsingleton_domain
#check PEMS.Theorem_1_1 (𝕜 := ℝ)
#check PEMS.Theorem_1_1 (𝕜 := ℂ)
#check PEMS.Theorem_1_4 (𝕜 := ℝ)
#check PEMS.Theorem_1_4 (𝕜 := ℂ)
#check PEMS.Theorem_1_5 (𝕜 := ℝ)
#check PEMS.Theorem_1_5 (𝕜 := ℂ)
#check PEMS.Theorem_1_14 (𝕜 := ℝ)
#check PEMS.Theorem_1_14 (𝕜 := ℂ)
#check PEMS.Corollary_1_2 (𝕜 := ℝ)
#check PEMS.Corollary_1_2 (𝕜 := ℂ)
#check PEMS.Corollary_1_7 (𝕜 := ℝ)
#check PEMS.Corollary_1_7 (𝕜 := ℂ)
#check PEMS.Corollary_1_8 (𝕜 := ℝ)
#check PEMS.Corollary_1_8 (𝕜 := ℂ)
#check PEMS.Corollary_1_9 (𝕜 := ℝ)
#check PEMS.Corollary_1_9 (𝕜 := ℂ)
#check PEMS.Corollary_1_11 (𝕜 := ℝ)
#check PEMS.Corollary_1_11 (𝕜 := ℂ)
#check PEMS.Corollary_1_12 (𝕜 := ℝ)
#check PEMS.Corollary_1_12 (𝕜 := ℂ)
#check PEMS.Corollary_1_13 (𝕜 := ℝ)
#check PEMS.Corollary_1_13 (𝕜 := ℂ)

#print axioms PEMS.Theorem_1_1
#print axioms PEMS.Corollary_1_2
#print axioms PEMS.Theorem_1_4
#print axioms PEMS.Theorem_1_5
#print axioms PEMS.Corollary_1_7
#print axioms PEMS.Corollary_1_8
#print axioms PEMS.Corollary_1_9
#print axioms PEMS.Corollary_1_11
#print axioms PEMS.Corollary_1_12
#print axioms PEMS.Corollary_1_13
#print axioms PEMS.Theorem_1_14
#print axioms ThesisCommon.BanachLatticeModel
#print axioms ThesisCommon.weaklyCompact_zero
#print axioms ThesisCommon.IsWeaklyCompactOperator.add
#print axioms ThesisCommon.IsWeaklyCompactOperator.smul
#print axioms ThesisCommon.IsWeaklyCompactOperator.comp_left
#print axioms ThesisCommon.IsWeaklyCompactOperator.comp_right
#print axioms ThesisCommon.weakEssentialNorm_nonneg
#print axioms ThesisCommon.weakEssentialNorm_le
#print axioms ThesisCommon.weakEssentialNorm_le_norm
#print axioms ThesisCommon.IsWeaklyCompactOperator.weakEssentialNorm_eq_zero
#print axioms ThesisCommon.lpCut_coe
#print axioms ThesisCommon.lpCut_add
#print axioms ThesisCommon.lpCut_smul
#print axioms ThesisCommon.norm_lpCut_le
#print axioms ThesisCommon.lpCutL
#print axioms ThesisCommon.norm_lpCutL_le
#print axioms ThesisCommon.quotientOperator
#print axioms ThesisCommon.quotientOperator_mk
#print axioms ThesisCommon.quotientOperatorNorm
#print axioms ThesisCommon.bidual_preserves_image
#print axioms ThesisCommon.residuumOperator
#print axioms ThesisCommon.residuumOperator_mk
#print axioms ThesisCommon.residuumNorm
#print axioms PEMS.cutOperatorNorm_eq
#print axioms PEMS.cutOperatorNorm_nonneg
#print axioms PEMS.cutOperatorNorm_le_norm
#print axioms PEMS.smallSetSup_bounds
#print axioms PEMS.alphaTheta_bounds
#print axioms PEMS.localizedWeakNoncompactness_bounds
#print axioms ThesisCommon.weakNoncompactness_sub_eq
#print axioms ThesisCommon.weakNoncompactness_le_weakEssentialNorm
#print axioms PEMS.lemma_5_10_proof
#print axioms PEMS.factorization_value_le_measure
#print axioms PEMS.proposition_5_11_of_factorization
#print axioms PEMS.theorem_1_1_zero
#print axioms PEMS.theorem_1_1_subsingleton_domain
#print PEMS.Theorem_3_7
#print PEMS.Proposition_3_14
#check PEMS.theorem_3_7_proof
#check PEMS.proposition_3_14_of_nonneg
#check PEMS.lemma_4_3_closed_superlevel_step
#print axioms PEMS.theorem_3_7_proof
#print axioms PEMS.proposition_3_14_of_nonneg
#print axioms PEMS.lemma_4_3_closed_superlevel_step
#print axioms ThesisCommon.lt_limit_iff_exists_rat_eventually
#print axioms ThesisCommon.superlevel_eq_iUnion_iInter_of_tendsto
#print axioms ThesisCommon.superlevel_ae_eq_iUnion_iInter_of_tendsto
#print axioms ThesisCommon.MeasureAlgebra.mk_eq_mk
#print axioms ThesisCommon.MeasureAlgebra.mk_representative
#print axioms ThesisCommon.MeasureAlgebra.representative_mk_ae
#print axioms ThesisCommon.MeasureAlgebra.measure_mk
#print axioms ThesisCommon.MeasureAlgebra.compl_mk
#print axioms ThesisCommon.MeasureAlgebra.iUnion_mk
#print axioms ThesisCommon.MeasureAlgebra.iInter_mk
#print axioms ThesisCommon.MeasureAlgebra.iInter_eq_compl_iUnion_compl
#print axioms ThesisCommon.MeasureAlgebraIso.map_iInter
#print axioms ThesisCommon.MeasureAlgebra.closedSuperlevel_eq_iInter
#print axioms ThesisCommon.MeasureAlgebra.superlevel_of_ae_tendsto
#print axioms ThesisCommon.MeasureAlgebraIso.map_superlevel_of_ae_tendsto
#print axioms ThesisCommon.MeasureAlgebraIso.map_closedSuperlevel_of_ae_tendsto
#print axioms ThesisCommon.MeasureAlgebra.comap_mk
#print axioms ThesisCommon.MeasureAlgebra.comap_injective
#print axioms ThesisCommon.MeasureAlgebra.comap_surjective
#print axioms ThesisCommon.MeasureAlgebra.comap_compl
#print axioms ThesisCommon.MeasureAlgebra.comap_iUnion
#print axioms ThesisCommon.MeasureAlgebra.measure_comap
#print axioms ThesisCommon.MeasureAlgebraIso.symm
#print axioms ThesisCommon.MeasureAlgebraIso.ofComapEq
#print axioms ThesisCommon.comap_mapNatBool
#print axioms ThesisCommon.cantorMeasureModel
#print axioms ThesisCommon.cantorMeasureAlgebraIso
#print axioms ThesisCommon.exists_standardFiniteMeasureSpace
#print axioms ThesisCommon.measurable_truncatedKernel
#print axioms ThesisCommon.norm_truncatedKernel_le
#print axioms ThesisCommon.integrable_truncatedKernel
#print axioms ThesisCommon.integrable_kernel_mul
#print axioms ThesisCommon.integrable_kernelApply
#print axioms ThesisCommon.kernelApplyL1_coe
#print axioms ThesisCommon.norm_kernelApplyL1_le
#print axioms ThesisCommon.kernelApplyL1_add
#print axioms ThesisCommon.kernelApplyL1_smul
#print axioms ThesisCommon.integralKernelOperator
#print axioms ThesisCommon.norm_integralKernelOperator_le
#print axioms ThesisCommon.isIntegralKernel_integralKernelOperator
#print axioms ThesisCommon.integrable_kernel_of_nonneg
#print axioms ThesisCommon.HasKernelBound.mono
#print axioms ThesisCommon.HasKernelBound.truncatedKernel
#print axioms ThesisCommon.truncatedKernelOperator
#print axioms ThesisCommon.isIntegralKernel_truncatedKernelOperator
#print axioms ThesisCommon.norm_truncatedKernelOperator_le
#print axioms ThesisCommon.lpComap_surjective
#print axioms ThesisCommon.lpComapEquiv
#print axioms ThesisCommon.lpComapEquiv_coe
#print axioms ThesisCommon.lpComapEquiv_cut
#print axioms ThesisCommon.cantorLOneEquiv
#print axioms ThesisCommon.IsIntegralKernel.unique
#print axioms ThesisCommon.hasKernelBound_of_nonneg
#print axioms ThesisCommon.positiveTruncatedKernelOperator
#print axioms ThesisCommon.isIntegralKernel_positiveTruncatedKernelOperator
#print axioms ThesisCommon.norm_positiveTruncatedKernelOperator_le
#print axioms ThesisCommon.operatorTransport
#print axioms ThesisCommon.operatorTransport_apply
#print axioms ThesisCommon.norm_operatorTransport
#print axioms ThesisCommon.operatorTransport_symm
#print axioms ThesisCommon.operatorTransport_sub
#print axioms ThesisCommon.weaklyCompact_operatorTransport_iff
#print axioms ThesisCommon.weakEssentialNorm_operatorTransport_le
#print axioms ThesisCommon.weakEssentialNorm_operatorTransport
#print axioms ThesisCommon.measurable_pullbackKernel
#print axioms ThesisCommon.pullbackKernel_truncatedKernel
#print axioms ThesisCommon.exists_pullbackKernel
#print axioms ThesisCommon.lpTransportOperator
#print axioms ThesisCommon.lpTransportOperator_apply
#print axioms ThesisCommon.norm_lpTransportOperator
#print axioms ThesisCommon.weaklyCompact_lpTransportOperator_iff
#print axioms ThesisCommon.weakEssentialNorm_lpTransportOperator
#print axioms ThesisCommon.lpCutL_comp_lpTransportOperator
#print axioms ThesisCommon.norm_lpCutL_comp_lpTransportOperator
#print axioms ThesisCommon.IsIntegralKernel.lpTransport
#print axioms ThesisCommon.isIntegralKernel_lpTransport_iff
#print axioms ThesisCommon.isIntegralOperator_lpTransport_iff
#print axioms ThesisCommon.HasKernelBound.pullback
#print axioms ThesisCommon.integralKernelOperator_pullback
#print axioms ThesisCommon.truncatedKernelOperator_pullback
#check PEMS.theorem_3_7_with_lOne
#print axioms PEMS.theorem_3_7_with_lOne
#print axioms ThesisCommon.lpComapEquiv_le_iff
#print axioms ThesisCommon.lpComapOrderIso
#print axioms ThesisCommon.lpComapEquiv_sup
#print axioms ThesisCommon.lpComapEquiv_inf
#print axioms ThesisCommon.lpComapEquiv_abs
#print axioms ThesisCommon.lOne_norm_add_of_nonneg
#check PEMS.theorem_3_7_with_lattice
#print axioms PEMS.theorem_3_7_with_lattice
#print PEMS.Proposition_3_1
#check PEMS.proposition_3_1_proof
#check PEMS.real_lOne_operator_regular
#check PEMS.real_lOne_norm_modulus
#check PEMS.real_lOne_rieszKantorovich
#print axioms PEMS.proposition_3_1_proof
#print axioms PEMS.real_lOne_operator_regular
#print axioms PEMS.real_lOne_norm_modulus
#print axioms PEMS.real_lOne_rieszKantorovich
#print axioms ThesisCommon.realL1_isALSpace
#print axioms ThesisCommon.al_countable_sup_property
#print axioms ThesisCommon.lOneOperatorModulus
#print axioms ThesisCommon.lOneOperatorModulus_dominates
#print axioms ThesisCommon.lOneOperatorModulus_least
#print axioms ThesisCommon.norm_lOneOperatorModulus
#print axioms ThesisCommon.lOne_operator_regular
#print axioms ThesisCommon.lOneOperatorModulus_rieszKantorovich
#print axioms ThesisCommon.operatorModulus_operatorTransport
#print axioms ThesisCommon.lOneOperatorModulus_lpTransport
#print axioms PEMS.lemma_4_3_coding_modulus_step
#check PEMS.lemma_4_3_coding_modulus_step
#check PEMS.proposition_3_14_proof
#check PEMS.integral_modulus_kernel
#check PEMS.exists_truncated_integral_operator
#check PEMS.integral_operator_le_iff_kernel_le
#print axioms PEMS.proposition_3_14_proof
#print axioms PEMS.integral_modulus_kernel
#print axioms PEMS.exists_truncated_integral_operator
#print axioms PEMS.integral_operator_le_iff_kernel_le
#print axioms ThesisCommon.IsIntegralKernel.modulus
#print axioms ThesisCommon.IsIntegralKernel.hasKernelBound
#print axioms ThesisCommon.IsIntegralKernel.nonneg_ae_of_positive
#print axioms ThesisCommon.IsIntegralKernel.kernel_unique

#check PEMS.integral_positive_ideal_finite_input
#check PEMS.integral_solid_finite_input
#print axioms PEMS.integral_positive_ideal_finite_input
#print axioms PEMS.integral_solid_finite_input
#print axioms ThesisCommon.integralOperatorSubmodule
#print axioms ThesisCommon.dominatedOperatorMeasure_le_kernelMeasure
#print axioms ThesisCommon.exists_density_of_le_withDensity

#check PEMS.integral_positive_ideal
#check PEMS.integral_operator_solid
#check PEMS.integral_operator_le_iff_kernel_le_sigmaFinite
#print axioms PEMS.integral_positive_ideal
#print axioms PEMS.integral_operator_solid
#print axioms PEMS.integral_operator_le_iff_kernel_le_sigmaFinite
#print axioms ThesisCommon.lOneWithDensityEquiv
#print axioms ThesisCommon.exists_positive_finite_density

#check PEMS.real_lOne_operator_dedekind_complete
#check PEMS.integral_band_countable_sequence_step
#check PEMS.integral_kernel_lattice_formulas
#check PEMS.integral_submodule_lattice_ideal
#print axioms PEMS.real_lOne_operator_dedekind_complete
#print axioms PEMS.integral_band_countable_sequence_step
#print axioms PEMS.integral_kernel_lattice_formulas
#print axioms PEMS.integral_submodule_lattice_ideal
#print axioms ThesisCommon.abs_lOneOperator_eq

#print PEMS.Theorem_3_15_real
#check PEMS.theorem_3_15_real_proof
#check PEMS.integral_singular_decomposition_unique
#print axioms PEMS.Theorem_3_15_real
#print axioms PEMS.theorem_3_15_real_proof
#print axioms PEMS.integral_operator_order_closed
#print axioms PEMS.integral_singular_decomposition_unique
#print axioms ThesisCommon.exists_integral_kernel_of_monotone_sup
#print axioms ThesisCommon.integralBandProjection
#print axioms ThesisCommon.integralBandProjection_eq_zero_iff
#print axioms ThesisCommon.lOne_linearMap_continuous_iff_regular
#print axioms ThesisCommon.continuous_positive_linearMap

#print PEMS.Proposition_3_2
#check PEMS.proposition_3_2_proof
#print axioms PEMS.Proposition_3_2
#print axioms PEMS.proposition_3_2_proof
#print axioms PEMS.singular_iff_signed_modulus
#print axioms PEMS.integral_projection_preserves_modulus
#print axioms PEMS.integral_singular_modulus_formula
#print axioms PEMS.lemma_4_3_coding_singular_step
#print axioms PEMS.lemma_4_3_coding_lattice_step
#print axioms PEMS.lemma_4_3_coding_band_projection_step

#print axioms PEMS.exists_weakly_compact_truncation_approximant
#print axioms PEMS.weis_truncation_upper_bound

#print PEMS.Lemma_4_3
#check PEMS.lemma_4_3_proof
#print axioms PEMS.Lemma_4_3
#print axioms PEMS.lemma_4_3_proof

#print axioms PEMS.cutOperatorNorm_mono
#print axioms PEMS.cutOperatorNorm_add_le
#print axioms PEMS.cutOperatorNorm_le_smallSetSup
#print axioms PEMS.smallSetSup_mono_delta
#print axioms PEMS.smallSetSup_add_le
#print axioms PEMS.alphaTheta_le_smallSetSup
#print axioms PEMS.alphaTheta_add_le
#print axioms PEMS.smallSetSup_univ_le
#print axioms PEMS.alphaTheta_univ_le
#print axioms PEMS.localizedWeakNoncompactness_eq_alphaTheta_univ
#print axioms PEMS.alphaTheta_univ_eq_zero_of_weaklyCompact
#print axioms PEMS.alphaTheta_univ_add_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_add_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_sub_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_le_weakEssentialNorm

#print axioms PEMS.cutOperatorNorm_abs
#print axioms PEMS.smallSetSup_abs
#print axioms PEMS.alphaTheta_abs
#print axioms PEMS.localizedWeakNoncompactness_abs

#print axioms PEMS.positive_truncation_inf_le_alphaTheta
#print axioms PEMS.positive_standard_weis_norm_formula
#print axioms PEMS.weakEssentialNorm_eq_localized_positive_standard
#print axioms PEMS.cutOperatorNorm_measureAlgebraTransport
#print axioms PEMS.smallSetSup_univ_measureAlgebraTransport
#print axioms PEMS.alphaTheta_univ_measureAlgebraTransport
#print axioms PEMS.localizedWeakNoncompactness_measureAlgebraTransport
#print axioms PEMS.weakEssentialNorm_eq_localized_measureAlgebraTransport_iff

#print axioms PEMS.truncatedOperator_eq_of_kernel_ae
#print axioms PEMS.truncatedOperator_eq_of_same_operator
#print axioms PEMS.real_standard_truncation_inf_le_localized
#print axioms PEMS.real_standard_weis_norm_formula
#print axioms PEMS.real_standard_weis_norm_formula_of_decomposition
#print axioms PEMS.weakEssentialNorm_eq_localized_real_standard
#print axioms PEMS.weakEssentialNorm_abs_real_standard
#print axioms PEMS.weakEssentialNorm_eq_localized_real_countablyGenerated
#print axioms PEMS.real_countablyGenerated_weis_norm_formula
#print axioms PEMS.real_countablyGenerated_weis_norm_formula_of_decomposition
#print axioms PEMS.weakEssentialNorm_abs_real_countablyGenerated
#print axioms PEMS.exists_positive_standard_weaklyCompact_bestApproximation
#print axioms PEMS.weaklyCompact_abs_iff_real_standard
#print axioms PEMS.exists_real_standard_weaklyCompact_bestApproximation
#print axioms PEMS.weaklyCompact_abs_iff_real_countablyGenerated
#print axioms PEMS.exists_real_countablyGenerated_weaklyCompact_bestApproximation
#print axioms PEMS.Lemma_4_11_nonzero
#print axioms PEMS.lemma_4_11_nonzero_proof
#print axioms PEMS.real_countablyGenerated_weis_essSup_formula
#print axioms PEMS.real_countablyGenerated_weis_essSup_formula_of_decomposition

#print axioms PEMS.rich_family_countable_intersection
#print axioms PEMS.separable_L1_subsigma_envelope

#print axioms PEMS.singular_countablyGenerated_alpha_eq_norm
#print axioms PEMS.Theorem_4_4_real
#print axioms PEMS.theorem_4_4_real_proof
#print axioms PEMS.real_countablyGenerated_attained_weis_formula
#print PEMS.Theorem_4_4_real
#print PEMS.Lemma_4_11_nonzero

#print axioms PEMS.theorem_1_1_real_finite_countablyGenerated

#print axioms PEMS.modulusPreservingL1Family
#print axioms PEMS.lemma_4_8_modulus_rich
#print axioms PEMS.lemma_4_8_simultaneous_modulus_rich
#print axioms PEMS.singularPreservingL1Family
#print axioms PEMS.lemma_4_9_singular_rich
#print axioms PEMS.separable_L1_complemented_envelope
#print axioms PEMS.strictlyLocalizableParts
#print axioms PEMS.strictlyLocalizablePart_measurable
#print axioms PEMS.strictlyLocalizablePart_finite
#print axioms PEMS.strictlyLocalizablePart_isFiniteMeasure
#print axioms PEMS.strictlyLocalizableParts_disjoint
#print axioms PEMS.strictlyLocalizable_sum_restrict
#print axioms PEMS.strictlyLocalizableL1Equiv
#print axioms PEMS.strictlyLocalizableL1Equiv_apply
#print axioms PEMS.strictlyLocalizableL1Equiv_symm_single
#print axioms PEMS.strictlyLocalizable_L1_hasSum
#print axioms PEMS.strictlyLocalizableOperatorGlue
#print axioms PEMS.strictlyLocalizableOperatorGlue_apply
#print axioms PEMS.norm_strictlyLocalizableOperatorGlue_le
#print axioms PEMS.strictlyLocalizableOperatorGlue_extend
#print axioms PEMS.strictlyLocalizableOperatorGlue_unique
#print axioms PEMS.strictlyLocalizable_operator_norm_le_of_pieces
#print axioms PEMS.smallSetSup_antitone_localization
#print axioms PEMS.alphaTheta_antitone_localization
#print axioms PEMS.localizedWeakNoncompactness_le_alphaTheta
#print axioms PEMS.localizedWeakNoncompactness_add_le
#print axioms PEMS.cutOperatorNorm_disjoint_union_le
#print axioms PEMS.localizedWeakNoncompactness_eq_zero_of_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_add_weaklyCompact_arbitrary_output
#print axioms PEMS.localizedWeakNoncompactness_sub_weaklyCompact_arbitrary_output
#print axioms PEMS.localizedWeakNoncompactness_le_weakEssentialNorm_arbitrary_output
#print axioms PEMS.cutOperatorNorm_lOneSubsigmaLift_le
#print axioms PEMS.smallSetSup_univ_lOneSubsigmaLift_le
#print axioms PEMS.alphaTheta_univ_lOneSubsigmaLift_le
#print axioms PEMS.localizedWeakNoncompactness_lOneSubsigmaLift_le
#print axioms PEMS.singular_finite_alpha_eq_norm
#print axioms PEMS.singular_finite_localized_eq_norm
#print axioms PEMS.singular_finite_weakEssentialNorm_eq_norm
#print axioms PEMS.proposition_4_10_real_finite
#print axioms PEMS.singular_finite_alpha_eq_adjoint_norm
#print axioms PEMS.localizedWeakNoncompactness_le_of_subsigma_intertwines
#print axioms PEMS.truncationInf_le_localized_real_finite
#print axioms PEMS.real_finite_weis_norm_formula
#print axioms PEMS.weakEssentialNorm_eq_localized_real_finite
#print axioms PEMS.weakEssentialNorm_abs_real_finite
#print axioms PEMS.real_finite_weis_essSup_formula
#print axioms PEMS.exists_positive_finite_weaklyCompact_bestApproximation
#print axioms PEMS.weaklyCompact_abs_iff_real_finite
#print axioms PEMS.exists_real_finite_weaklyCompact_bestApproximation
#print axioms PEMS.real_finite_attained_weis_formula
#print axioms PEMS.theorem_1_1_real_finite
#print axioms PEMS.cutOperatorNorm_precomp_isometry
#print axioms PEMS.smallSetSup_precomp_isometry
#print axioms PEMS.alphaTheta_precomp_isometry
#print axioms PEMS.localizedWeakNoncompactness_precomp_isometry
#print axioms PEMS.weakEssentialNorm_precomp_isometry
#print axioms PEMS.weaklyCompact_precomp_isometry_iff
#print axioms PEMS.weakEssentialNorm_eq_localized_real_sigmaFiniteInput
#print axioms PEMS.weakEssentialNorm_abs_real_sigmaFiniteInput
#print axioms PEMS.weaklyCompact_abs_iff_real_sigmaFiniteInput
#print axioms PEMS.exists_real_sigmaFiniteInput_weaklyCompact_bestApproximation
#print axioms PEMS.real_sigmaFiniteInput_attained_weis_formula
#print axioms PEMS.theorem_1_1_real_sigmaFiniteInput_finiteOutput

#print axioms PEMS.cutOperatorNorm_complex_modulus
#print axioms PEMS.smallSetSup_complex_modulus
#print axioms PEMS.alphaTheta_complex_modulus
#print axioms PEMS.localizedWeakNoncompactness_complex_modulus
#print axioms PEMS.complex_singular_finite_alpha_eq_norm
#print axioms PEMS.complex_singular_finite_localized_eq_norm
#print axioms PEMS.complex_finite_truncationInf_eq_localized
#print axioms PEMS.complex_finite_truncationInf_le_localized
#print axioms PEMS.complex_singular_truncated_norm_eq_essSup
#print axioms PEMS.complex_finite_localized_eq_essSup
#print axioms PEMS.strictlyLocalizable_withDensity_of_bound
#print axioms PEMS.exists_strictlyLocalizable_normalization
#print axioms PEMS.localized_sigmaFinite_to_finite_lattice_isometry
#print axioms PEMS.proposition_4_21_real
#print axioms PEMS.alphaTheta_univ_eq_zero_of_complex_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_eq_zero_of_complex_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_add_complex_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_sub_complex_weaklyCompact
#print axioms PEMS.localizedWeakNoncompactness_le_complex_weakEssentialNorm

#print axioms PEMS.cutOperatorNorm_le_of_abs_le
#print axioms PEMS.smallSetSup_le_of_abs_le
#print axioms PEMS.alphaTheta_le_of_abs_le
#print axioms PEMS.localizedWeakNoncompactness_le_of_abs_le
#print axioms PEMS.weakEssentialNorm_le_of_abs_le_real_finite
#print axioms PEMS.weaklyCompact_of_abs_le_real_finite
#print axioms PEMS.weaklyCompact_of_complex_modulus_real_finite
#print axioms PEMS.weaklyCompact_complex_modulus_of_finite
#print axioms PEMS.weaklyCompact_complex_modulus_iff_finite
#print axioms PEMS.weaklyCompact_of_complex_modulus_le_finite
#print axioms PEMS.exists_complex_finite_weaklyCompact_modulus_bestApproximation
#print axioms PEMS.weakEssentialNorm_eq_localized_complex_finite
#print axioms PEMS.weakEssentialNorm_complex_modulus_finite
#print axioms PEMS.exists_complex_finite_weaklyCompact_bestApproximation
#print axioms PEMS.complex_finite_attained_weis_formula
#print axioms PEMS.theorem_1_1_complex_finite
#print axioms PEMS.complex_finite_weis_norm_formula
#print axioms PEMS.complex_finite_weis_essSup_formula

#print axioms PEMS.singular_smallSet_preserves_adjoint_on_subset
#print axioms PEMS.positive_singular_kernel_tail_le_of_smallCuts
#print axioms PEMS.localized_truncation_le_smallSetSup_of_input_contraction
#print axioms PEMS.strictlyLocalizableInputPiece
#print axioms PEMS.norm_strictlyLocalizableInputPiece_le
#print axioms PEMS.strictlyLocalizableInputPiece_nonneg
#print axioms PEMS.exists_strictlyLocalizable_nonneg_localized_kernels
#print axioms PEMS.exists_positive_strictlyLocalizable_localized_budget_approx
#print axioms PEMS.strictlyLocalizable_uniform_localized_truncation
#print axioms PEMS.exists_positive_strictlyLocalizable_alpha_approximation
#print axioms PEMS.exists_positive_strictlyLocalizable_localized_boundedRange_approx
#print axioms PEMS.exists_positive_strictlyLocalizable_alpha_boundedRange_approximation
#print axioms PEMS.alphaTheta_eq_zero_of_supported_small_cuts
#print axioms PEMS.alphaTheta_eq_zero_of_real_supported_weaklyCompact
#print axioms PEMS.alphaTheta_eq_zero_of_complex_supported_weaklyCompact
#print axioms PEMS.alphaTheta_add_eq_of_zero
#print axioms PEMS.alphaTheta_add_real_supported_weaklyCompact
#print axioms PEMS.alphaTheta_add_complex_supported_weaklyCompact
#print axioms PEMS.alphaTheta_le_supportedWeakEssentialNorm_of_zero_on_supported
#print axioms PEMS.proposition_4_16_real
#print axioms PEMS.proposition_4_16_complex
#print axioms PEMS.exists_real_strictlyLocalizable_alpha_approximation
#print axioms PEMS.supportedWeakEssentialNorm_eq_alphaTheta_real_strictlyLocalizable
#print axioms PEMS.exists_real_finite_supported_bestApproximation
#print axioms PEMS.exists_real_sigmaFinite_supported_bestApproximation
#print axioms PEMS.weakEssentialNorm_eq_localized_real_strictlyLocalizable
#print axioms PEMS.weakEssentialNorm_abs_real_strictlyLocalizable
#print axioms PEMS.weaklyCompact_abs_iff_real_strictlyLocalizable
#print axioms PEMS.exists_real_strictlyLocalizable_weaklyCompact_bestApproximation
#print axioms PEMS.real_strictlyLocalizable_attained_weis_formula
#print axioms PEMS.theorem_1_1_real
#print axioms PEMS.weakEssentialNorm_eq_localized_complex_sigmaFiniteInput
#print axioms PEMS.weakEssentialNorm_complex_modulus_sigmaFiniteInput
#print axioms PEMS.weaklyCompact_complex_modulus_iff_sigmaFiniteInput
#print axioms PEMS.exists_complex_sigmaFiniteInput_weaklyCompact_bestApproximation
#print axioms PEMS.complex_sigmaFiniteInput_attained_weis_formula
#print axioms PEMS.theorem_1_1_complex_sigmaFiniteInput_finiteOutput
#print axioms PEMS.factorizationSup_ellOne_le_weakEssentialNorm
#print axioms PEMS.one_sub_le_factorizationSup_of_near_disjoint

#print axioms PEMS.exists_complex_strictlyLocalizable_localized_phaseLift
#print axioms PEMS.exists_complex_strictlyLocalizable_alpha_approximation
#print axioms PEMS.supportedWeakEssentialNorm_eq_alphaTheta_complex_strictlyLocalizable
#print axioms PEMS.exists_complex_finite_supported_bestApproximation
#print axioms PEMS.exists_complex_sigmaFinite_supported_bestApproximation
#print axioms PEMS.weakEssentialNorm_eq_localized_complex_strictlyLocalizable
#print axioms PEMS.weakEssentialNorm_complex_modulus_strictlyLocalizable
#print axioms PEMS.weaklyCompact_complex_modulus_iff_strictlyLocalizable
#print axioms PEMS.exists_complex_strictlyLocalizable_weaklyCompact_bestApproximation
#print axioms PEMS.complex_strictlyLocalizable_attained_weis_formula
#print axioms PEMS.theorem_1_1_complex
#print axioms PEMS.proposition_5_2

-- October 2: factorization, representation, and C(K) structural proofs.
#print axioms PEMS.exists_finite_measure_witness_reduction
#print axioms PEMS.exists_real_finite_measure_witness_reduction
#print axioms PEMS.exists_complex_finite_measure_witness_reduction
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable
#print axioms PEMS.theorem_1_4_real_strictlyLocalizable
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable
#print axioms PEMS.theorem_1_4_complex_strictlyLocalizable
#print axioms PEMS.bonsallWeakCalkinMinimality_real_strictlyLocalizable
#print axioms PEMS.corollary_1_11_real_strictlyLocalizable
#print axioms PEMS.proposition_5_11_real_strictlyLocalizable
#print axioms PEMS.bonsallWeakCalkinMinimality_complex_strictlyLocalizable
#print axioms PEMS.corollary_1_11_complex_strictlyLocalizable
#print axioms PEMS.proposition_5_11_complex_strictlyLocalizable
#print axioms PEMS.proposition_4_21_complex
#print axioms PEMS.mul_one_sub_le_factorizationSup_of_almost_disjoint
#print axioms PEMS.le_factorizationSup_of_almost_disjoint
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_of_almost_disjoint
#print axioms PEMS.factorization_witness_of_operatorTransport
#print axioms PEMS.factorizationSup_operatorTransport
#print axioms PEMS.factorization_constant_le_norm
#print axioms PEMS.factorizationSup_le_norm
#print axioms PEMS.factorizationSup_nonneg
#print axioms PEMS.factorizationSup_of_contractive_composition_le
#print axioms PEMS.factorizationSup_ellOne_of_contractive_composition_le
#print axioms PEMS.exists_normalized_disjoint_blocks_of_weak_residual
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_real_finite
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_complex_finite
#print axioms PEMS.theorem_1_4_real_finite
#print axioms PEMS.theorem_1_4_complex_finite
#print axioms PEMS.one_le_algebraNorm_of_nonweaklyCompact_idempotent
#print axioms PEMS.weakEssentialNorm_id_eq_one_of_ne_zero
#print axioms PEMS.bonsallWeakCalkinMinimality_of_ellOne_factorization
#print axioms PEMS.disjointOutputWitness_step
#print axioms PEMS.exists_almost_disjointOutputWitness
#print axioms PEMS.exists_disjointOutputWitness_bounds
#print axioms PEMS.exists_disjointOutputWitness_limit
#print axioms PEMS.Lemma_5_1
#print axioms PEMS.exists_real_disjointOutputWitness_weakEssentialNorm
#print axioms PEMS.exists_complex_disjointOutputWitness_weakEssentialNorm
#print axioms PEMS.lemma_5_1_real
#print axioms PEMS.lemma_5_1_complex
#print axioms PEMS.extremal_cutoff_residual_unifIntegrable
#print axioms PEMS.extremal_cutoff_residual_uniformIntegrable
#print axioms PEMS.disjoint_extremal_cutoff_residual_uniformIntegrable
#print axioms PEMS.eventually_cutOperatorNorm_lt_alphaTheta_univ_add
#print axioms PEMS.cutoff_norm_limit_le_alphaTheta_univ
#print axioms PEMS.extremal_cutoff_input_norm_tendsto_one
#print axioms PEMS.exists_normalized_disjoint_extremal_of_splitting
#print axioms PEMS.exists_disjointOutputWitness_extremal
#print axioms PEMS.exists_real_finite_disjointInput_extremal
#print axioms PEMS.exists_complex_finite_disjointInput_extremal
#print axioms PEMS.lemma_5_4_real_finite
#print axioms PEMS.lemma_5_4_complex_finite
#print axioms PEMS.lemma_5_3_real_subsequence_splitting
#print axioms PEMS.lemma_5_3_complex_subsequence_splitting

-- Sixth checked PEMS batch.
#print axioms PEMS.sigmaMeasure_strictlyLocalizable
#print axioms PEMS.FiniteL1OperatorModel
#print axioms PEMS.exists_finiteL1OperatorModel_of_witness
#print axioms PEMS.exists_real_finiteL1OperatorModel
#print axioms PEMS.lemma_5_5_real
#print axioms PEMS.exists_complex_finiteL1OperatorModel
#print axioms PEMS.lemma_5_5_complex
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_real_AL
#print axioms PEMS.theorem_1_4_real
#print axioms PEMS.weakEssentialNorm_eq_factorizationSup_complex_AL
#print axioms PEMS.theorem_1_4_complex
#print axioms PEMS.corollary_1_11_real
#print axioms PEMS.proposition_5_11_real
#print axioms PEMS.corollary_1_11_complex
#print axioms PEMS.proposition_5_11_complex
#print axioms PEMS.exists_real_AL_weaklyCompact_bestApproximation
#print axioms PEMS.exists_complex_AL_weaklyCompact_bestApproximation
#print axioms PEMS.corollary_1_2_real
#print axioms PEMS.corollary_1_2_complex
#print axioms PEMS.deBlasiSet_nonneg
#print axioms PEMS.deBlasiSet_le_of_approximation
#print axioms PEMS.deBlasiSet_le_of_bound
#print axioms PEMS.deBlasiOperator_nonneg
#print axioms PEMS.deBlasiOperator_le_norm_sub
#print axioms PEMS.deBlasiOperator_le_weakEssentialNorm
#print axioms PEMS.deBlasiOperator_le_norm
#print axioms PEMS.deBlasiOperator_eq_zero_of_weaklyCompact
#print axioms PEMS.ellOne_factorization_constant_le_deBlasiOperator
#print axioms PEMS.factorizationSup_ellOne_le_deBlasiOperator
#print axioms PEMS.deBlasiOperator_eq_weakEssentialNorm_of_ellOne_factorization
#print axioms PEMS.deBlasiOperator_eq_weakEssentialNorm_real_AL
#print axioms PEMS.deBlasiOperator_eq_weakEssentialNorm_complex_AL
#print axioms PEMS.deBlasi_banachAdjoint_eq_dualWeakEssentialNorm_real_continuousMap
#print axioms PEMS.deBlasi_banachAdjoint_eq_dualWeakEssentialNorm_complex_continuousMap
#print axioms PEMS.exists_ordered_lOne_representation_of_real_AL
#print axioms PEMS.exists_lOne_representation_of_real_isAL
#print axioms PEMS.exists_lOne_representation_of_complex_AL_model
#print axioms PEMS.exists_lOne_representation_of_complex_isAL
#print axioms PEMS.weakCalkinNorm_le_sq_mul_of_factorization_and_bound
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds
#print axioms PEMS.minimalWeakCalkinNorm_of_factorization_and_upperBounds
#print axioms PEMS.exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies
#print axioms PEMS.exists_weakCalkinAlgebraNorm_upperBound_of_square_equiv
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_of_square_and_factorization
#print axioms PEMS.minimalWeakCalkinNorm_of_square_and_factorization
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_of_weaklyCompact_id
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_of_factorization_and_nonreflexive_square
#print axioms PEMS.weakCalkinAlgebraNorm_upperBound_of_representative_bound
#print axioms PEMS.weakCalkinMk_eq_compressed_of_weaklyCompact_remainder
#print axioms PEMS.exists_weakCalkinAlgebraNorm_upperBound_of_complemented_core
#print axioms PEMS.exists_weakCalkinAlgebraNorm_upperBound_of_weaklyCompact_product
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_atomic_real_AL
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_intervalL1_real
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_intervalL1_complex
#print axioms PEMS.LebesgueProductALModel
#print axioms PEMS.exists_weakCalkinAlgebraNorm_upperBound_of_lebesgueProductModel
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_real_AL_of_lebesgueProductModel
#print axioms PEMS.uniqueWeakCalkinAlgebraNorm_complex_AL_of_lebesgueProductModel
#print axioms PEMS.theorem_6_5_continuousMap
#print axioms PEMS.exists_cZero_factorization_of_fixed_copy_sequentiallyCompact
#print axioms PEMS.le_factorizationSup_of_fixed_copy_sequentiallyCompact
#print axioms PEMS.minimumModulus_cZero_nonneg
#print axioms PEMS.minimumModulus_cZero_mul_norm_le
#print axioms PEMS.minimumModulus_comp_le_dualWeakEssentialNorm
#print axioms PEMS.fixesCZeroSup_le_dualWeakEssentialNorm

-- Seventh checked PEMS batch.
#print axioms PEMS.exists_real_AL_disjoint_positiveWitness
#print axioms PEMS.exists_complex_AL_disjoint_positiveWitness
#print axioms PEMS.exists_real_continuousMapDual_disjoint_positiveWitness
#print axioms PEMS.exists_complex_continuousMapDual_disjoint_positiveWitness
#print axioms PEMS.residuumNorm_le_of_weakCompact_approximation
#print axioms PEMS.residuumNorm_le_deBlasiOperator
#print axioms PEMS.factorizationSup_infinity_le_residuumNorm
#print axioms PEMS.weakEssentialNorm_eq_residuumNorm_of_infinity_factorization
#print axioms PEMS.residuumNorm_eq_deBlasiOperator_of_infinity_factorization
#print axioms PEMS.theorem_1_5_real
#print axioms PEMS.theorem_1_5_complex
#print axioms PEMS.four_quantities_of_real_extremallyDisconnected_model
#print axioms PEMS.four_quantities_of_complex_extremallyDisconnected_model
#print axioms PEMS.continuousMap_four_quantities_real
#print axioms PEMS.continuousMap_four_quantities_complex
#print axioms PEMS.exists_real_adjoint_disjoint_open_witness
#print axioms PEMS.exists_complex_adjoint_disjoint_open_witness
#print axioms PEMS.fixesCZeroSup_nonneg
#print axioms PEMS.dualWeakEssentialNorm_le_fixesCZeroSup_real
#print axioms PEMS.dualWeakEssentialNorm_le_fixesCZeroSup_complex
#print axioms PEMS.dualWeakEssentialNorm_eq_fixesCZeroSup_real
#print axioms PEMS.dualWeakEssentialNorm_eq_fixesCZeroSup_complex
#print axioms PEMS.le_fixesCZeroSup_of_column_lower_bound
#print axioms PEMS.le_fixesCZeroSup_of_disjoint_continuous_columns
#print axioms PEMS.theorem_6_7_countable
#print axioms PEMS.le_factorizationSup_infinity_of_fixed_copy_extremallyDisconnected
#print axioms PEMS.factorization_constant_le_fixesCZeroSup
#print axioms PEMS.factorizationSup_le_fixesCZeroSup_of_isometry
#print axioms PEMS.factorizationSup_cZero_le_fixesCZeroSup
#print axioms PEMS.factorizationSup_infinity_le_fixesCZeroSup
#print axioms PEMS.fixesCZeroSup_eq_factorizationSup_cZero_sequentiallyCompact
#print axioms PEMS.fixesCZeroSup_eq_factorizationSup_infinity_extremallyDisconnected
#print axioms PEMS.theorem_1_5_of_fixing_formula
#print axioms PEMS.generic_product_factorization_constants_le_algebraNorm
#print axioms PEMS.generic_quotientNorm_id_eq_one_of_ne_zero
#print axioms PEMS.bonsallWeakCalkinMinimality_of_generic_factorization
#print axioms PEMS.bonsall_weakEssentialNorm_of_generic_factorization
#print axioms PEMS.bonsall_dualWeakEssentialNorm_of_generic_factorization
#print axioms PEMS.factorizationSup_le_rectangular_bound
#print axioms PEMS.minimalWeakCalkinNorm_of_generic_factorization
#print axioms PEMS.minimal_weakEssentialNorm_of_generic_factorization
#print axioms PEMS.minimal_dualWeakEssentialNorm_of_generic_factorization
#print axioms PEMS.dualWeakEssentialNorm_eq_cZero_factorization_real
#print axioms PEMS.dualWeakEssentialNorm_eq_cZero_factorization_complex
#print axioms PEMS.weakEssentialNorm_eq_infinity_factorization_real
#print axioms PEMS.weakEssentialNorm_eq_infinity_factorization_complex
#print axioms PEMS.corollary_1_8_real
#print axioms PEMS.corollary_1_8_complex
#print axioms PEMS.corollary_1_9_real
#print axioms PEMS.corollary_1_9_complex
#print axioms PEMS.corollary_1_12_real
#print axioms PEMS.corollary_1_12_complex
#print axioms PEMS.corollary_1_13_real
#print axioms PEMS.corollary_1_13_complex
#print axioms PEMS.minimal_weakCalkinNorm_real_AL
#print axioms PEMS.minimal_weakCalkinNorm_complex_AL
#print axioms PEMS.theorem_1_14_real
#print axioms PEMS.theorem_1_14_complex

-- Final Corollary 1.7 construction and main proofs.
#print axioms PEMS.exists_weakCalkinAlgebraNorm_upperBound_of_corner_selfCopies
#print axioms PEMS.corollary_1_7_real
#print axioms PEMS.corollary_1_7_complex
