import UPFP

/-! A target's axiom report checks its definition, NOT its truth. -/
#print UPFP.Theorem_1_1
#print UPFP.Theorem_1_2
#print UPFP.Corollary_1_3
#print UPFP.Corollary_1_5
#print UPFP.Theorem_1_6
#print ThesisCommon.IsSequenceSelfSimilar
#print ThesisCommon.IsFiniteLpSelfSimilar
#print ThesisCommon.HasFiniteCotype
#print ThesisCommon.HasRademacherCotype
#print axioms UPFP.Theorem_1_1
#print axioms UPFP.Theorem_1_2
#print axioms UPFP.Corollary_1_3
#print axioms UPFP.Corollary_1_5
#print axioms UPFP.Theorem_1_6
#print axioms UPFP.proposition_5_5_infinity
#print axioms UPFP.proposition_5_5_cZero
#print axioms UPFP.proposition_5_5_ellOne
#print axioms UPFP.lemma_5_6
#print axioms UPFP.ellOne_upfp_of_ellOne_equiv
#print axioms UPFP.theorem_1_6_empty_index_upfp
#print axioms UPFP.infinity_upfp_of_diagonal_reduction
#print axioms UPFP.lemma_3_4_infinity
#print axioms UPFP.lemma_3_4_cZero
#print axioms UPFP.lemma_4_6_infinity
#print axioms UPFP.lemma_4_6_cZero
#print axioms UPFP.proposition_4_7_infinity
#print axioms UPFP.proposition_4_7_cZero
#print axioms UPFP.proposition_3_5_infinity
#print axioms UPFP.proposition_3_5_cZero
#print axioms UPFP.proposition_5_3_infinity
#print axioms UPFP.proposition_5_3_cZero
#print axioms UPFP.theorem_1_2_finiteCotype_upfp
#check UPFP.theorem_1_2_finiteCotype_upfp
#print axioms UPFP.theorem_1_2_finiteCotype
#check UPFP.theorem_1_2_finiteCotype
#print axioms UPFP.theorem_1_1_ellOne_equiv
#print axioms UPFP.lemma_3_7_infinity
#print axioms UPFP.lemma_3_7_cZero
#print axioms UPFP.lemma_4_8_infinity
#print axioms UPFP.lemma_4_8_cZero
#check UPFP.theorem_1_1_ellOne_equiv
#check UPFP.lemma_3_7_infinity
#check UPFP.lemma_3_7_cZero
#check UPFP.lemma_4_8_infinity
#check UPFP.lemma_4_8_cZero
#print axioms UPFP.proposition_3_8_infinity
#print axioms UPFP.proposition_3_8_cZero
#print axioms UPFP.proposition_4_9_infinity
#print axioms UPFP.proposition_4_9_cZero
#check UPFP.proposition_3_8_infinity
#check UPFP.proposition_3_8_cZero
#check UPFP.proposition_4_9_infinity
#check UPFP.proposition_4_9_cZero
#print UPFP.InfinityDiagonalReduction
#print UPFP.infinity_upfp_of_diagonal_reduction

example : CompleteSpace (ThesisCommon.CZeroSum
    (ThesisCommon.IntervalLp ℂ ⟨1, le_rfl⟩)) := inferInstance
example : CompleteSpace (ThesisCommon.EllOneSum (ULift.{1} ℝ)
    (ThesisCommon.IntervalLp ℝ ⟨1, le_rfl⟩)) := inferInstance
#print axioms UPFP.proposition_5_4_infinity
#print axioms UPFP.proposition_5_4_cZero
#print axioms UPFP.theorem_1_2_finiteLpSelfSimilar
#print axioms UPFP.theorem_1_2_proof
#check UPFP.proposition_5_4_infinity
#check UPFP.proposition_5_4_cZero
#check UPFP.theorem_1_2_finiteLpSelfSimilar
#check UPFP.theorem_1_2_proof
#print axioms UPFP.lemma_3_2_lp
#check UPFP.lemma_3_2_lp
#print axioms UPFP.lemma_3_2_infinity
#check UPFP.lemma_3_2_infinity
#print axioms UPFP.lemma_3_2_cZero
#check UPFP.lemma_3_2_cZero
#print axioms UPFP.lemma_4_4_lp
#check UPFP.lemma_4_4_lp
#print axioms UPFP.lemma_4_4_infinity
#check UPFP.lemma_4_4_infinity
#print axioms UPFP.lemma_4_4_cZero
#check UPFP.lemma_4_4_cZero
#print axioms UPFP.proposition_3_3_lp
#check UPFP.proposition_3_3_lp
#print axioms UPFP.proposition_3_3_cZero
#check UPFP.proposition_3_3_cZero
#print axioms UPFP.proposition_4_5_lp
#check UPFP.proposition_4_5_lp
#print axioms UPFP.proposition_4_5_cZero
#check UPFP.proposition_4_5_cZero
#print axioms UPFP.proposition_5_2_lp
#print axioms UPFP.proposition_5_2_cZero
#print axioms UPFP.theorem_1_1_selfSimilar
#check UPFP.proposition_5_2_lp
#check UPFP.proposition_5_2_cZero
#check UPFP.theorem_1_1_selfSimilar
#print axioms UPFP.lemma_4_1
#print axioms UPFP.proposition_5_1
#print axioms UPFP.theorem_1_1_dualFiniteCotype
#print axioms UPFP.theorem_1_1_proof
#check UPFP.lemma_4_1
#check UPFP.proposition_5_1
#check UPFP.theorem_1_1_dualFiniteCotype
#check UPFP.theorem_1_1_proof
#print axioms UPFP.proposition_3_1
#print axioms UPFP.proposition_4_3
#check UPFP.proposition_3_1
#check UPFP.proposition_4_3

#print axioms ThesisCommon.intervalL1_hasCPFP_four
#print axioms ThesisCommon.realL1_ellOne_finite_interference
#print axioms ThesisCommon.complexL1_ellOne_finite_interference
#print axioms ThesisCommon.ellOne_finite_interference_near_diagonal
#print axioms ThesisCommon.ellOne_hasCPFP_of_finite_interference
#print axioms ThesisCommon.intervalL1ArbitraryEllOne_hasUPFP
#print axioms ThesisCommon.intervalContinuousDualLebesgueEquiv
#print axioms UPFP.corollary_1_3_L1
#print axioms UPFP.theorem_1_6_proof
#check UPFP.theorem_1_6_proof

#print axioms ThesisCommon.intervalL2HaarIsometry
#print axioms ThesisCommon.intervalL2_hasUPFP
#print axioms UPFP.corollary_1_3_L2
#check UPFP.corollary_1_3_L2

#print axioms UPFP.corollary_1_5_of_base
#print axioms UPFP.corollary_1_5_countable
#print axioms UPFP.corollary_1_5_exceptional_equiv
#print axioms UPFP.corollary_1_5_initial_below_countable_exponent_full
#print axioms UPFP.corollary_1_5_smallOrdinal
#check UPFP.corollary_1_5_smallOrdinal

#print axioms UPFP.corollary_1_5_proof
#check UPFP.corollary_1_5_proof

#print axioms UPFP.corollary_1_3_of_remaining_lp_base
#check UPFP.corollary_1_3_of_remaining_lp_base

-- Alspach--Enflo--Odell foundations and the actual finite-p base proof.
#print axioms ThesisCommon.haar_sign_second_moment
#print axioms ThesisCommon.haar_sign_variance_le
#print axioms ThesisCommon.haar_sign_simultaneous_small
#print axioms ThesisCommon.HasUPFP.of_mutual_retracts
#print axioms ThesisCommon.selfSimilar_kernel_retract
#print axioms ThesisCommon.intervalLpMeanZeroProjection_retract
#print axioms ThesisCommon.intervalLpMeanZero_contains_retract
#print axioms ThesisCommon.intervalLp_hasUPFP_of_meanZero
#print axioms ThesisCommon.NormalizedSchauderBasis.kernelTail
#print axioms ThesisCommon.NormalizedSchauderBasis.coord_norm_le_of_prefix_bound
#print axioms ThesisCommon.haar_functional_variation_le
#print axioms ThesisCommon.lpHaarDyadic_level_sum_norm_le
#print axioms ThesisCommon.lpHaarDyadic_functional_variance_le
#print axioms ThesisCommon.intervalLpMeanZeroHaarBasis
#print axioms ThesisCommon.intervalLpMeanZeroHaarBasis_coord_norm_le
#print axioms ThesisCommon.NormalizedSchauderBasis.summableMatrix_entry
#print axioms ThesisCommon.NormalizedSchauderBasis.subtract_offDiagonal_action
#print axioms ThesisCommon.lpHaarDyadic_signed_block_small
#print axioms ThesisCommon.hasCPFP_of_scalar_compressions
#print axioms ThesisCommon.haar_countable_trace_cluster
#print axioms ThesisCommon.lpHaarPartitionStep_norm_eq
#print axioms ThesisCommon.lpHaarSignedPart_equal_measure
#print axioms ThesisCommon.lpHaarSignedBlock_eq_vector
#print axioms ThesisCommon.lpHaarSignedBlock_norm
#print axioms ThesisCommon.lebesgueLpRestrict_norm_of_supported
#print axioms ThesisCommon.lpHaar_L1_backward_mass_tendsto_zero
#print axioms ThesisCommon.norm_lebesgueLpToOne_le
#print axioms ThesisCommon.lpHaar_backward_mass_tendsto_zero
#print axioms ThesisCommon.lpHaarSignedBlock_subset_small
#print axioms ThesisCommon.lpHaarSignedBlockReader_self
#print axioms ThesisCommon.lpHaarSignedBlockReader_multiplier
#print axioms ThesisCommon.lpHaarSignedBlockReader_uniform_small
#print axioms ThesisCommon.lpHaarSignedBlock_two_sided_small
#print axioms ThesisCommon.haar_trace_sign_balance
#print axioms ThesisCommon.lpHaarRefine_mass
#print axioms ThesisCommon.lpHaarParent_select_small
#print axioms ThesisCommon.lpHaar_operator_diagonal_norm_le
#print axioms ThesisCommon.lpHaarLevelTrace_cluster
#print axioms ThesisCommon.lpHaar_operator_diagonal_trace_limit
#print axioms ThesisCommon.lpHaarSignedChildAtoms_parent
#print axioms ThesisCommon.lpHaarDyadicTrace_sum_atoms
#print axioms ThesisCommon.NormalizedSchauderBasis.exists_operator_of_stable_basis
#print axioms ThesisCommon.NormalizedSchauderBasis.norm_diagonal_sub_scalar_le

#print axioms ThesisCommon.lpHaarPartitionTransfer_norm_le
#print axioms ThesisCommon.LpHaarPartitionTree.exists_embedding
#print axioms ThesisCommon.LpHaarPartitionTree.exists_faithful_retraction
#print axioms ThesisCommon.LpHaarPartitionTree.exists_faithful_meanZero_retraction
#print axioms ThesisCommon.LpHaarSequentialSplits.faithful
#print axioms ThesisCommon.exists_sequence_with_history
#print axioms ThesisCommon.lpHaar_infinite_two_sided_selection
#print axioms ThesisCommon.LpHaarPartitionTree.reading_coefficient
#print axioms ThesisCommon.LpHaarPartitionTree.embedding_haar
#print axioms ThesisCommon.lpHaar_diagonal_edge_norm_le
#print axioms ThesisCommon.lpHaarTrace_balanced_split
#print axioms ThesisCommon.lpHaar_trace_parent_select_normalized
#print axioms ThesisCommon.lpHaar_infinite_trace_selection
#print axioms ThesisCommon.lpHaar_geometric_edge_budget
#print axioms ThesisCommon.LpHaarSequentialSplits.compression_multiplier
#print axioms ThesisCommon.lpHaar_multiplier_scalar_compression
#print axioms ThesisCommon.lpHaar_infinite_normalized_selection
#print axioms ThesisCommon.LpHaarSequentialSplits.normalized_compression_coefficient
#print axioms ThesisCommon.NormalizedSchauderBasis.exists_diagonal_of_geometric_entries
#print axioms ThesisCommon.lpHaar_near_diagonal_compression
#print axioms ThesisCommon.intervalLp_scalar_compression_meanZero
#print axioms ThesisCommon.intervalLpMeanZero_scalar_compressions
#print axioms ThesisCommon.intervalLpMeanZero_hasCPFP_four
#print axioms ThesisCommon.intervalLpMeanZero_hasUPFP
#print axioms ThesisCommon.intervalLp_hasUPFP
#print axioms UPFP.corollary_1_3_proof
#check UPFP.corollary_1_3_proof
