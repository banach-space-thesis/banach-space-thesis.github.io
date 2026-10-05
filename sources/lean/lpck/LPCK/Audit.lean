import LPCK
#print axioms LPCK.lemma_3_1_lp
#print axioms LPCK.corollary_3_2_lp
#print axioms LPCK.lemma_3_3_lp
#print axioms LPCK.proposition_3_5_lp
#print axioms LPCK.lemma_3_8
#check LPCK.lemma_3_1_lp
#check LPCK.corollary_3_2_lp
#check LPCK.lemma_3_3_lp
#check LPCK.proposition_3_5_lp
#check LPCK.lemma_3_8
#print axioms LPCK.lemma_3_10
#print axioms LPCK.lemma_2_14
#print axioms LPCK.remark_2_16_extension_norm
#print axioms LPCK.remark_2_16_extension_identity
#print axioms LPCK.lemma_3_11_unitInterval
#check LPCK.lemma_3_10
#check LPCK.lemma_2_14
#check LPCK.remark_2_16_extension_norm
#check LPCK.remark_2_16_extension_identity
#check LPCK.lemma_3_11_unitInterval
#print axioms LPCK.proposition_3_13_unitInterval
#print axioms LPCK.proposition_3_15_unitInterval
#print axioms LPCK.lemma_4_1_unitInterval
#check LPCK.proposition_3_13_unitInterval
#check LPCK.proposition_3_15_unitInterval
#check LPCK.lemma_4_1_unitInterval
#print axioms LPCK.lemma_4_3_unitInterval
#print axioms LPCK.lemma_4_4_unitInterval
#print axioms LPCK.proposition_4_6_unitInterval
#print axioms LPCK.theorem_1_2_of_base_results
#check LPCK.lemma_4_3_unitInterval
#check LPCK.lemma_4_4_unitInterval
#check LPCK.proposition_4_6_unitInterval
#check LPCK.theorem_1_2_of_base_results
#check LPCK.theorem_1_2_of_base_upfp
#print axioms LPCK.theorem_1_2_of_base_upfp

/-! A target's axiom report checks its definition, NOT its truth. -/
#print LPCK.Theorem_1_1
#print LPCK.Theorem_1_2
#print LPCK.Corollary_1_3
#print ThesisCommon.IsPrimary
#print ThesisCommon.HasUPFP
#print ThesisCommon.HasCPFP
#print ThesisCommon.FactorsIdentityWith
#print axioms LPCK.Theorem_1_1
#print axioms LPCK.Theorem_1_2
#print axioms LPCK.Corollary_1_3
#print axioms LPCK.lemma_2_3_infinity
#print axioms LPCK.lemma_2_3
#print axioms LPCK.lemma_2_4
#print axioms LPCK.corollary_2_5_infinity
#print axioms LPCK.corollary_2_5
#print axioms LPCK.theorem_1_2_proof
#print axioms LPCK.corollary_1_3_finite
#print axioms LPCK.corollary_1_3_uncountable
#print axioms LPCK.ordinalContinuousDualEllOneEquiv
#print axioms LPCK.countableCanonicalOrdinalCZeroEquiv
#print axioms LPCK.countableCanonicalOrdinal_sequence_hasUPFP
#print axioms LPCK.countableOrdinal_sequence_hasUPFP
#print axioms LPCK.theorem_1_1_countable
#print axioms LPCK.ordinal_lt_aleph_one_of_countable_interval
#print axioms LPCK.corollary_1_3_proof
#check LPCK.corollary_1_3_proof
#check LPCK.theorem_1_1_countable

example : CompleteSpace (ThesisCommon.SequenceSum ⟨⊤, le_top⟩
    (ThesisCommon.OrdinalContinuous ℂ (0 : Ordinal))) := inferInstance
example : CompleteSpace (ThesisCommon.SequenceSum ⟨1, le_rfl⟩
    (ThesisCommon.IntervalContinuous ℝ)) := inferInstance

#print axioms ThesisCommon.rademacher_second_le_three_first_sq
#print axioms ThesisCommon.scalar_ellOne_hasRademacherCotype_two
#print axioms ThesisCommon.HasRademacherCotype.two_of_equiv
#print axioms LPCK.ordinalContinuousDual_hasFiniteCotype
#print axioms LPCK.canonicalOrdinal_sequence_of_base
#print axioms LPCK.exists_ordinal_sequence_canonical_power
#print axioms LPCK.theorem_1_1_of_canonical_bases
#print axioms LPCK.initialPowerCZeroEquiv
#print axioms LPCK.theorem_1_1_initial_higher_countable_cofinal
#print axioms LPCK.theorem_1_1_initial_below_countable_exponent
#print axioms LPCK.theorem_1_1_regular_initial_finite_multiple
#print axioms LPCK.GenericOrdinal.initialOrdinal_hasCPFP_sixteen
#print axioms LPCK.omegaPower_base_hasUPFP_small
#print axioms LPCK.theorem_1_1_smallOrdinal
#check LPCK.theorem_1_1_smallOrdinal
#check LPCK.GenericOrdinal.initialOrdinal_hasCPFP_sixteen
#print axioms LPCK.GenericOrdinal.principalRank_hasUPFP
#print axioms LPCK.GenericOrdinal.exists_ordinalSpace_canonical_power_normalForm
#check LPCK.GenericOrdinal.principalRank_hasUPFP

#print axioms LPCK.GenericOrdinal.fullRepeatedRegularOrdinal_hasCPFP_sixteen
#print axioms LPCK.GenericOrdinal.regularInitialSquare_hasUPFP
#print axioms LPCK.GenericOrdinal.jlmsScalarCZero_infinite_hasUPFP
#print axioms LPCK.GenericOrdinal.initialOrdinalInfiniteQuotient_hasUPFP_of_scalar
#print axioms LPCK.GenericOrdinal.singularInitialBelowSquare_hasUPFP
#print axioms LPCK.omegaPower_base_hasUPFP_allUniverses
#print axioms LPCK.theorem_1_1_proof
#check LPCK.theorem_1_1_proof
