import PL1.MainTheoremA
import PL1.MainDaugavet
import PL1.DaugavetRealification
import PL1.IntrinsicExposedPoint
import PL1.IntrinsicTailNorm
import PL1.ExplicitMartingaleFiltration
import PL1.ExplicitMartingaleWeak
import PL1.ConstantNoiseTrace
import PL1.ComplementedLatticeRealAmbient
import PL1.NoiseGeneratorCore
import PL1.GeneratorGraphBanach
import PL1.ExtendedDiscreteInterpolation
import PL1.MainInterpolation
import PL1.InterpolationBochner
import PL1.InterpolationNorm
import PL1.DaugavetDiameter
import PL1.SummingTransport

/-!
# Exact type and axiom audit for the second three-hour pass

The original A targets below are proved without added hypotheses. The full B
endpoint remains conditional on three explicitly printed real structural
premises. All geometry uses the original intrinsic norm. These ordinary Lean
checks and axiom reports complement the independent semantic audits.
-/

set_option pp.universes true

example : PL1.TheoremARealStatement := PL1.theoremAReal
example : PL1.TheoremAComplexStrongStatement := PL1.theoremAComplexStrong

#check @PL1.theoremA
#print PL1.TheoremAStatement
#print PL1.TheoremAComplexStrongStatement
#print axioms PL1.separableSchurLatticeRNP
#print axioms PL1.theoremA
#print axioms PL1.theoremAReal
#print axioms PL1.theoremAComplexStrong

#print PL1.ComplementedLattice.ComplementedL1LatticeClassification
#print PL1.ComplementedLattice.SeparableRealL1Dichotomy
#print PL1.ComplementedLattice.L1CopyExtraction
#check @PL1.ComplementedLattice.theoremB_real_and_complex_of_real_structural_properties
#print axioms PL1.ComplementedLattice.theoremB_real_and_complex_of_real_structural_properties
#print axioms PL1.ComplementedLattice.scalarIntervalRealCopy

#check @PL1.NoiseHypercontractivity.positiveTimeNoiseL2
#check @PL1.NoiseHypercontractivity.positiveTimeNoiseL2_overlap
#print axioms PL1.NoiseHypercontractivity.norm_positiveTimeNoiseL2_le_one
#print axioms PL1.NoiseHypercontractivity.positiveTimeNoiseL2_overlap
#print axioms PL1.NoiseHypercontractivity.exponent_lt_two
#check @PL1.Noise.constant_intervalProjection_hasVanishingDyadicTrace
#print axioms PL1.Noise.constant_resolvent_hasVanishingDyadicTrace
#print axioms PL1.Noise.constant_projection_hasVanishingDyadicTrace
#print axioms PL1.Noise.constant_intervalProjection_hasVanishingDyadicTrace
#print axioms PL1.Noise.constant_intervalProjection_identity_distance
#print axioms PL1.Noise.constant_intervalProjection_not_factors_identity

#print PL1.Daugavet.HasDaugavetProperty
#check PL1.Noise.schur_intrinsic_hasDaugavetProperty ℝ
#check PL1.Noise.schur_intrinsic_hasDaugavetProperty ℂ
#check PL1.Noise.constant_intrinsic_hasDaugavetProperty ℝ
#check PL1.Noise.constant_intrinsic_hasDaugavetProperty ℂ
#check PL1.Noise.schur_intrinsic_underlyingReal_hasDaugavetProperty ℂ
#check PL1.Noise.constant_intrinsic_underlyingReal_hasDaugavetProperty ℂ
#print axioms PL1.Noise.schur_intrinsic_hasDaugavetProperty
#print axioms PL1.Noise.constant_intrinsic_hasDaugavetProperty
#print axioms PL1.Noise.schur_intrinsic_underlyingReal_hasDaugavetProperty
#print axioms PL1.Noise.constant_intrinsic_underlyingReal_hasDaugavetProperty

#check @PL1.IntrinsicTailNorm.schur_norm_id_sub_intrinsicExpectation_eq_two
#check @PL1.IntrinsicTailNorm.constant_norm_id_sub_intrinsicExpectation_eq_two
#print axioms PL1.IntrinsicTailNorm.schur_norm_id_sub_intrinsicExpectation_eq_two
#print axioms PL1.IntrinsicTailNorm.constant_norm_id_sub_intrinsicExpectation_eq_two
#check @PL1.IntrinsicExposedPoint.integralFunctional_maximum_iff
#check @PL1.IntrinsicExposedPoint.integralFunctional_strict_maximum
#print axioms PL1.IntrinsicExposedPoint.norm_integralFunctional
#print axioms PL1.IntrinsicExposedPoint.schur_integralFunctional_exposes_constant
#print axioms PL1.IntrinsicExposedPoint.constant_integralFunctional_exposes_constant

#check PL1.ExplicitMartingale.schur_explicit_martingale ℝ
#check PL1.ExplicitMartingale.schur_explicit_martingale ℂ
#check PL1.ExplicitMartingale.constant_explicit_martingale ℝ
#check PL1.ExplicitMartingale.constant_explicit_martingale ℂ
#check @PL1.ExplicitMartingale.schur_beta_exists_dual_oscillation
#check @PL1.ExplicitMartingale.schur_beta_not_weaklyCauchy_real
#print axioms PL1.ExplicitMartingale.schur_explicit_martingale
#print axioms PL1.ExplicitMartingale.constant_explicit_martingale
#print axioms PL1.ExplicitMartingale.schur_beta_exists_dual_oscillation
#print axioms PL1.ExplicitMartingale.schur_beta_not_weaklyCauchy_real

#print PL1.Noise.IsGeneratorPair
#check @PL1.Noise.isGeneratorPair_iff_mem_graph
#check @PL1.Noise.IsGeneratorPair.polynomial_core
#check @PL1.GeneratorGraphBanach.norm_eq
#check @PL1.GeneratorGraphBanach.kFunctional_eq
#print axioms PL1.Noise.isGeneratorPair_iff_mem_graph
#print axioms PL1.Noise.dense_generator_domain
#print axioms PL1.Noise.isClosed_generator_graph
#print axioms PL1.Noise.IsGeneratorPair.polynomial_core
#print axioms PL1.GeneratorGraphBanach.norm_eq
#print axioms PL1.GeneratorGraphBanach.kFunctional_eq
#print axioms PL1.KFunctional.half_norm_defect_le
#print axioms PL1.KFunctional.value_le_defect
#print axioms PL1.DiscreteInterpolation.mem_range_evalZero_iff
#print axioms PL1.DiscreteInterpolation.half_norm_le
#print axioms PL1.DiscreteInterpolation.normValue_le
#print axioms PL1.DiscreteInterpolation.extendedNorm_ne_top_iff

#print PL1.Interpolation.normIntegral
#check @PL1.Interpolation.intrinsic_eq_realInterpolation
#check PL1.Interpolation.intrinsic_eq_realInterpolation ℝ PL1.Noise.schurRates
#check PL1.Interpolation.intrinsic_eq_realInterpolation ℂ PL1.Noise.schurRates
#check PL1.Interpolation.intrinsic_eq_realInterpolation ℝ PL1.Noise.constantRates
#check PL1.Interpolation.intrinsic_eq_realInterpolation ℂ PL1.Noise.constantRates
#print axioms PL1.KFunctional.continuousNorm_le_four_extendedNorm
#print axioms PL1.KFunctional.extendedNorm_le_five_continuousNorm
#print axioms PL1.Interpolation.mem_intrinsic_iff
#print axioms PL1.Interpolation.normValue_lower
#print axioms PL1.Interpolation.normValue_upper
#print axioms PL1.Interpolation.intrinsic_eq_realInterpolation

#check @PL1.Interpolation.mem_intrinsic_iff_integrable
#check @PL1.Interpolation.normValue_eq_integral
#check @PL1.InterpolationNorm.continuousLinearEquiv
#check @PL1.InterpolationNorm.norm_eq_integral
#print axioms PL1.Interpolation.mem_intrinsic_iff_integrable
#print axioms PL1.Interpolation.normValue_eq_integral
#print axioms PL1.KFunctional.continuousNorm_add_le
#print axioms PL1.KFunctional.continuousNorm_smul
#print axioms PL1.KFunctional.continuousNorm_eq_zero_iff
#print axioms PL1.InterpolationNorm.continuousLinearEquiv
#print axioms PL1.InterpolationNorm.norm_eq_integral
#print axioms PL1.InterpolationNorm.inclusion_injective

example : CompleteSpace (PL1.InterpolationNorm.Space ℝ PL1.Noise.schurRates) := inferInstance
example : CompleteSpace (PL1.InterpolationNorm.Space ℂ PL1.Noise.constantRates) := inferInstance

-- Importing the dedicated interpolation norm leaves the original norm intact.
example (K : Type*) [RCLike K] (rates : ℕ → NNReal)
    (x : (PL1.Noise.dyadicSystem K rates).IntrinsicSpace) :
    ‖x‖ = ∑' n, ‖PL1.IntrinsicGraph.coord (PL1.Noise.dyadicSystem K rates).analysis n x‖ :=
  PL1.IntrinsicGraph.norm_eq_tsum _ x

#check @PL1.Daugavet.SliceCriterion.diam_realPartSlice
#check @PL1.Daugavet.SliceCriterion.not_strongly_exposes
#check @PL1.Noise.schur_intrinsic_integral_maximizing_sequence_far
#check @PL1.Noise.constant_intrinsic_integral_maximizing_sequence_far
#print axioms PL1.Daugavet.SliceCriterion.diam_realPartSlice
#print axioms PL1.Daugavet.SliceCriterion.not_strongly_exposes
#print axioms PL1.Noise.schur_intrinsic_underlyingReal_diam_realPartSlice
#print axioms PL1.Noise.constant_intrinsic_underlyingReal_diam_realPartSlice
#print axioms PL1.Noise.schur_intrinsic_integral_maximizing_sequence_far
#print axioms PL1.Noise.constant_intrinsic_integral_maximizing_sequence_far

-- The ambient summing bounds and principal projections remain explicit inputs.
#check @PL1.ComplementedLattice.OneSummingWith.precomp
#check @PL1.ComplementedLattice.OneSummingWith.postcomp
#check @PL1.ComplementedLattice.TwoSummingWith.precomp
#check @PL1.ComplementedLattice.TwoSummingWith.postcomp
#check @PL1.ComplementedLattice.uniform_finite_summing_estimates
#check @PL1.ComplementedLattice.disjoint_sum_norm_le_of_complemented_ambient_estimates
#print axioms PL1.ComplementedLattice.OneSummingWith.precomp
#print axioms PL1.ComplementedLattice.OneSummingWith.postcomp
#print axioms PL1.ComplementedLattice.TwoSummingWith.precomp
#print axioms PL1.ComplementedLattice.TwoSummingWith.postcomp
#print axioms PL1.ComplementedLattice.uniform_finite_summing_estimates
#print axioms PL1.ComplementedLattice.disjoint_sum_norm_le_of_complemented_ambient_estimates
