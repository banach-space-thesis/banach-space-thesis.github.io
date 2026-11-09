import PL1CD.EntropyScalar
import PL1CD.EntropyGap
import PL1CD.IntegralCauchySchwarz
import PL1CD.BoundedEntropy
import PL1CD.EntropyAverage
import PL1CD.LpEntropyGap
import PL1CD.FiniteEntropy
import PL1CD.CylinderRefinement
import PL1CD.PartitionEntropy
import PL1CD.LimsupSeminorm
import PL1CD.Variation
import PL1CD.RefinementEnergy
import PL1CD.CubeEntropy
import PL1CD.AnisotropicCubeEntropy
import PL1CD.HaarCubeEntropy
import PL1CD.CubeApproximation
import PL1CD.EntropyContinuity
import PL1CD.HaarEntropyContraction
import PL1CD.EntropyUpper
import PL1CD.PositiveHaarOperators
import PL1CD.PositiveKernelAverages
import PL1CD.RealL1Order
import PL1CD.HaarPartitions
import PL1CD.HaarPartitionAlgebra
import PL1CD.RealL1FiniteOrder
import PL1CD.AbsoluteRefinement
import PL1CD.HaarPartitionExpansion
import PL1CD.StrongOperatorLimits
import PL1CD.AbsoluteOperatorLimit
import PL1CD.EntropyEnergy
import PL1CD.EntropyGrowth
import PL1CD.AlmostDisjoint
import PL1CD.Statements
import PL1CD.ProjectionFamily
import PL1CD.GeneratedIdeals
import PL1CD.DunfordPettisIdeals
import PL1CD.StageParameters
import PL1CD.StageFiltration
import PL1CD.StageAsymptotics
import PL1CD.StageBlockEvents
import PL1CD.BlockConcentration
import PL1CD.StageBlocks
import PL1CD.BoundedPositiveVanishing
import PL1CD.PositiveTruncation
import PL1CD.PositiveVanishing
import PL1CD.AbsoluteMajorant
import PL1CD.Cardinality
import PL1CD.PartitionNorms
import PL1CD.SumSeries
import PL1CD.SemigroupVanishing
import PL1CD.RealOperatorVanishing
import PL1CD.ScalarOperatorVanishing
import PL1CD.RealInputVariation
import PL1CD.CoordinateVanishing
import PL1CD.FiniteExpectations
import PL1CD.DensitySeparation
import PL1CD.HaarTransport
import PL1CD.IdealSeparation
import PL1CD.VariationComposition
import PL1CD.IntrinsicZeroVanishing
import PL1CD.IntrinsicVanishing
import PL1CD.RangeVanishing
import PL1CD.StageGrowth
import PL1CD.MaximalVariation
import PL1CD.StageSeparation
import PL1CD.StageCarrier
import PL1CD.StageRangeGeometry
import PL1CD.ProofEndpoints
import PL1CD.MainTheorems

#print PL1CD.StageAnalyticSeparation

#check PL1CD.AlmostDisjoint.family_diff_biUnion_infinite
#print axioms PL1CD.AlmostDisjoint.family_diff_biUnion_infinite

#check PL1CD.generatedIdeal_isClosedTwoSided
#print axioms PL1CD.generatedIdeal_isClosedTwoSided

#check PL1CD.generatedIdeal_empty
#print axioms PL1CD.generatedIdeal_empty

#check PL1CD.closedOperatorIdeals_cardinality_le
#print axioms PL1CD.closedOperatorIdeals_cardinality_le

#check PL1CD.stageProjectionFamily_norm_le
#print axioms PL1CD.stageProjectionFamily_norm_le

#check PL1CD.stageProjectionFamily_range_schur
#print axioms PL1CD.stageProjectionFamily_range_schur

#check PL1CD.stageProjectionFamily_idealAdditionalSpec
#print axioms PL1CD.stageProjectionFamily_idealAdditionalSpec

#check PL1CD.StageParameters.dimension_ratio_times_exp_high_tendsto
#print axioms PL1CD.StageParameters.dimension_ratio_times_exp_high_tendsto

#check PL1CD.StageParameters.exists_common_null_carrier
#print axioms PL1CD.StageParameters.exists_common_null_carrier

#check PL1CD.stageProjectionFamily_additionalStrongSpec
#print axioms PL1CD.stageProjectionFamily_additionalStrongSpec

#check PL1CD.averagedVariation_unitResolvent_eq_two
#print axioms PL1CD.averagedVariation_unitResolvent_eq_two

#check PL1CD.Entropy.bounded_average_entropy_gap
#print axioms PL1CD.Entropy.bounded_average_entropy_gap

#check PL1CD.Entropy.cubeEntropy_varyingNoise_le
#print axioms PL1CD.Entropy.cubeEntropy_varyingNoise_le

#check PL1CD.Entropy.Phi_tendsto_of_bounded_L1
#print axioms PL1CD.Entropy.Phi_tendsto_of_bounded_L1

#check PL1CD.Entropy.Ent_noise_le
#print axioms PL1CD.Entropy.Ent_noise_le

#check PL1CD.Entropy.Ent_eq_relativeEntropy
#print axioms PL1CD.Entropy.Ent_eq_relativeEntropy

#check PL1CD.Entropy.Phi_noise_le
#print axioms PL1CD.Entropy.Phi_noise_le

#check PL1CD.CylinderRefinement.mean_operator_descendants
#print axioms PL1CD.CylinderRefinement.mean_operator_descendants

#check PL1CD.Entropy.bounded_lp_average_entropy_gap
#print axioms PL1CD.Entropy.bounded_lp_average_entropy_gap

#check PL1CD.CylinderRefinement.descendant_entropy_gap
#print axioms PL1CD.CylinderRefinement.descendant_entropy_gap

#check PL1CD.CylinderRefinement.refinementVariation_eq_finiteVariation
#print axioms PL1CD.CylinderRefinement.refinementVariation_eq_finiteVariation

#check PL1CD.CylinderRefinement.level_energy_le
#print axioms PL1CD.CylinderRefinement.level_energy_le

#check PL1CD.Variation.averagedVariation_eq_zero_of_entropy
#print axioms PL1CD.Variation.averagedVariation_eq_zero_of_entropy

#check PL1CD.Variation.resolvent_vanishing_of_noise_vanishing
#print axioms PL1CD.Variation.resolvent_vanishing_of_noise_vanishing

#check PL1CD.theoremsCDStrong_of_stageAnalyticSeparation
#print axioms PL1CD.theoremsCDStrong_of_stageAnalyticSeparation

#check PL1CD.theoremCReal_of_stageAnalyticSeparation
#print axioms PL1CD.theoremCReal_of_stageAnalyticSeparation

#check PL1CD.theoremCComplex_of_stageAnalyticSeparation
#print axioms PL1CD.theoremCComplex_of_stageAnalyticSeparation

#check PL1CD.theoremDReal_of_stageAnalyticSeparation
#print axioms PL1CD.theoremDReal_of_stageAnalyticSeparation

#check PL1CD.theoremDComplex_of_stageAnalyticSeparation
#print axioms PL1CD.theoremDComplex_of_stageAnalyticSeparation

#check PL1CD.PositiveHaarOperators.positive_noise_vanishing
#print axioms PL1CD.PositiveHaarOperators.positive_noise_vanishing

#check PL1CD.exists_strongLimit_of_dense
#print axioms PL1CD.exists_strongLimit_of_dense

#check PL1CD.L1Order.exists_L1_limit_of_monotone
#print axioms PL1CD.L1Order.exists_L1_limit_of_monotone

#check PL1CD.HaarPartitions.exists_positive_decomposition
#print axioms PL1CD.HaarPartitions.exists_positive_decomposition

#check PL1CD.Variation.scalar_noise_vanishing
#print axioms PL1CD.Variation.scalar_noise_vanishing

#check PL1CD.Variation.scalar_resolvent_vanishing
#print axioms PL1CD.Variation.scalar_resolvent_vanishing

#check PL1CD.PartitionNorms.exists_coordinate_majorant
#print axioms PL1CD.PartitionNorms.exists_coordinate_majorant

#check PL1CD.Variation.sum_averagedVariation_eq_zero_of_coordinates
#print axioms PL1CD.Variation.sum_averagedVariation_eq_zero_of_coordinates

#check PL1CD.Variation.intrinsic_evalZero_vanishing
#print axioms PL1CD.Variation.intrinsic_evalZero_vanishing

#check PL1CD.Variation.intrinsic_vanishing
#print axioms PL1CD.Variation.intrinsic_vanishing

#check PL1CD.Variation.interval_range_vanishing
#print axioms PL1CD.Variation.interval_range_vanishing

#check PL1CD.stage_growthCriterion
#print axioms PL1CD.stage_growthCriterion

#check PL1CD.stageAnalyticSeparation
#print axioms PL1CD.stageAnalyticSeparation

#check PL1CD.theoremC
#print axioms PL1CD.theoremC

#check PL1CD.theoremD
#print axioms PL1CD.theoremD

#check PL1CD.theoremsCDStrong
#print axioms PL1CD.theoremsCDStrong

#check PL1CD.theoremCReal
#print axioms PL1CD.theoremCReal

#check PL1CD.theoremCComplex
#print axioms PL1CD.theoremCComplex

#check PL1CD.theoremDReal
#print axioms PL1CD.theoremDReal

#check PL1CD.theoremDComplex
#print axioms PL1CD.theoremDComplex

#check PL1CD.theoremsCDRealStrong
#print axioms PL1CD.theoremsCDRealStrong

#check PL1CD.theoremsCDComplexStrong
#print axioms PL1CD.theoremsCDComplexStrong

