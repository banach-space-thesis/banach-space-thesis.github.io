import PL1.MainTheoremA
import PL1.MainTheoremB
import PL1.EnfloNoL1
import PL1.EnfloSmoothing
import PL1.EnfloCopyExclusion
import PL1.ALAlternative
import PL1.FiniteGrothendieck

/-!
# Exact reviewed endpoints and axiom audit for the third pass

The examples require the original reviewed real and strong complex targets,
without any structural input. The construction uses the original projection
and inherited norm. The arbitrary-L1-copy obstruction is proved directly for
the noise construction; a general Enflo–Starbird extraction theorem is not
asserted. The lattice consequence uses the proved direct AL alternative.
-/

set_option pp.universes true

example : PL1.TheoremARealStatement := PL1.theoremAReal
example : PL1.TheoremAComplexStrongStatement := PL1.theoremAComplexStrong
example : PL1.TheoremBRealStatement := PL1.theoremBReal
example : PL1.TheoremBComplexStrongStatement := PL1.theoremBComplexStrong

example : PL1.MainTheoremsStatement :=
  ⟨PL1.theoremAReal, PL1.theoremAComplexStrong, PL1.theoremBReal, PL1.theoremBComplexStrong⟩

#print PL1.TheoremBSpec
#print PL1.TheoremBStatement
#print PL1.TheoremBRealStatement
#print PL1.TheoremBComplexStrongStatement
#check @PL1.theoremB
#print axioms PL1.theoremAReal
#print axioms PL1.theoremAComplexStrong
#print axioms PL1.theoremB
#print axioms PL1.theoremBReal
#print axioms PL1.theoremBComplexStrong

#check @PL1.FiniteSumming.matrixGrothendieckWith_128
#print axioms PL1.FiniteSumming.matrixGrothendieckWith_128
#print axioms PL1.FiniteSumming.oneSumming_128
#print axioms PL1.FiniteSumming.twoSumming_128
#print axioms PL1.DyadicL1Coordinates.analysis_synthesis
#print axioms PL1.DyadicL1Coordinates.norm_synthesis
#check @PL1.IntervalSumming.oneSumming_interval
#check @PL1.IntervalSumming.twoSumming_interval
#print axioms PL1.IntervalSumming.oneSumming_interval
#print axioms PL1.IntervalSumming.twoSumming_interval

#check @PL1.PositiveLowerOneBridge.positiveLowerOne_of_disjoint
#check @PL1.PositiveLowerOneBridge.positiveLowerOne_of_complemented_ambient
#print axioms PL1.PositiveLowerOneBridge.positiveLowerOne_of_disjoint
#print axioms PL1.PositiveLowerOneBridge.positiveLowerOne_of_complemented_ambient
#print axioms PL1.ALRenorming.seminorm_bounds
#print axioms PL1.ALRenorming.isALNorm
#print axioms PL1.ALAtomic.coordinateIsometry
#print axioms PL1.ALAtomic.hasSchurProperty
#print axioms PL1.ALDyadicEmbedding.containsIsomorphicCopy_of_not_atomic
#check @PL1.ALAlternative.schur_or_contains_interval_of_complemented
#print axioms PL1.ALAlternative.schur_or_contains_interval_of_complemented

#print axioms PL1.EnfloBush.dyadic_max_integral_mul_norm
#print axioms PL1.EnfloBush.exists_dyadic_majorant
#check @PL1.EnfloBush.noise_comp_dyadicVanishing
#print axioms PL1.EnfloBush.noise_comp_dyadicVanishing
#print axioms PL1.DyadicCoordinateDomination.exists_summable_majorant
#print axioms PL1.EnfloBush.maxMass_flatten
#print axioms PL1.EnfloBush.not_boundedBelow_sum_of_coordinates
#print axioms PL1.EnfloBush.dyadicVanishing_resolvent_of_noise
#print axioms PL1.EnfloBush.dyadicVanishing_intrinsic_evalZero
#print axioms PL1.EnfloBush.dyadicVanishing_intrinsic_flatten
#print axioms PL1.EnfloBush.not_boundedBelow_two_maps
#print axioms PL1.IntrinsicRealParts.norm_le_parts
#print axioms PL1.EnfloBush.scalarIntrinsic_no_real_L1_of_operators
#check @PL1.Noise.constant_intervalProjection_range_no_real_L1
#check @PL1.Noise.constant_intervalProjection_range_no_underlying_real_L1
#print axioms PL1.Noise.constant_intervalProjection_range_no_real_L1
#print axioms PL1.Noise.constant_intervalProjection_range_no_underlying_real_L1
