import PL1.DaugavetIntrinsicFramework
import PL1.IntrinsicSpikeFamilies
import PL1.ConstantTailSpikes

/-!
# The Daugavet property of both actual intrinsic spaces

The equalities use the original graph ell1 norm of the intrinsic spaces.
They discharge the geometric slice criterion from the actual finite tail
families, without extra concentration, multiplication or averaging premises.
-/

noncomputable section
open scoped NNReal

namespace PL1.Noise

variable (K : Type*) [RCLike K]

theorem schur_intrinsic_sliceCriterion :
    Daugavet.SliceCriterion K (dyadicSystem K schurRates).IntrinsicSpace :=
  intrinsic_sliceCriterion_of_finiteSpikeFamilies K schurRates
    (IntrinsicSpikeFamilies.finiteSpikeFamilies schurRates
      (fun d T _ hδ => TailSpikes.exists_family d T hδ))

theorem constant_intrinsic_sliceCriterion :
    Daugavet.SliceCriterion K (dyadicSystem K constantRates).IntrinsicSpace :=
  intrinsic_sliceCriterion_of_finiteSpikeFamilies K constantRates
    (IntrinsicSpikeFamilies.finiteSpikeFamilies constantRates
      (fun d T _ hδ => TailSpikes.exists_constant_family d T hδ))

theorem schur_intrinsic_hasDaugavetProperty :
    Daugavet.HasDaugavetProperty K (dyadicSystem K schurRates).IntrinsicSpace := by
  let := intrinsicSpace_nontrivial K schurRates
  exact (schur_intrinsic_sliceCriterion K).hasDaugavetProperty

theorem constant_intrinsic_hasDaugavetProperty :
    Daugavet.HasDaugavetProperty K (dyadicSystem K constantRates).IntrinsicSpace := by
  let := intrinsicSpace_nontrivial K constantRates
  exact (constant_intrinsic_sliceCriterion K).hasDaugavetProperty

end PL1.Noise
