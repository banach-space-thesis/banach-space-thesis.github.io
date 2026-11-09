import PL1.PartialMainTheorems
import PL1.Ell1RNP

/-! # Neither actual interval projection range is isomorphic to scalar ell1

These consequences of full RNP failure do not assert absence of an interval
L1 subspace and do not complete the nonlattice obstruction.
-/

noncomputable section
namespace PL1.Noise

theorem schur_intervalProjection_range_not_isomorphic_ell1 (𝕜 : Type*) [RCLike 𝕜] :
    IsEmpty ((intervalProjection 𝕜 schurRates).range ≃L[𝕜] Ell1 𝕜) :=
  Ell1RNP.not_isomorphic_of_not_RNP 𝕜 (schur_intervalProjection_range_not_RNP 𝕜)

theorem constant_intervalProjection_range_not_isomorphic_ell1 (𝕜 : Type*) [RCLike 𝕜] :
    IsEmpty ((intervalProjection 𝕜 constantRates).range ≃L[𝕜] Ell1 𝕜) :=
  Ell1RNP.not_isomorphic_of_not_RNP 𝕜 (constant_intervalProjection_range_not_RNP 𝕜)

end PL1.Noise
