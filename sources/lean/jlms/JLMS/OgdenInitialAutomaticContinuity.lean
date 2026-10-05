import JLMS.OgdenCommonProjections
import JLMS.MainStatements

/-!
# Ogden's automatic continuity theorem for regular uncountable initial ordinals

The proof uses Ogden's matrix and complemented-projection constructions
simultaneously for countably many operators. Their common factors imply
continuity on M₀ by the null-sequence criterion; the two bounded scalar
coordinates extend it to the full operator algebra. This avoids the
geometric approximate-identity construction while preserving the matrix
and continuity-ideal mechanism. Cohen factorization is proved separately.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalLimitOperatorGroup ordinalLimitOperatorSpace ordinalLimitOperatorAlgebra
  ordinalLimitOperatorScalarTower ordinalLimitOperatorScalarComm

theorem continuous_initialOrdinal_operator_hom
    {A : Type v} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A) : Continuous θ := by
  let f : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₗ[𝕜] A :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := θ.map_smul }
  apply continuous_of_continuous_on_loyWillisZeroEndpoint hc hu f
  apply continuous_restriction_of_common_ideal_factors θ (loyWillisZeroEndpointSubspace hc hu)
  intro x
  exact exists_ogden_common_ideal_factors hc hu θ (fun n => (x n).val)
    (fun n => (x n).property)

theorem theorem_1_3_initialOrdinal {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) : Theorem_1_3.{u, v, w} 𝕜 c.ord := by
  intro A _ _ _ _ _ θ
  exact continuous_initialOrdinal_operator_hom hc hu θ

end JLMS
